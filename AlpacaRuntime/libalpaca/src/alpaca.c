#include <stdarg.h>
#include <string.h>
#include <libio/log.h>
#include <msp430.h>

#include "alpaca.h"

#define CHKPT_ACTIVE 0
#define CHKPT_STATUS_MAX 0x8000
#define CHKPT_USELESS 1
#define CHKPT_INACTIVE 2
#define CHKPT_NEEDED 3

#define CHKPT_IMMORTAL 0x7F // positive largest

#define RECOVERY_MODE 0 // tmp
#define NORMAL_MODE 0xFFFF

#define MAX_TRACK 3000 // temp
#define PACK_BYTE 8

#define BITSET(port, val) port |= val
#define BITCLR(port, val) port &= ~(val)

// This are fixed magic number
// It should change according to the clock speed
#define MIN_STEPSIZE 10
#define GUARD 0

#define ALWAYS_CHECKPOINT 0

#define UNDO_LOG 0
#define CHECKPOINT 1
#define RESTORE 2
#define END_RUN 3
#define OVERHEAD 999
__nv unsigned debug_cntr = 0;

__nv uint16_t new_stepsize;
__nv uint16_t step = 0xFF; //arbitrary
__nv uint16_t chkpt_cntr = 0;
__nv uint16_t stuck_cntr = 0;
uint16_t timer_overflow = 0;
__nv uint16_t timer_interval = 0xFFFF;
__nv uint16_t optimistic_interval = 0xFFFF;
__nv uint16_t timer_overflow_bnd = 256;
__nv uint16_t optimistic_bnd = 256;
__nv uint8_t needSlightImprovement = 1;
__nv uint8_t needRadicalImprovement = 1;
__nv uint8_t mayNeedSlightImprovement = 0;
__nv uint8_t optimistic_reached = 0;
__nv uint16_t mayNeedDegradation = 0;

__nv uint8_t* backup[MAX_TRACK];
// TODO: This can be uint8_t
//__nv unsigned backup_size[MAX_TRACK];
//__nv unsigned backup_bitmask[BITMASK_SIZE]={0};
__nv uint8_t bitmask_counter = 1;
__nv uint8_t need_bitmask_clear = 0;

__nv uint8_t* start_addr;
__nv uint8_t* end_addr;
__nv unsigned offset;
uint8_t program_end = 0;
__nv volatile isSafeKill = 1;

__nv volatile unsigned regs_0[16];
__nv volatile unsigned regs_1[16];

// temp size
__nv unsigned special_stack[SPECIAL_STACK_SIZE];
uint8_t* special_sp = ((uint8_t*)(&special_stack[0])) - 2;
__nv uint8_t* stack_tracer = ((uint8_t*)(&special_stack[0])) - 2;

__nv context_t context_0 = {
	.cur_reg = NULL,
	.backup_index = 0,
	.stack_tracer = ((uint8_t*)(&special_stack[0])) - 2,
};
__nv context_t context_1 = {
	.stack_tracer = ((uint8_t*)(&special_stack[0])) - 2,
};
__nv context_t * volatile curctx = &context_0;

__nv uint8_t isNoProgress = 0;
__nv uint16_t mode_status = NORMAL_MODE;
__nv uint8_t chkpt_ever_taken = 0;


/**
 * @brief Function to be called once to set the global range
 * ideally, it is enough to be called only once, however, currently it is called at the beginning of task_0
 * it can be optimized. (i.e., it needs not be set at runtime)
 */
// TODO: This can be removed
void set_global_range(uint8_t* _start_addr, uint8_t* _end_addr, uint8_t* _start_addr_bak) {
	start_addr = _start_addr;
	//end_addr = _end_addr;
	end_addr = start_addr + global_size - 2;
	offset = _start_addr - _start_addr_bak;
	// sanity check
	// TODO: offset calculation can be removed
#if 0 // TEMP disable
	while(offset != global_size) {
		PRINTF("global size calculation is wrong: %u vs %u\r\n", offset, global_size);
	}
#endif
}

__nv unsigned chkpt_i = 0;

__nv needUpdate = 0;
void checkpoint();

__nv unsigned clear_bitmask_iter;
void clear_bitmask() {
	// TODO: what if it is too large for one E-cycle?
	unsigned bitmask_num = ((unsigned)((global_size+(PACK_BYTE -1))/PACK_BYTE));
	while (clear_bitmask_iter < bitmask_num) {
		backup_bitmask[clear_bitmask_iter] = 0;
		clear_bitmask_iter++;
	}
}

void _kw_end_run() {
#if OVERHEAD == END_RUN
	P1OUT |= BIT4;
#endif
	PRINTF("chkpt: %u\r\n", debug_cntr);
	debug_cntr = 0;
	if (needRadicalImprovement) {
		needRadicalImprovement = 0; // for robustness against power failure
		if (timer_interval == 0)
			timer_interval = 1;
		else if (timer_interval <= 0x7FFF) {
			if (timer_interval > 1) {
				timer_interval <<= 1;
			}
		}
		else {
			if (timer_overflow_bnd == 0)
				timer_overflow_bnd = 1;
			else if (timer_overflow_bnd <= 0x7FFF)
				timer_overflow_bnd <<= 1;
			timer_interval = 0;
		}
		// this heuristic is not important
		step = timer_interval;
	}
	else if (needSlightImprovement) {
//		timer_overflow_bnd = optimistic_bnd;
		needSlightImprovement = 0; // for robustness against power failure
		timer_overflow_bnd = optimistic_bnd;
		// Since MIN_STEPSIZE > GUARD, this will never cause underflow
		if (optimistic_interval > GUARD) {
			timer_interval = optimistic_interval - GUARD;
		}
		else {
			timer_interval = 1;
		}
	}
	else if (mayNeedDegradation > 2) {
		mayNeedDegradation = 0;
		if (timer_interval > (step >> 1)) {
			timer_interval -= step >> 1;
		}
		else {
			timer_interval = 1;
		}
	}
	new_stepsize = step >> 1;
	checkpoint();
	step = new_stepsize;
	if (step < MIN_STEPSIZE)
		step = MIN_STEPSIZE;
	needRadicalImprovement = 1;
	needSlightImprovement = 1;
	if (timer_interval <= (0xFFFF - step)) {
		optimistic_interval = timer_interval + step;
		optimistic_bnd = timer_overflow_bnd;
	}
	else {
		if (timer_overflow_bnd != 0xFFFF)
			optimistic_bnd = timer_overflow_bnd + 1;
		else
			optimistic_bnd = timer_overflow_bnd;
		optimistic_interval = 0;
	}
	PRINTF("improve: %u %u %u\r\n", timer_overflow_bnd, timer_interval, step);
#if OVERHEAD == END_RUN
	P1OUT &= ~BIT4;
#endif
}

/**
 * @brief checkpoint regs
 */
void checkpoint() {
#if OVERHEAD == CHECKPOINT
	P1OUT |= BIT4;
#endif
	unsigned r12;
	/* When you call this function:
	 * LR gets stored in Stack
	 * R4 gets stored in Stack
	 * Then 22 is added to SP (for local use)
	 * R12 gets stored in Stack
	 * SP gets saved to R4 */
	// TODO: Nubers will change!
	// Check correctness!!
	__asm__ volatile ("PUSH R12"); // we will use R12 for saving cur_reg
	__asm__ volatile ("MOV %0, R12" :"=m"(curctx->cur_reg)); 

	// currently, R4 holds SP, and PC is at 
	__asm__ volatile ("MOV 26(R1), 0(R12)"); // LR is going to be the next PC

	__asm__ volatile ("MOV R1, 2(R12)"); // We need to add 6 to get the prev SP 
	__asm__ volatile ("ADD #28, 2(R12)");
	// TODO: do we need to save R2 (SR)? Because it is chaned while we
	// subtract from SP anyway (guess it does not matters)
	__asm__ volatile ("MOV R2, 4(R12)");
	__asm__ volatile ("MOV 24(R1), 6(R12)"); // R4
	__asm__ volatile ("MOV R5, 8(R12)");
	__asm__ volatile ("MOV R6, 10(R12)");
	__asm__ volatile ("MOV R7, 12(R12)");
	__asm__ volatile ("MOV R8, 14(R12)");
	__asm__ volatile ("MOV R9, 16(R12)");
	__asm__ volatile ("MOV R10, 18(R12)");
	__asm__ volatile ("MOV R11, 20(R12)");
	// TODO: Do we ever have to save R12, R13, R14, R15. Lets not
	// Maybe if we only place checkpointing at the end of a basicblock,
	// We do not need to save these

//	__asm__ volatile ("MOV 0(R1), 22(R12)");
//	__asm__ volatile ("MOV R13, 24(R12)");
//	__asm__ volatile ("MOV R14, 26(R12)");
//	__asm__ volatile ("MOV R15, 28(R12)");

	__asm__ volatile ("MOV R12, %0":"=m"(r12));

	// copy the special stack
	//unsigned stack_size = special_sp  + 2 - (uint8_t*)special_stack;
	////PRINTF("stack size: %u\r\n", stack_size);
	//if (stack_size)
	//	memcpy(curctx->special_stack, special_stack, stack_size);
	uint8_t* last_mod_stack = curctx->stack_tracer > stack_tracer ?
		stack_tracer : curctx->stack_tracer;
	unsigned stack_size = special_sp - last_mod_stack;
	unsigned st_offset = last_mod_stack + 2 - (uint8_t*)special_stack;
	//PRINTF("stack size: %u\r\n", stack_size);
	if (stack_size)
		memcpy(((uint8_t*)curctx->special_stack) + st_offset,
				((uint8_t*)special_stack) + st_offset, stack_size);

	// copy the sp as well
	curctx->special_sp = special_sp;
	//	curctx->stack_tracer = stack_tracer;

	context_t *next_ctx;
	next_ctx = (curctx == &context_0 ? &context_1 : &context_0 );
	next_ctx->cur_reg = curctx->cur_reg == regs_0 ? regs_1 : regs_0;
	next_ctx->backup_index = 0;
	// TEMP disable. is it always correct without this???
	next_ctx->stack_tracer = stack_tracer;

	bitmask_counter++;
	if (!bitmask_counter) {
		need_bitmask_clear = 1;
		bitmask_counter++;
	}
	if (need_bitmask_clear) {
		clear_bitmask();
		need_bitmask_clear = 0;
	}
	timer_expired = ALWAYS_CHECKPOINT;
	debug_cntr++;
	if (optimistic_reached) {
	//if (mayNeedSlightImprovement > 0) {
		// If optimistic interval has reached + checkpoint has taken
		// reset timer
		BITSET(TA1CTL , TACLR); // clear counter here
		mayNeedSlightImprovement = 1;
		optimistic_reached = 0;
	}
	else {
		chkpt_cntr++;
	}
	// reset timer here
	//BITSET(TA1CTL , TACLR);
	//timer_overflow = 0;

	// atomic update of curctx
	curctx = next_ctx;
	isNoProgress = 0;
	//chkpt_ever_taken = 1;
	stack_tracer = special_sp;

	// TODO: Do not know for sure, doing conservative thing
	// Do we need this?
	__asm__ volatile ("MOV %0, R12":"=m"(r12));
	__asm__ volatile ("MOV 4(R12), R2");
	// TODO: We do not save R12-R15
	//	__asm__ volatile ("MOV 24(R12), R13");
	//	__asm__ volatile ("MOV 26(R12), R14");
	//	__asm__ volatile ("MOV 28(R12), R15");
#if OVERHEAD == CHECKPOINT
	P1OUT &= ~BIT4;
#endif
	__asm__ volatile ("POP R12"); // we will use R12 for saving cur_reg
}


bool is_backed_up(uint8_t* addr) {
	unsigned index = (unsigned)(addr - start_addr);
	return backup_bitmask[(unsigned)(index/PACK_BYTE)] == bitmask_counter;
}

// append war_list and backup
void back_up(uint8_t* addr) {
	// If backup array overflows, we consider it as a power failure.
	if (curctx->backup_index == MAX_TRACK) {
		PMMCTL0 = PMMPW | PMMSWPOR;
	}

	//backup the pack
	uint8_t* addr_aligned = (uint8_t*)((unsigned)addr & ~(PACK_BYTE - 1));
	uint8_t* addr_bak = addr_aligned - offset;
	memcpy(addr_bak, addr_aligned, PACK_BYTE);
	//append dirtylist
	//backup_size[curctx->backup_index] = size;
	//backup[curctx->backup_index] = addr;
	backup[curctx->backup_index] = addr_aligned;
	curctx->backup_index++;

	unsigned index = (unsigned)(addr - start_addr);
	backup_bitmask[(unsigned)(index/PACK_BYTE)] = bitmask_counter;
}

#if ENERGY == 0
	__attribute__((interrupt(41)))
void Timer1_A1_ISR(void)
{
	switch(TA1IV) {
		case TA1IV_TACCR1:
			// Timer expired. need checkpoint!
			if (timer_overflow == timer_overflow_bnd) {
				timer_expired = 1;
			}
			break;
		case TA1IV_TACCR2:
			// Timer even reached here.
			if (timer_overflow == optimistic_bnd) {
				// Do not reset timer here, but
				// wait till we take a checkpoint
				// 1. if we die before seeing checkpoint
				// -> optimistic interval is too large
				// 2. if we even meet a checkpoint
				// -> timer_interval needs increasing.
				timer_expired = 1;
				optimistic_reached = 1;
				//mayNeedSlightImprovement = 1;
				//timer_overflow = 0;
				//if (chkpt_cntr > 0) {
					// If optimistic interval has reached + checkpoint has taken
					// reset timer
					//BITSET(TA1CTL , TACLR); // clear counter here
				//}
			}
			break;
		case TA1IV_TAIFG:
			// Timer overflow
			timer_overflow++;
			break;
	}
	//	BITCLR(TA1CTL , TAIFG);
}
__attribute__((section("__interrupt_vector_timer1_a1"),aligned(2)))
void(*__vector_timer1_a1)(void) = Timer1_A1_ISR;
#endif

//__attribute__((interrupt(39)))
//void Timer2_A0_ISR(void)
//{
//	if (TA1IV == 0x0E) {
//		timer_overflow++;
//		if (timer_overflow == timer_overflow_bnd) {
//			timer_expired = 1;
//		}
//	}
//	else if (TA1IV == 0x02) {
//		needSlightImprovement = 1;
//	}
//	BITCLR(TA1CTL , TAIFG);
//}
//__attribute__((section("__interrupt_vector_timer2_a0"),aligned(2)))
//void(*__vector_timer2_a0)(void) = Timer2_A0_ISR;

#if ENERGY == 0
/**
 * @brief Function resotring on power failure
 */
void restore() {
#if OVERHEAD == RESTORE
	P1OUT |= BIT4;
#endif
	bitmask_counter++;
	if (!bitmask_counter) {
		need_bitmask_clear = 1;
		clear_bitmask_iter = 0;
		bitmask_counter++;
	}
	if (need_bitmask_clear) {
		clear_bitmask();
		need_bitmask_clear = 0;
	}
	// restore NV globals
	while (curctx->backup_index != 0) {
		uint8_t* w_data_dest = backup[curctx->backup_index - 1];
		uint8_t* w_data_src = w_data_dest - offset;
		//unsigned w_data_size = backup_size[curctx->backup_index - 1];
		memcpy(w_data_dest, w_data_src, PACK_BYTE);
		--(curctx->backup_index);
	}

	// restore regs (including PC)
	restore_regs();
}

/**
 * @brief restore regs
 */
void restore_regs() {
	// start timer here
//		P1OUT &= ~BIT4;
	BITSET(TA1CCTL1 , CCIE);
	BITSET(TA1CCTL2 , CCIE);
	TA1CCR1 = timer_interval;
	TA1CCR2 = optimistic_interval;
	timer_expired = ALWAYS_CHECKPOINT;
	//	BITSET(TA1CTL , (TASSEL_1 | MC_2 | TACLR | TAIE));
	// Timer will never overflow anyways
	BITSET(TA1CTL , (TASSEL_1 | MC_2 | TACLR));

	// If even single cycle are against improvement,
	// do not try improving
	needSlightImprovement &= mayNeedSlightImprovement;
	if (chkpt_cntr < 2) {
		needRadicalImprovement = 0;
	}
	chkpt_cntr = 0;
	mayNeedSlightImprovement = 0;
	optimistic_reached = 0;

	//timer_overflow = 0;
	context_t* prev_ctx;
	unsigned pc;

	if (!chkpt_ever_taken) {
		curctx->cur_reg = regs_0;
		chkpt_ever_taken = 1;
		// first, grab any checkpoint
		timer_expired = 1;
		return;
	}
	// TODO: potential bug point
	//else if (curctx->cur_reg == regs_0) {
	else if (curctx == &context_0) {
		//prev_reg = regs_1;
		prev_ctx = &context_1;
	}
	else {
		prev_ctx = &context_0;
		//prev_reg = regs_0;
	}

	if (isNoProgress) {
		stuck_cntr++;
		mayNeedDegradation++;
		// If stuck, and cannot proceed
		if (stuck_cntr > 2) {
			if (timer_overflow_bnd > 0) {
				timer_overflow_bnd >>= 1;
			}
			else {
				if (timer_interval > 1)
					timer_interval >>= 1;
				else {
//					P1OUT |= BIT4;
//					P1OUT &= ~BIT4;
				}
				// binary step decision
			}
			optimistic_bnd = timer_overflow_bnd;
			step = timer_interval >> 1;
			if (step < MIN_STEPSIZE)
				step = MIN_STEPSIZE;

			if (timer_interval <= (0xFFFF - step)) {
				optimistic_interval = timer_interval + step;
			}
			else {
				if (optimistic_bnd < 0xFFFF)
					optimistic_bnd++;
				optimistic_interval = 0;
			}
			// if radical decrease takes place, no need for slight decrease
			mayNeedDegradation = 0;
		}
		PRINTF("backoff: %u %u %u %u\r\n", timer_overflow_bnd, timer_interval,
				optimistic_bnd, optimistic_interval);
	}
	else {
		stuck_cntr = 0;
	}
	isNoProgress = 1;

	// copy the sp as well
	special_sp = prev_ctx->special_sp;
	// copy the special stack
	//unsigned stack_size = special_sp + 2 - (uint8_t*)special_stack;
	unsigned stack_size = special_sp - stack_tracer;
	unsigned st_offset = stack_tracer  + 2 - (uint8_t*)special_stack;
	if (stack_size)
		memcpy(((uint8_t*)special_stack) + st_offset,
				((uint8_t*)prev_ctx->special_stack) + st_offset, stack_size);

	__asm__ volatile ("MOV %0, R12" :"=m"(prev_ctx->cur_reg));
	// TODO: do we need R15 - R12? Lets not
	//	__asm__ volatile ("MOV 28(R12), R15");
	//	__asm__ volatile ("MOV 26(R12), R14");
	//	__asm__ volatile ("MOV 24(R12), R13");
	__asm__ volatile ("MOV 20(R12), R11");
	__asm__ volatile ("MOV 18(R12), R10");
	__asm__ volatile ("MOV 16(R12), R9");
	__asm__ volatile ("MOV 14(R12), R8");
	__asm__ volatile ("MOV 12(R12), R7");
	__asm__ volatile ("MOV 10(R12), R6");
	__asm__ volatile ("MOV 8(R12), R5");
	__asm__ volatile ("MOV 6(R12), R4");
	__asm__ volatile ("MOV 4(R12), R2");
	__asm__ volatile ("MOV 2(R12), R1");
	__asm__ volatile ("MOV 0(R12), %0" :"=m"(pc));
#if OVERHEAD == RESTORE
	P1OUT &= ~BIT4;
#endif
	//	__asm__ volatile ("MOV 22(R12), R12");
	__asm__ volatile ("MOV %0, R0" :"=m"(pc));
}
// slow search, no reset version
void check_before_write_may(uint8_t *addr) {
#if OVERHEAD == UNDO_LOG
	P1OUT |= BIT4;
#endif
	if (addr < start_addr || addr > end_addr) {
#if OVERHEAD == UNDO_LOG
		P1OUT &= ~BIT4;
#endif
		return;
	}
	unsigned index = (unsigned)(addr - start_addr);

	if(backup_bitmask[(unsigned)(index/PACK_BYTE)] == bitmask_counter) {
		//if (is_backed_up(addr)) {
#if OVERHEAD == UNDO_LOG
		P1OUT &= ~BIT4;
#endif
		return;
	}
	//back_up(addr);
	if (curctx->backup_index == MAX_TRACK) {
		PMMCTL0 = PMMPW | PMMSWPOR;
	}

	//backup the pack
	uint8_t* addr_aligned = (uint8_t*)((unsigned)addr & ~(PACK_BYTE - 1));
	uint8_t* addr_bak = addr_aligned - offset;
	memcpy(addr_bak, addr_aligned, PACK_BYTE);
	//append dirtylist
	//backup_size[curctx->backup_index] = size;
	//backup[curctx->backup_index] = addr;
	backup[curctx->backup_index] = addr_aligned;
	curctx->backup_index++;

	backup_bitmask[(unsigned)(index/PACK_BYTE)] = bitmask_counter;
#if OVERHEAD == UNDO_LOG
	P1OUT &= ~BIT4;
#endif
	return;
	}

	void check_before_write_must(uint8_t *addr) {
#if OVERHEAD == UNDO_LOG
	P1OUT |= BIT4;
#endif
		unsigned index = (unsigned)(addr - start_addr);

		if(backup_bitmask[(unsigned)(index/PACK_BYTE)] == bitmask_counter) {
#if OVERHEAD == UNDO_LOG
		P1OUT &= ~BIT4;
#endif
			return;
		}
		if (curctx->backup_index == MAX_TRACK) {
			PMMCTL0 = PMMPW | PMMSWPOR;
		}

		//backup the pack
		uint8_t* addr_aligned = (uint8_t*)((unsigned)addr & ~(PACK_BYTE - 1));
		uint8_t* addr_bak = addr_aligned - offset;
		memcpy(addr_bak, addr_aligned, PACK_BYTE);
		//append dirtylist
		//backup_size[curctx->backup_index] = size;
		//backup[curctx->backup_index] = addr;
		backup[curctx->backup_index] = addr_aligned;
		curctx->backup_index++;

		backup_bitmask[(unsigned)(index/PACK_BYTE)] = bitmask_counter;
#if OVERHEAD == UNDO_LOG
	P1OUT &= ~BIT4;
#endif
		return;
	}

	// slight optimization. This does not check for prev backup and just back up
	void check_before_write_must_unconditional(uint8_t *addr) {
#if OVERHEAD == UNDO_LOG
	P1OUT |= BIT4;
#endif
		unsigned index = (unsigned)(addr - start_addr);

		if (curctx->backup_index == MAX_TRACK) {
			PMMCTL0 = PMMPW | PMMSWPOR;
		}

		//backup the pack
		uint8_t* addr_aligned = (uint8_t*)((unsigned)addr & ~(PACK_BYTE - 1));
		uint8_t* addr_bak = addr_aligned - offset;
		memcpy(addr_bak, addr_aligned, PACK_BYTE);
		//append dirtylist
		//backup_size[curctx->backup_index] = size;
		//backup[curctx->backup_index] = addr;
		backup[curctx->backup_index] = addr_aligned;
		curctx->backup_index++;

		backup_bitmask[(unsigned)(index/PACK_BYTE)] = bitmask_counter;
#if OVERHEAD == UNDO_LOG
	P1OUT &= ~BIT4;
#endif
		return;
	}
#endif








	// For energy measurement
#if ENERGY == 1
	/**
	 * @brief Function resotring on power failure
	 */
	void restore() {
		bitmask_counter++;
		if ((!bitmask_counter) || 1) { // Worst case
			need_bitmask_clear = 1;
			clear_bitmask_iter = 0;
			bitmask_counter++;
		}
		if (need_bitmask_clear) {
			clear_bitmask();
			need_bitmask_clear = 0;
		}
		// restore NV globals
		while (curctx->backup_index != 0) {
			uint8_t* w_data_dest = backup[curctx->backup_index - 1];
			uint8_t* w_data_src = w_data_dest - offset;
			//unsigned w_data_size = backup_size[curctx->backup_index - 1];
			memcpy(w_data_dest, w_data_src, PACK_BYTE);
			--(curctx->backup_index);
		}

		// restore regs (including PC)
		restore_regs();
	}

	/**
	 * @brief restore regs
	 */
	void restore_regs() {
		context_t* prev_ctx;
		unsigned pc;
		//	if (curctx->cur_reg == NULL) {
		if ((!chkpt_ever_taken) && 0) {
			curctx->cur_reg = regs_0;
			chkpt_ever_taken = 1;
			mode_status = RECOVERY_MODE;
			return;
		}
		// TODO: potential bug point
		//else if (curctx->cur_reg == regs_0) {
		else if (curctx == &context_0) {
			//prev_reg = regs_1;
			prev_ctx = &context_1;
		}
		else {
			prev_ctx = &context_0;
			//prev_reg = regs_0;
		}
		if ((mode_status == RECOVERY_MODE) && 0) {
			//PRINTF("recovery: %u\r\n", prev_ctx->cur_reg[15]);
			//if (isNoProgress) {
			//	// this mean even if it was in the recovery mode,
			//	// it couldn't checkpoint once. weird!!!
			//}
			if (prev_ctx->cur_reg[15] != 0xFFFF) {
				chkpt_status[prev_ctx->cur_reg[15]] = 0;
				//chkpt_status[prev_ctx->cur_reg[15]] = CHKPT_ACTIVE;
				//chkpt_book[prev_ctx->cur_reg[15]] = 2;
				chkpt_book[prev_ctx->cur_reg[15]] = 1;
			}

			mode_status = NORMAL_MODE;
		}
		else {
			if (isNoProgress && 0) {
				mode_status = RECOVERY_MODE;
			}
			else {
				// specialize for loops
				if ((curctx->cur_reg[15] == prev_ctx->cur_reg[15]) && 0) {
					if (prev_ctx->cur_reg[15] != 0xFFFF) {
						prev_ctx->cur_reg[15] = 0xFFFF;
						curctx->cur_reg[15] = 0xFFFF;
					}
				}
				else {
					//chkpt_book[prev_ctx->cur_reg[15]] += 2;
					if ((prev_ctx->cur_reg[15] != 0xFFFF) || 1) {
						chkpt_book[prev_ctx->cur_reg[15]] += 2;
						prev_ctx->cur_reg[15] = 0xFFFF;
					}
					if ((curctx->cur_reg[15] != 0xFFFF) || 1) {
						chkpt_book[curctx->cur_reg[15]]--;
						curctx->cur_reg[15] = 0xFFFF;
					}
				}
			}
		}
		isNoProgress = 1;

		// copy the sp as well
		special_sp = prev_ctx->special_sp;
		// copy the special stack
		//unsigned stack_size = special_sp + 2 - (uint8_t*)special_stack;
		unsigned stack_size = special_sp - stack_tracer;
		unsigned st_offset = stack_tracer  + 2 - (uint8_t*)special_stack;
		if (stack_size && 0)
			memcpy(((uint8_t*)special_stack) + st_offset,
					((uint8_t*)prev_ctx->special_stack) + st_offset, stack_size);
		//	unsigned stack_size = special_sp + 2 - (uint8_t*)special_stack;
		//	if (stack_size)
		//		memcpy(special_stack, 
		//				prev_ctx->special_stack, stack_size);

#if 0 //case 2.
		//chkpt_book[prev_reg[15]] = 0;
#endif
#if 0 // case 1.
		//	chkpt_book[prev_reg[15]]++;
#endif
		__asm__ volatile ("MOV %0, R12" :"=m"(prev_ctx->cur_reg)); 
		// TODO: do we need R15 - R12? Lets not
		//	__asm__ volatile ("MOV 28(R12), R5");
		//	__asm__ volatile ("MOV 26(R12), R5");
		//	__asm__ volatile ("MOV 24(R12), R5");
		__asm__ volatile ("MOV 20(R12), R5");
		__asm__ volatile ("MOV 18(R12), R5");
		__asm__ volatile ("MOV 16(R12), R5");
		__asm__ volatile ("MOV 14(R12), R5");
		__asm__ volatile ("MOV 12(R12), R5");
		__asm__ volatile ("MOV 10(R12), R5");
		__asm__ volatile ("MOV 8(R12), R5");
		__asm__ volatile ("MOV 6(R12), R5");
		__asm__ volatile ("MOV 4(R12), R5");
		__asm__ volatile ("MOV 2(R12), R5");
		__asm__ volatile ("MOV 0(R12), %0" :"=m"(pc));
		//	__asm__ volatile ("MOV 22(R12), R12");
		__asm__ volatile ("MOV %0, R5" :"=m"(pc));
	}
	void check_before_write_may(uint8_t *addr) {
		if ((addr < start_addr || addr > end_addr) && 0)
			return;
		unsigned index = (unsigned)(addr - start_addr);

		if((backup_bitmask[(unsigned)(index/PACK_BYTE)] == bitmask_counter) && 0) {
			return;
		}
		//back_up(addr);
		if ((curctx->backup_index == MAX_TRACK) && 0) {
			PMMCTL0 = PMMPW | PMMSWPOR;
		}

		//backup the pack
		uint8_t* addr_aligned = (uint8_t*)((unsigned)addr & ~(PACK_BYTE - 1));
		uint8_t* addr_bak = addr_aligned - offset;
		memcpy(addr_bak, addr_aligned, PACK_BYTE);
		//append dirtylist
		//backup_size[curctx->backup_index] = size;
		//backup[curctx->backup_index] = addr;
		backup[curctx->backup_index] = addr_aligned;
		curctx->backup_index++;

		backup_bitmask[(unsigned)(index/PACK_BYTE)] = bitmask_counter;
		return;
	}

	void check_before_write_must(uint8_t *addr) {
		unsigned index = (unsigned)(addr - start_addr);

		if((backup_bitmask[(unsigned)(index/PACK_BYTE)] == bitmask_counter) && 0) {
			return;
		}
		if ((curctx->backup_index == MAX_TRACK) && 0) {
			PMMCTL0 = PMMPW | PMMSWPOR;
		}

		//backup the pack
		uint8_t* addr_aligned = (uint8_t*)((unsigned)addr & ~(PACK_BYTE - 1));
		uint8_t* addr_bak = addr_aligned - offset;
		memcpy(addr_bak, addr_aligned, PACK_BYTE);
		//append dirtylist
		//backup_size[curctx->backup_index] = size;
		//backup[curctx->backup_index] = addr;
		backup[curctx->backup_index] = addr_aligned;
		curctx->backup_index++;

		backup_bitmask[(unsigned)(index/PACK_BYTE)] = bitmask_counter;
		return;
	}

	// slight optimization. This does not check for prev backup and just back up
	void check_before_write_must_unconditional(uint8_t *addr) {
		unsigned index = (unsigned)(addr - start_addr);

		if ((curctx->backup_index == MAX_TRACK) && 0) {
			PMMCTL0 = PMMPW | PMMSWPOR;
		}

		//backup the pack
		uint8_t* addr_aligned = (uint8_t*)((unsigned)addr & ~(PACK_BYTE - 1));
		uint8_t* addr_bak = addr_aligned - offset;
		memcpy(addr_bak, addr_aligned, PACK_BYTE);
		//append dirtylist
		//backup_size[curctx->backup_index] = size;
		//backup[curctx->backup_index] = addr;
		backup[curctx->backup_index] = addr_aligned;
		curctx->backup_index++;

		backup_bitmask[(unsigned)(index/PACK_BYTE)] = bitmask_counter;
		return;
	}
#endif
