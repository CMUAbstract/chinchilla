#ifndef CHINCHILLA_H
#define CHINCHILLA_H

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#include <libmsp/mem.h>

//#define CHKPT_NUM 65
#define VAR_NUM 30
#define NOP 0x43034303
#define end_run() _kw_end_run()
#define SPECIAL_STACK_SIZE 300
typedef void (task_func_t)(void);
typedef unsigned task_idx_t;

extern unsigned chkpt_count;
//extern uint16_t mode_status;
extern uint8_t timer_expired;
extern uint8_t isNoProgress;
extern uint8_t* stack_tracer;
extern volatile unsigned regs_0[16];
extern volatile unsigned regs_1[16];
/** @brief Task */
//typedef struct {
	/** @brief function address */
//	task_func_t *func;
	/** @brief index (only used for showing progress) */
//	task_idx_t idx;
//} task_t;
typedef struct _chkpt_info {
	unsigned backup; 
	unsigned* fix_point;
	unsigned fix_to;
} chkpt_info;

typedef struct _vars {
	// TODO: maybe uint8_t will be enough
	unsigned cutted_num;
	uint32_t* nopable_address;
} vars;
/** @brief Execution context */
typedef struct _context_t {
	/** @brief current register */
	unsigned* cur_reg;
	/** @brief indicate whether to jump to commit stage on power failure*/
	volatile unsigned backup_index;	
	uint8_t* special_stack[SPECIAL_STACK_SIZE];
	uint8_t* special_sp;
	uint8_t* stack_tracer;
} context_t;

//extern uint8_t* data_src[];
//extern uint8_t* data_dest[];
//extern unsigned data_size[];
//extern uint8_t** data_src_base;
//extern uint8_t** data_dest_base;
//extern unsigned* data_size_base;
extern volatile unsigned _numBoots;
extern volatile unsigned num_dirty_gv;
extern context_t * volatile curctx;
extern int8_t chkpt_book[];
extern uint16_t chkpt_status[];
extern chkpt_info chkpt_list[];
extern uint8_t backup_bitmask[];
extern unsigned global_size;
extern unsigned CHKPT_NUM;
extern unsigned debug_cntr;
//extern unsigned max_backup;
void _kw_end_run();
void restore_regs();
void patch_logging();
void push_to_nvstack();
void return_to_nvstack();
/** @brief LLVM generated function that clears all isDirty_ array */
//extern void clear_isDirty();
/** @brief Function called on every reboot
 *  @details This function usually initializes hardware, such as GPIO
 *           direction. The application must define this function because
 *           different app uses different GPIO.
 */
extern void init();

void set_global_range(uint8_t* _start_addr, uint8_t* _end_addr, uint8_t* _start_addr_bak);
void task_prologue();
void transition_to(void (*task)());
void write_to_gbuf(uint8_t *data_src, uint8_t *data_dest, size_t var_size); 
//void __loop_bound__(unsigned val){};

/** @brief Internal macro for constructing name of task symbol */
#define TASK_SYM_NAME(func) _task_ ## func

/** @brief Declare a task
 *
 *  @param idx      Global task index, zero-based
 *  @param func     Pointer to task function
 *
 */
#define TASK(idx, func) \
	void func(); //\
//__nv task_t TASK_SYM_NAME(func) = { func, idx }; \

/** @brief Macro for getting address of task */
//#define TASK_REF(func) &TASK_SYM_NAME(func)
#define TASK_REF(func) &func

/** @brief First task to run when the application starts
 *  @details Symbol is defined by the ENTRY_TASK macro.
 *           This is not wrapped into a delaration macro, because applications
 *           are not meant to declare tasks -- internal only.
 *
 *  TODO: An alternative would be to have a macro that defines
 *        the curtask symbol and initializes it to the entry task. The
 *        application would be required to have a definition using that macro.
 *        An advantage is that the names of the tasks in the application are
 *        not constrained, and the whole thing is less magical when reading app
 *        code, but slightly more verbose.
 */
//extern task_t TASK_SYM_NAME(_entry_task);

/** @brief Declare the first task of the application
 *  @details This macro defines a function with a special name that is
 *           used to initialize the current task pointer.
 *
 *           This does incur the penalty of an extra task transition, but it
 *           happens only once in application lifetime.
 *
 *           The alternatives are to force the user to define functions
 *           with a special name or to define a task pointer symbol outside
 *           of the library.
 */
#define ENTRY_TASK(task) \
	TASK(0, _entry_task) \
void _entry_task() { TRANSITION_TO(task); }

/** @brief Init function prototype
 *  @details We rely on the special name of this symbol to initialize the
 *           current task pointer. The entry function is defined in the user
 *           application through a macro provided by our header.
 */
void _init();

/** @brief Declare the function to be called on each boot
 *  @details The same notes apply as for entry task.
 */
#define INIT_FUNC(func) void _init() { func(); }

/**
 *  @brief way to simply rename vars. I don't need it actually.
 *  I should remove it or rename it..
 *  Actually I should just remove this thing!
 */
#define GLOBAL_SB(type, name, ...) GLOBAL_SB_(type, name, ##__VA_ARGS__, 3, 2)
#define GLOBAL_SB_(type, name, size, n, ...) GLOBAL_SB##n(type, name, size)
#define GLOBAL_SB2(type, name, ...) __nv type _global_ ## name
#define GLOBAL_SB3(type, name, size) __nv type _global_ ## name[size]

/**
 *  @brief way to simply reference renamed vars. I don't need it actually.
 *  I should remove it or rename it..
 *  Actually I should just remove this thing!
 */
#define GV(type, ...) GV_(type, ##__VA_ARGS__, 2, 1)
#define GV_(type, i, n, ...) GV##n(type, i)
#define GV1(type, ...) _global_ ## type
#define GV2(type, i) _global_ ## type[i]

/** @brief Transfer control to the given task
 *  @param task     Name of the task function
 *  */
//#define TRANSITION_TO(task) transition_to(TASK_REF(task))
#define TRANSITION_TO(task) transition_to(&task)
#endif // CHINCHILLA_H
