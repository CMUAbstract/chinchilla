LLVM_DIR = LLVM

ifneq ($(ALPACA_DEBUG_LOG),)
  CMAKE_VARS += -DDEBUG_LOG=$(ALPACA_DEBUG_LOG)
endif

include $(MAKER_ROOT)/Makefile.llvm
