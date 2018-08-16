# alpaca-pass

LLVM Pass for Alpaca programming model reference implementation

Build:

	$ (rm -rf build)
	$ (mkdir build)
	$ cd build
	$ cmake ..
	$ make


Run:

	$ clang -Xclang -load -Xclang build/src/libAlpacaPass.* something.c
