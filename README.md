# Alpaca: Intermittent Programs without Checkpoints

Alpaca ([OOPSLA\'17](https://dl.acm.org/citation.cfm?doid=3152284.3133920)) is
a task-based programming model for writing reliable software for intermittent,
energy-harvesting computer systems.

Alpaca programs are written as a set of tasks that access shared data in
non-volatile memory and private data in task-local variables. The programmer
uses macros defined in `libalpaca` library to declare tasks and identify the
shared variables. A compiler pass detects which of the variables need to be
protected such that the tasks have a consistent view of the data despite
reboots due to power failure.  The compiler inserts code to privatize protected
data and commit it atomically upon transition to the following task. The
runtime library implements the two-phase commit.

Programming interface
---------------------

Tasks are declared with the `TASK()` macro and defined by a void function:

    TASK(index, task_func)
    void task_func() { ... }

where `index` is a unique numeric index that identifies the task.

A reference to a task can be assigned to a variable using a helper macro:

    task_t *var = TASK_REF(task_func);

To transfer control from one task to another, task code invokes
the `TRANSITION_TO()` macro at any point:

    TRANSITION_TO(task_func);

A variable named `var` of type `type` that is accessed by multiple tasks (and
is known as a *protected* variable) is declared and defined in global scope with:

    GLOBAL_SB(type, var);

A protected array with *n* elements is declared and defined using the same macro:

    GLOBAL_SB(type, var, n);

Task code accesses protected variables through an accessor macro:

    GV(var) = val;
    type local_var = GV(var);

    GV(arr, index) = val;
    type local_var = GV(arr, index);

Building applications with Alpaca
---------------------------------

Alpaca ships with recipes for [Maker](https://github.com/CMUAbstract/maker)
build system. Creating applications with Maker is documented in the [Maker
documentation](https://github.com/CMUAbstract/maker). Applications that use
Maker can include the [Alpaca toolchain](https://github.com/CMUAbstract/alpaca)
as a dependent git submodule, and have Maker build the toolchain itself and the
application with the toolchain.

The advantage of including the toolchain as a dependency, alongside
other library dependencies, is that the application repository will refer to an
exact snapshot of the toolchain, giving explicit control over updating the
(evolving) toolchain.

An application built with Maker contains the `ext/` directory for external
dependencies references as git submodules, `src/` for application source code,
and `bld/` for build artifacts organized in a subdirectory per toolchain, with
Alpaca's artifacts in `bld/alpaca`.

Add Alpaca toolchain as a submodule in `ext/`:

    cd ext/ && git submodule add https://github.com/CMUAbstract/alpaca

and declaring the link dependency on `libalpaca` in `bld/Makefile`

    DEPS += libalpaca

To tell Maker to build the Alpaca compiler passes (only needs to be done once):

    make ext/alpaca/llvm

To tell Maker to build the `libalpaca` dependency and then the application with
Alpaca's compiler passes:

    make bld/alpaca/all
