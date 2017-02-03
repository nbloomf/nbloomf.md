---
title: Notes on Homework 1
---

([Go back to the course page](/classes/parp/index.html))

## Links

* [Stampede User Guide](https://portal.tacc.utexas.edu/user-guides/stampede)


## Meta-info (how to run programs)

Before digging into the guts of the homework assignment itself, we need to learn the mechanics of just how to compile and run our programs.


### Basics

All our homework programs will be compiled and run from your shell on XSEDE machines. To do this we will log in remotely, using either ``ssh`` (on a unix-like machine) or ``putty`` (from Windows). If you have never used either of these tools before, don't worry! We'll learn what we need to know.


### The Shell

A shell, also called a "terminal" for historical reasons, is a textual interface for interacting with your computer. Windows has two shells built in: cmd and PowerShell. Unix has several different shells; ``bash`` is the default. For this class it doesn't matter which shell you use.

If you've never used a shell before, it will probably seem confusing at first. But I highly recommend that you give it a shot -- with practice you can be much more productive on the command line than by pointing and clicking.

From now on I'll assume you have a shell open; the shell prompt is ``$>``.


### Logging in to Stampede

* **To log in** to Stampede using ``ssh``:

    ```bash
    $> ssh username@login.xsede.org

    $> gsissh stampede
    ```

    (replace ``username`` with your actual username!)

* **To log in** to Stampede using ``putty``:

    ```bash
    ???
    ```

You did remember to set up the DUO 2FA on your XSEDE account, right? :) If not, the login server will complain and not let you in. If so, you'll get a phone call or text to verify your identity.

Note that regardless of what OS your computer is running, Stampede is running some version of unix. So once we've ``ssh``d into Stampede, we will only be using unix commands.


### Getting, compiling, and running the sample programs

On stampede, you have three different working directories: ``$HOME``, ``$WORK``, and ``$SCRATCH``. Your programs will live in ``$WORK``. To go to that directory, use ``cdw``.

* To **get the files** for Homework 1:

    ```bash
    $> cdw

    $> wget https://nbloomf.github.io/raw/parp/xsede_hw1_2017.tar

    $> tar -xvzf xsede_hw1_2017.tar
    ```

* To **explore the files** that you just unpacked:

    ```bash
    $> cd hw1

    $> ls
    ```

* To **build your code**:

    ```bash
    $> cdw

    $> cd hw1

    $> make
    ```

* Programs are not simply run; they are **scheduled** using the ``sbatch`` tool by supplying a *job script*. The sample code comes with three different programs, each with a job script:

    * ``job-naive`` runs ``benchmark-naive``,
    * ``job-blocked`` runs ``benchmark-blocked``, and
    * ``job-blas`` runs ``benchmark-blas``.

    To run ``benchmark-naive``, for example, say

    ```bash
    $> sbatch job-naive
    ```

* The output (``stdout`` and ``stderr``) of your programs will be sent to files as specified in the job script.

* To **read and edit text** (code/scripts/logs)

    Use ``vim`` or ``emacs`` or ``nano`` (my favorite).

Handy tip: you can configure the job scripts to send you an email when your job starts and finishes. To do this, add these lines to your build script. This is more useful if the machine is busy (so your job is queued for a while) or if your job will take a long time.

```bash
#SBATCH --mail-user={your email}
#SBATCH --mail-type=all
```

## The Assignment

The file you turn in will be named ``dgemm.c`` and must include two functions with precise signatures. We will get started by copying one of the examples.

```bash
$> cp dgemm-blocked.c dgemm.c
$> cp job-blocked job
```

Now we need to edit the ``Makefile`` to compile our hand-tuned program. Change the lines

```
targets = benchmark-naive benchmark-blocked benchmark-blas
objects = benchmark.o dgemm-naive.o dgemm-blocked.o dgemm-blas.o
```

to this:

```
targets = benchmark-naive benchmark-blocked benchmark-blas benchmark-hw1
objects = benchmark.o dgemm-naive.o dgemm-blocked.o dgemm-blas.o dgemm.o
```

And add this:

```
benchmark-hw1 : benchmark.o dgemm.o
        $(CC) -o $@ $^ $(LDLIBS)
```

to the end of the list of rules.

You should now be able to compile your copied code; try it with ``make``.

Last but not least, we need to edit the job script to run our program ``benchmark-hw1``. To do this, open ``job`` and change this:

```
#SBATCH -o MyBlockedOutputFile.%j.out
#SBATCH -e MyBlockedErrorFile.%j.err

./benchmark-blocked
```

to this:

```
#SBATCH -o HW1_OutputFile.%j.out
#SBATCH -e HW1_ErrorFile.%j.err

./benchmark-hw1
```

Test it out with

```bash
sbatch job
```

If all this went well, you can now play with the source file ``dgemm.c``. This is the file we will eventually submit for grading.
