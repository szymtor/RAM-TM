Turing machines and word random access machines compute exactly the same
total functions from finite lists of natural numbers to finite lists of
natural numbers. The word RAM is the archive's existing canonical model.
Because that machine has a finite word length, plain RAM computability
includes a computable input-dependent threshold above which one uniform
program must return the exact answer. The effective threshold rules out
the strictly weaker notion of convergence without a computable modulus.

The submission also states the polynomial-time refinement. Both machines
measure an input by the length of one canonical binary encoding. On the RAM
side, one polynomial bounds the sufficient word length and another bounds
the number of instructions; this is exactly the restriction needed for a
Turing simulation of unit-cost word operations to retain polynomial time.
