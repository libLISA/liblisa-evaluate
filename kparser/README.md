# A warning
This code replicates Dasgupta et al.'s approach to SMT generation here: https://github.com/sdasgup3/validating-binary-decompilation/blob/master/source/libs/exprs/exprs.cpp -- but it eliminates the need for the K framework by implementing a just-barely-good-enough parser and rewrite engine.

In implementing this parser, we have taken many shortcuts. *This code will likely break when used on anything other than the X86-64 semantics from Dasgupta et al.*