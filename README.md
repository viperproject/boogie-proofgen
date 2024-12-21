# Proof Generation for Boogie

This is a version of the [Boogie verifier](https://github.com/boogie-org/boogie) 
that extends the verifier with proof generation capabilities for a subset of
the Boogie intermediate verification language (see below for the currently
supported subset).

The goal of this project is to increase the reliability of the Boogie verifier.
Whenever the tool is run on a program, the proof generation extension generates 
an Isabelle proof that shows a transformed version of the input program is 
correct under the assumption of the VC that Boogie generates.

Most of the source code in the `Source` folder is directly forked from the original
source. The main extension is implemented as a C# project in `Source/ProofGeneration`.
Moreover, the existing source has been instrumented to generate calls to the 
proof generation module such that enough information is obtained to generate 
a proof.


## What do the proofs show
Boogie performs various transformations on the input program before finally
generating an AST. For the default Boogie options, the steps performed by 
Boogie are roughly as follows (and also in this order):

1. Parse source AST program to an internal CFG representation (from this point onwards
only CFG representations are used)
2. Basic transformations 1: eliminate dead variables, coalesce blocks, prune unreachable blocks
3. CFG-to-DAG phase: eliminate cycles via loop invariants
4. Basic transformations 2: insert pre- and postconditions (in potentially new blocks), 
ensure that no join block (a block with multiple predecessors) has a predecessor
with multiple successors
5. Passification phase: eliminate assignments via variable versioning and assumptions + perform
constant propagation
6. Basic transformations 3: Remove empty blocks, prune unreachable blocks
7. VC phase: generate VC using weakest precondition

Our certificate shows for each procedure that the CFG right before the CFG-to-DAG 
phase is correct under the assumption of the VC. That is, we support all the 
transformation listed above except those listed in points 1 and 2.

**Note: points 1 and 2 are also handled on [a separate branch](https://github.com/viperproject/boogie-proofgen/tree/cfg_optimizations) that has not yet been merged into this default branch.**

## Modifications to the VC
We change the VC that Boogie generates in the following ways:
1. We do not generate any axioms about built-in types that we do not support.
2. We do not generate any counterexample-related variables in the VC (since our 
results are mainly relevant for verifying programs we do not need these variables)

Both of these changes are trivial: The first change just requires commenting out
some lines and the second change just requires invoking a VC generation method
with a "null" argument where a counterexample-related argument is expected.


## Supported subset
We currently support only the default Boogie options and we do not
support any attributes (the subsumption attribute is one exception). In terms of
language features, we currently support:
* Integers and booleans
* Type constructors
* (Polymorphic) functions
* Most operations on integers/booleans
* Type and value quantification
* Old expressions
* Any gotos/labels/while loops that Boogie accepts
* Commands: assertions, assumptions, assignments, havocs

Moreover, we currently do not support files that contain type constructors without
any polymorphism. The reason is that Boogie currently monomorphizes such programs,
which leads to a different VC. If you want to try such programs, just add some 
polymorphic function to the program such as `function test<T>(x:T):T` (that
does not have to be used anywhere).

## Dependencies
Our tool has the same dependencies as Boogie for the generation of Isabelle proofs:
* [.NET Core](https://dotnet.microsoft.com)
* a supported SMT solver (see the [original Boogie repository](https://github.com/boogie-org/boogie)
for details)

To check Isabelle proofs, one additionally requires Isabelle 2021, as well as 
an installation of the Isabelle session that provides the [formalization of 
Boogie](https://github.com/gauravpartha/foundational_boogie/). Installation
of this session can be done by adding the path to `foundational_boogie/BoogieLang`
to the `ROOTS` file in the Isabelle home directory.

## Building

To build the Boogie proof generation extension run:

```
dotnet build Source/Boogie.sln
```

The compiled Boogie binary is
`Source/BoogieDriver/bin/${CONFIGURATION}/${FRAMEWORK}/BoogieDriver`.

## Running the tool
One can run the tool with any standard Boogie options that do not affect the 
transformations executed by the verifier. For example, running 
```BoogieDriver /proverLog:vc.smt2 <boogie_file>```
is fine, since this just stores the generated VC in `vc.smt2`.

The main new non-experimental option that we provide is `/proofOutputDir`.
`BoogieDriver /proofOutputDir:<dir_path> <boogie_file>` creates a directory 
with path `dir_path` in which the Isabelle proofs are stored. If there already
is a directory at `dir_path`, then an error is reported. If this option is not 
provided (i.e., one invokes `boogieproof <boogie_file>`), then a new folder with 
the name `<boogie_file>_proofs` is created (and possibly some suffix if such a 
directory already exists) in which the proofs are stored.

In the proof generation output folder, a separate folder is created for each 
procedure. There are multiple Isabelle theory files in each folder. The main
theorem for the procedure is the last Isabelle lemma in the file with the suffix
`cfg_to_dag_proof.thy`. This final lemma shows that the validity of the VC 
implies correctness of the input CFG of the CFG-to-DAG phase.

When using the tool, one currently needs to make sure that no special characters
are used that are reserved in Isabelle (such as `#` or `'`). Moreover, for
files that do not verify, the tool cannot provide detailed information, since
the counterexample information is not available.
