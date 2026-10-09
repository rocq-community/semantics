<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Semantics

[![Docker CI][docker-action-shield]][docker-action-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]
[![DOI][doi-shield]][doi-link]

[docker-action-shield]: https://github.com/rocq-community/semantics/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/rocq-community/semantics/actions/workflows/docker-action.yml

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users


[doi-shield]: https://zenodo.org/badge/DOI/10.1017/CBO9780511770524.016.svg
[doi-link]: https://doi.org/10.1017/CBO9780511770524.016

This is a survey of programming language semantics styles
for a miniature example of a programming language, with their encoding
in Rocq (Coq), the proofs of equivalence of different styles, and the proof
of soundess of tools obtained from axiomatic semantics or abstract
interpretation.  The tools can be run inside Rocq, thus making them
available for proof by reflection, and the code can also be extracted
and connected to a yacc-based parser, thanks to the use of a functor
parameterized by a module type of strings.  A hand-written parser is
also provided in Rocq, but there are no proofs associated.

The current version is only compatible with a recent version of Rocq
(tested with versions 9.0 to 9.1) but previous versions of this repository
worked with older version of Rocq and Coq


## Meta

- Author(s):
  - Yves Bertot (initial)
- Rocq-community maintainer(s):
  - Yves Bertot ([**@ybertot**](https://github.com/ybertot))
- License: [MIT License](LICENSE)
- Compatible Rocq/Coq versions: 9.0 or later
- Additional dependencies:
  - [rocq-stdlib] (https://github.com/rocq-prover/stdlib)
  - [ocamlbuild](https://github.com/ocaml/ocamlbuild)
- Rocq/Coq namespace: `Semantics`
- Related publication(s):
  - [Theorem proving support in programming language semantics](https://hal.inria.fr/inria-00160309) doi:[10.1017/CBO9780511770524.016](https://doi.org/10.1017/CBO9780511770524.016)

## Building and installation instructions

The easiest way to install the latest released version of Semantics
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install rocq-semantics
```

To instead build and install manually, you need to make sure that all the
libraries this development depends on are installed.  The easiest way to do that
is still to rely on opam:

``` shell
git clone https://github.com/rocq-community/semantics.git
cd semantics
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install --deps-only .
make   # or make -j <number-of-cores-on-your-machine> 
make install
```


## Description
These files describe several approaches to the description of a simple
programming language using the Rocq (formerly Coq) system.

`syntax.v` the constructs of the language

`little.v` operational semantics in three forms: natural semantics (also know
  as big-step semantics), structural operational semantics (small-step
  semantics), and a functional implementation of the latter.  This file
  also contains the proof that the three point descriptions are equivalent.

`function_cpo.v`  A description of partial functions and Tarski's fixpoint theorem.

`constructs.v`  A proof that the constructs of the programming language are
  continuous, with respect to the notion of continuity given in function_cpo

`denot.v` A description of the programming language in the style of denotational
  semantics.  This file also contains the proof that denotational semantics
  and natural semantics are equivalent.

`axiom.v` Hoare triples and Dijkstra's weakest pre-condition calculus, in the form
  of a verification condition generator.  This   file also contains a proof that
  the axiomatic semantics (base on Hoare triples) and the vcg are sound with
  respect to the natural semantics.

`intervals.v` A notion of intervals to be used in an abstract interpreter.
  A type of extended integers is defined to incorporate infinities (minfty
  and pinfty) and intervals are defined as pairs of extended integers
  (this accepts the meaningless intervals of the form (minfty, minfty), but
  they do not cause any problem).  Different forms additions and comparisons
  are defined for extended integers and intervals.

`abstract_i.v`  An abstract interpreter defined as a parameterized module over
  a notion of abstract domain.  This abstract interpreter is instantiated
  with the intervals defined above.

`little_w_string.v`  The whole development is defined as a set of modules
  parameterized by a notion of strings.  This file instantiate the development
  on the string package provided in Rocq.

`parser.v` A parser for the language and assertions, which can be hooked on all
  the tools.  This is nice for the examples.  There are no proofs on this
  parser, and when parsing fails, it simply returns the "skip" program.

`example.v`, `example2.v`, `ex_i.v`  These are examples where the interpreter,  the abstract interpreter,
  and the vcg are used in a reflective manner directly inside Rocq.

 To execute little programs inside Rocq, you should parse them using the
 function `parse_instr'` and then remove the annotations using the function
 `un_annot`. Beware that programs containg syntax errors will
 silently be parsed to `skip`.  Then there are three ways to execute the
 program.
 - The function `f_star` can be used with a numeric argument which limits the
 number of elementary steps of execution that can be performed.  This is
 convenient only for small execution attempts, because the number of steps
 is represented as a natural number an only small natural numbers can be
 used.  This is proved correct in file `little.v`
 - The function `ds_abstract` can be used with `Tarski_fix_z` and a numeric
 argument that limits the number of times each loop can be unrolled.  This
 is proved correct in file `denot.v` (only partially, because the proof
 that `Tarski_fix_z n` and `Tarski_fix` are functionally equivalent has not
 been formally verified.  This mode of execution is fragile because the
 resulting term is overwhelmingly large when the numeric oargument provided
 is too small for execution to complete.
 - The function `ds_abstract` can be used with `limited_unroll` and a numeric
 argument.  Here again, the numeric argument limits the number of times
 each loop can be unrolled.  Execution with this technique have not been
 proved correct yet.  This is the most practical: when the limit is too small,
 the result is simply `None`.  When the limit is large enough, and there is
 no other execution error (which may happen when the environment does not
 contain initial values for some of the program variables), the result is
 `Some l` where `l` is a list of bindings describing the final value of all
 program variables.

`extract_interpret.v`  This file contains the directives to extract code from
  the proved tools.

`asm.v`  This file contains the description of a simple assembly language and
  a compiler from the little language to this assembly language.  The machine
  modeled in this assembly language is a stack machine with a random access
  memory, both modeled as lists of integers.  This assembly
  language has an unconditional branching instruction `goto`, and a conditional
  branching instruction `branch`, which interprets the top value of the stack
  as a boolean value, through the coercion from `Z` to `bool` given by
  `Z.b2z`.  If the top value is `Z.b2z true`, then branching at the prescribed
  address occurs, otherwise control flow passes to the next instruction in the
  program.  The compiler comes with a partial proof of correctness, expressing
  that when an instruction executes and terminates, the compiled expression
  can also be executed in a memory faithful to the environment, and execution
  proceeds until the program counter reaches the end of the compiled expression.

This development also comes with ml files used to encapsulate the extracted
code.

`str_little.ml`  A definition of the module of strings as needed for the
  extracted code, but this module is based on ocaml native strings.

`parse_little.mly` A parser description using the yacc extension of ocaml
llex.mll the lexical analyser to be used with the parser.

`little.ml` basic encapsulation: a single command is generated, with four
  options:
  - `-interpreter` (just to execute a program)
  - `-vcg` (to generate the conditions for the verification of an annotated program)
  - `-vcg-rocq` (to generate the conditions in rocq syntax)
  - `-static-analysis` (to run the abstract interpreter).

