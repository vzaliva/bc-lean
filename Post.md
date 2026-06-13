# Extracting a Formal Semantics with AI Agents

When we talk about formal verification of programs, one of the first questions
is: does the programming language we are verifying have a formal semantics? If
the language behaviour is specified only by an implementation or by prose
written for humans, then formal reasoning about programs in that language is
impossible without first formalising the language itself.

Many programming languages either lack a formal semantics, or have one that was
developed separately from the implementation. Even when such a semantics exists,
it may cover only part of the language or lag behind the current implementation.

Recently, while attending [FMxAI'26](https://fmxai.org/), I joined a breakout
session titled "How to handle all other languages?". We discussed the idea of
autoformalising semantics from standards documents, implementation source code,
and differential testing against real compilers and interpreters. I prefer the
term "semantics extraction": the goal is not to invent a new semantics, but to
recover the one already implicit in the implementation and its test suite.

I decided to test the idea on a small but real language: the Unix `bc(1)`
calculator. It is compact enough for an experiment, but it is not a toy. It has
arithmetic expressions, mutable variables and arrays, loops, conditionals,
functions, recursion, special variables such as `scale`, `ibase`, and `obase`,
and arbitrary-precision decimal arithmetic. It also has some interesting
language quirks, such as the unusual handling of `quit`, and numeric literals
whose interpretation depends on the current `ibase`.

The resulting project is [bc-lean](https://github.com/vzaliva/bc-lean): an
experiment in AI-assisted semantics extraction for the POSIX subset of `bc`,
checked against GNU bc 1.07.1 and formalised in Lean 4.

## The Experiment Setup

I set up the experiment so that AI agents would do as much of the engineering
work as possible, with limited human guidance. Across the project I used several
models and agent environments, including Cursor Composer 2.5, Claude Opus 4.8,
and Codex/GPT-5.5.

The agents were allowed to inspect the GNU bc 1.07.1 source tree, especially the
parser and execution engine, and to run a local GNU bc binary as a reference
implementation. They also used test programs from GNU bc and a curated
BSD-2-Clause subset of Gavin Howard's bc tests for validation.

The target was an executable formal model in Lean 4: a parser, an abstract
syntax tree, two operational semantics, tests against the reference
implementation, and some metatheory about the semantics themselves.

## What Was Built

The repository now contains:

1. A standalone tree-sitter parser for POSIX `bc` syntax.
2. A Lean surface AST and a tree-sitter XML bridge.
3. A big-step executable semantics.
4. A structural small-step executable semantics.
5. Shared runtime support.
6. A command-line interpreter, `bc-lean`, which can run either semantics.
7. Regression tests comparing both Lean evaluators with GNU bc.
8. A progress theorem for the small-step semantics.
9. A big-step/small-step equivalence theorem.

The project includes a syntax-only parser, but not a typechecker or diagnostics
layer. This matches the scope of the experiment: `bc` is an untyped calculator
language, and GNU bc's warning modes are a separate concern. The current scope
is the POSIX/standard subset, with GNU bc 1.07.1 used as the behavioural
reference.

## Current Status

At the current checkpoint, the project builds with no `sorry` in the proof
surface. The latest documented verification run reports:

- AST golden tests: 40/40 passing.
- Big-step evaluator tests: 39/39 matching GNU bc.
- Small-step evaluator tests: 39/39 matching GNU bc.
- `lake build` green across the Lean tree.

The main proved results are:

- `Bc.Progress.progress`: every small-step configuration is either terminal
  or can take a step.
- `Bc.BigSmall.runProgram_iff`: the big-step and small-step semantics agree on
  final results for ordinary program runs.
- `Bc.BigSmall.runProgramWithState_iff`: the same equivalence for custom initial
  states whose `stopped` flag is false.

This should still be read as an experiment rather than a finished, audited
formalisation. The code and proofs have not yet received enough independent
human review to treat the model as authoritative.

## Effort

Development effort was non-linear. The initial syntax work was surprisingly
quick: the first tree-sitter parser was extracted in well under an hour from the
GNU bc yacc/lex sources, then connected to a Lean AST and golden tests in
another short session. However, independent review by a different agent/model
found real issues: associativity mistakes, over-permissive grammar cases, string
handling bugs, and some confusion about which checks belonged in syntax rather
than later semantics. This was a useful pattern for the whole project:
generation was fast, but review and boundary-setting mattered.

The big-step semantics was relatively straightforward. Once the parser and AST
were stable, the agent could read GNU bc's execution engine, implement an
executable Lean evaluator, and validate it against GNU bc. This still required
careful modelling of decimal arithmetic, functions, arrays, special variables,
and output formatting, but it followed the natural recursive structure of the
language. In terms of independent agent work, this was one of the smoother parts
of the experiment.

The small-step semantics was where human intervention mattered most. The first
version worked as an executable interpreter, but it was not really the
structural small-step semantics we wanted: it shared too much structure with the
big-step evaluator, and some evaluation was effectively big-step work hidden
inside a single small-step transition. We had to split the common runtime layer
out, make big-step and small-step independent siblings, and start over with a
structural residual semantics. Several of the most important improvements came
from human review asking for the right semantic shape, not from simply asking the
agent to keep coding.

The proof work was mostly automatic in the sense that agents did the detailed
Lean engineering: generating auxiliary lemmas, repairing proof scripts, and
iterating until `lake build` was clean. The progress theorem had to be
corrected: the first attempt proved a property of the fuel-bounded runner, not
the intended fuel-free one-step semantics. The big-step/small-step equivalence
also had to be stated at the final `RunResult` level, where the two semantics
may use different fuel measures. The final equivalence proof took the largest
proof engineering effort, with forward and backward simulations, residual-term
evaluation, fuel monotonicity lemmas, and determinism arguments, but it was
ultimately completed by the agent without `sorry` or custom axioms.

## Summary

I think the experiment was a success. In two days of mostly agent work, with
perhaps two hours of human supervision, we extracted a formal semantics for an
existing language from reference implementations, unit tests, and documentation.
Doing this manually would certainly have taken me much longer. However, the
correctness of the result remains an open question until it receives further
human review.
