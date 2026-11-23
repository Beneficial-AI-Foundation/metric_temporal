# Related work

Status: read on 2026-11-23 from the pages that each entry links. The content of each
entry is as its page states it. A point that the page does not state is marked "not
checked".

## 1. The logics

- MTL (metric temporal logic) adds time intervals to the operators of LTL.
- MFOTL (metric first-order temporal logic) adds data to MTL. At each time point, the
  state is a set of events with arguments, and formulas can quantify over the
  arguments. MTL is the case with no arguments and no quantifiers.
- MFODL (metric first-order dynamic logic) adds regular expressions to MFOTL.
- MLTL (mission-time LTL) is LTL with bounded integer intervals over finite traces.
  It is close to bounded discrete-time MTL, but its until differs. In the AFP entry,
  `φ U[a,b] ψ` requires `φ` only from offset `a` up to the witness. The `untilIn` of
  the tick core requires `φ` from offset 0. For example, on a trace where only `q`
  holds, at tick 1, MLTL gives `p U[1,1] q` and `untilIn 1 1 p q` does not hold.

## 2. Isabelle/HOL

All four entries below are deep embeddings: a datatype of formulas and a satisfaction
function.

### 2.1 Mission-time Linear Temporal Logic

[AFP entry](https://www.isa-afp.org/entries/Mission_Time_LTL.html). Kosaian, Wang,
Sloan, 2025-01-24.

- Constructors: true, false, propositions, negation, conjunction, disjunction, and
  bounded F, G, U and R (release) with bounds `[a, b]`.
- Traces are finite lists of sets of propositions. The semantics is
  `semantics_mltl`, written `π ⊨ φ`.
- Results: equivalences (De Morgan, dualities of F and G and of U and R,
  distributivity) and a negation normal form that keeps the semantics for well-formed intervals
  (`a ≤ b`).
- Later entries use it: a translation to regular expressions, language partitioning,
  and formula progression.

### 2.2 MFOTL_Monitor

[AFP entry](https://www.isa-afp.org/entries/MFOTL_Monitor.html). Schneider, Traytel,
2019-07-04.

- Formula datatype: `Pred`, `Eq`, `Neg`, `Or`, `Exists`, `Prev I`, `Next I`,
  `Since φ I ψ`, `Until φ I ψ`. The semantics is
  `sat :: 'a trace ⇒ 'a env ⇒ nat ⇒ 'a formula ⇒ bool`.
- An interval is a pair `(i : nat, j : enat)` with `i ≤ j`. The upper bound can be
  infinite.
- A trace is an infinite stream of pairs (set of events, time stamp). The time stamps
  are natural numbers. They never decrease (`ssorted`), and they are unbounded
  (`sincreasing`). Two events can have the same time stamp.
- The monitorable formulas are the safe formulas (`safe_formula`) with a finite
  future reach. The monitor is executable and verified against `sat`. The exact
  correctness theorem is not checked.

### 2.3 MFODL_Monitor_Optimized

[AFP entry](https://www.isa-afp.org/entries/MFODL_Monitor_Optimized.html). Dardinier,
Heimes, Raszyk, Schneider, Traytel, 2020-04-09. It extends 2.2 with regular expressions
and aggregations (count, sum, median and others), multi-way joins and a sliding-window
algorithm.

### 2.4 MFOTL_Checker

[AFP entry](https://www.isa-afp.org/entries/MFOTL_Checker.html). Herasimau, Huerta y
Munive, Lima, Raszyk, Traytel, 2024-04-16. A verified checker for the proof trees that
the unverified monitor WhyMon gives as explanations of its verdicts. A 2025 update adds
regular expressions.

## 3. Tools

- [MonPoly](https://bitbucket.org/monpoly/monpoly/) is the unverified MFOTL monitor. It
  reads three files: a signature (`publish(x:int)`), a formula, and a log of
  time-stamped events (`@10 publish(1) approve(2)`).
- [VeriMon 2.0](https://github.com/dtraytel/verimon) reads a restricted variant of the
  formats of MonPoly. Its parser and CLI documents list the differences. It
  supports MFODL with comparisons, arithmetic and regular expressions. It also has
  aggregations (`CNT`, `SUM`, `AVG`, `MIN`, `MAX`, `MED`) and `LET` and `LETPAST`
  definitions. Its
  README says that future intervals must be bounded. In `MFODL_Monitor_Optimized`, a monitorable
  formula bounds the interval of `Until` and of a future match, and allows an unbounded
  `Next`. `MFOTL_Monitor` also bounds `Next`. The parsers, the type check, the formula preparation and
  the monitor are verified in Isabelle/HOL. A small OCaml driver and the code generator
  are trusted. License LGPL 2.1 with a linking exception. VeriMon 1, a mode of MonPoly
  (`monpoly -verified`), used the unverified front end of MonPoly. The papers on
  VeriMon 1 describe that version.
- WhyMon gives explanations of its verdicts as proof trees. 2.4 checks them.

## 4. Lean 4

No reusable Lean 4 library for MTL or MFOTL was found. Two paper artifacts formalize
metric temporal logics in Lean 4:

- [policy-change-lean](https://github.com/francois-hublet/policy-change-lean)
  (Hublet, created 2026-11-10): the Lean formalization of the paper "Policy change for
  treelike monitors". Its `PolicyChange/Spec.lean` defines past-time MTL (pMTL) and its
  semantics over real and discrete time, and online monitors. Its README states that
  all statements are proved, with no `sorry`. It uses Lean v4.31.0 and Mathlib, and the
  repository names no license. It is an artifact for one paper, not a library.
- [EnfFlash](https://github.com/runtime-enforcement/EnfFlash) (created 2026-10-01,
  LGPL-3.0): an enforcement tool for MFOTL policies, with a compiler in OCaml and
  an enforcement engine in Rust. Its `lean/`
  directory is a Lean 4 formalization of the compilation from MFOTL and its
  correctness, for the paper [arXiv 2610.04611](https://arxiv.org/abs/2610.04611). It
  uses Lean v4.31.0 and Mathlib. Which fragment of MFOTL it covers is not checked.

The other Lean work found is about LTL:

- [LeanLTL](https://github.com/UCSCFormalMethods/LeanLTL) (Vin, Miller, Fremont, ITP
  2025, [arXiv 2507.01780](https://arxiv.org/abs/2507.01780)): LTL over finite and
  infinite traces, with LTL syntax mixed with Lean expressions, and tactics. Its file
  list shows LTL and LTLf. Metric and past operators are not mentioned. It depends on
  Mathlib. Its `lean-toolchain` on `main` names `v4.17.0-rc1`, and the last commit is
  from 2026-10-21. BSD-3-Clause.
- [LeanearTemporalLogic](https://github.com/mrigankpawagi/LeanearTemporalLogic): LTL
  syntax, semantics and transition systems, after Baier and Katoen.

On 2026-11-19, `docs/timing-plan.md` in LeanAID found no Lean 4 MTL or MLTL library
that suits that project. It did not search for MFOTL.

## 5. What this means for the library

- The tick core of this library is a shallow embedding of a fragment of
  discrete-time MTL with past operators. The formula type of 2.2 also has
  `Prev`, `Next` and `Since` with intervals, which the tick core lacks. Stage 1 of the
  plan adds a tick `next` without an interval. The intervals of 2.2 can have an
  infinite upper bound, and the formulas have first-order data. A tick trace is the special case of a trace of 2.2 in which the
  time stamp of point `i` is `i`.
- A deep layer that copies the formula type and `sat` of 2.2 can be compared with the
  Isabelle definitions one clause at a time.
- A monitorable formula of the deep layer can be printed in the format of MonPoly.
  Each monitor entry (2.2 and 2.3) defines which formulas it can monitor, and the
  two definitions differ, for example for `Next`. Then VeriMon 2.0 can monitor the logs and the
  replays of LeanAID. The printer and the conversion of
  time stamps are trusted. The time stamps of VeriMon in its example are seconds, and
  LeanAID uses milliseconds.
- LeanLTL is the nearest Lean library. It does not cover metric or past operators, and
  it depends on Mathlib. Its approach is a mixed form, with syntax and Lean expressions
  together. Whether that form can carry metric operators is not checked.
- policy-change-lean has past-time MTL as a formula datatype (`PMTL` in
  `PolicyChange/Spec.lean`), and EnfFlash formalizes a part of MFOTL. Both are paper
  artifacts with Mathlib. Their definitions are references for the deep layer, next to
  the AFP entries.
