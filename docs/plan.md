# Plan: factor the time code out into one library

Status: plan. Nothing in this file is done. Written 2026-11-23.

## 1. Goal

Three repositories of the Beneficial AI Foundation state and prove timed properties:

- `patients_facing_verif` formalizes medical device documents (`DeviceDocs/Time/`).
- `iot_verif` formalizes IoT documents. `IotVerif/Time/` is a copy of the core of
  `patients_facing_verif`.
- `LeanAID` verifies the oref0 dosing algorithm (`LeanAID/Time/`).

This library takes the time code out of the three repositories. Each repository then
imports the library. The library gets its own review, its own findings and its own
releases. It becomes a contribution on its own with two parts: a deep layer for
MFOTL that follows the Isabelle definitions (section 6), and the proved link between
the two models of time (section 7). [related-work.md](related-work.md) lists the
existing work.

The repository is in the GitHub organization `Beneficial-AI-Foundation`. It is private
for now, because the plan describes the three user repositories, which are private.
It becomes public when it has library code and the maintainer has reviewed what the
documents say about the private repositories. Its name is `metric_temporal`, and the Lean library and the namespace are `MetricTemporal`.
"Metric temporal" names the family of logics that contains MTL and MFOTL, so the name
stays true from the first stage to the deep layer. It does not claim a complete
library for either logic. The name does not use `Time` alone, because Lean core has
`Std.Time` (calendar time). On 2026-11-23, no Lean repository on GitHub used the name.

## 2. What exists today

All three repositories use Lean `v4.36.0` and have no dependencies.

### 2.1 Tick traces in the document repositories

`DeviceDocs/Time/` has 159 lines in two files. It was written for the first commit of
`patients_facing_verif` (a60f886, 2026-11-20) and did not change after that.
`IotVerif/Time/` is the same code in the namespace `IotVerif`. Only one comment differs
(the example of a tick length). It also did not change after its first commit
(e4e8814).

- `Trace.lean`: `Trace σ := Nat → σ`, `TProp σ := Trace σ → Nat → Prop`, `Sat`, the
  Boolean connectives, `always` and `eventually`. It also has the bounded operators
  `alwaysIn`, `eventuallyIn`, `untilIn`, `onceIn`, `historicallyIn` and
  `leadsToWithin`. Ten lemmas give monotonicity, the duality of `F[a,b]` and `G[a,b]`,
  and `sat_always`.
- `Machine.lean`: a deterministic machine (`init`, `step`), the states `before` and
  `after` of an activation, the observed `trace`, and the lemma `invariant`.

Users in `patients_facing_verif`: nine files in `DeviceDocs/Example/RegulatorInit/`,
`DeviceDocs/Sr2011/` and `DeviceDocs/BtIds/`. Six import the core, and the three
`Adequacy.lean` files use it through those imports. They refer to `Trace`, `TProp`, `Sat` and
`Machine` without a prefix, because these names are in the parent namespace
`DeviceDocs`.

Users in `iot_verif`: the documents on the branches for `En303645`, `MatterAcl` and
`ZwaveS2Inclusion`. `main` has only the core.

### 2.2 Helpers that each document wrote again

The documents wrote the same few patterns in their own directories. The core did not
have them, and the rules forbid an edit of the core in a document branch.

| Pattern | Instances |
|---|---|
| The value of the previous tick, or a function of it, with a start value | `prevMode` (RegulatorInit), `prevOwed`, `prevTempRate`, `tempCarry` (Sr2011), `prevDev` (BtIds), `prevSt` (MatterAcl) |
| The last value of an optional field, held until the next value | `lastTx` (BtIds) |
| A state defined by recursion over the trace | `lastRx` (BtIds) |
| A condition held for the last `n` ticks, and the trace is long enough | `initFor` (RegulatorInit), `idleFor`, `nonDeliveryRun` (Sr2011) |
| A sum over a window of ticks | `sumRange` and three lemmas (Sr2011) |
| The witness of `untilIn` is unique | `responds_at` (BtIds) |
| A trace observer equals the machine state | `prevOwed_obs`, `prevTempRate_obs` (Sr2011), `rx_inv`, `tx_inv` (BtIds) |

The last row is one lemma in general form. Let an observer be defined by recursion
over the trace, and let a field of the machine state follow the same recursion: the
same start value as the field of `init`, and the same step. Then the observer equals
that field of `before` at each tick.

`docs/method.md` in `patients_facing_verif` lists a set of limits that overlaps with
this table, under "The pilots found these limits of the time core". It does not name
the held value, the recursive observer or the observer lemma. It adds three limits: no
operator for "from the next tick", no conventions for the order of events inside one
tick, and no rational numbers.

### 2.3 Timed runs in LeanAID

See [leanaid-time.md](leanaid-time.md). In short: of about 2,300 lines in
`LeanAID/Time/`, only `Run.lean` (125 lines) is generic. It defines finite runs of
timestamped steps, the state at a time, and a window integral over `Rat`.

## 3. Layout of the library

```
MetricTemporal/Tick/Trace.lean      Trace, TProp, operators, lemmas (from DeviceDocs/Time)
MetricTemporal/Tick/Machine.lean    Machine, before, after, trace, invariant
MetricTemporal/Tick/Past.lean       prev, hold, heldFor, observer lemma
MetricTemporal/Tick/Window.lean     window sums and their lemmas
MetricTemporal/Run/Run.lean         Step, Run, Increasing, stateAt (from LeanAID)
MetricTemporal/Run/Integral.lean    sumFrom, integral over Rat (from LeanAID)
MetricTemporal/Deep/Formula.lean    formula type and sat, after MFOTL_Monitor (section 6)
MetricTemporal/Deep/Eval.lean       eval into the shallow operators, and agreement
MetricTemporal/Export/MonPoly.lean  printer for formulas, signatures and logs
MetricTemporal/Sample.lean          the link between runs and tick traces (section 7)
MetricTemporal/Examples.lean        the instances of section 2.2, proved from the general forms
MetricTemporal.lean                 imports all modules
```

Each module states its definitions and theorems in a header comment. The library has
no `sorry`, no `admit`, no `axiom`, and no Mathlib.

## 4. Stage 1: tick traces, and the two document repositories

### 4.1 The library

1. Create the Lake package: a `lakefile.toml` with the library `MetricTemporal` and
   `defaultTargets = ["MetricTemporal"]`, so that `lake build` builds it, a
   `lean-toolchain` with `leanprover/lean4:v4.36.0`, and the root file
   `MetricTemporal.lean`.
2. Copy `DeviceDocs/Time/Trace.lean` and `Machine.lean` into `MetricTemporal/Tick/`, and
   change the namespace to `MetricTemporal` and the import in `Machine.lean` to
   `MetricTemporal.Tick.Trace`. Keep the names of all definitions and
   lemmas, so that the move changes only imports and `open` lines in the users.
3. Add the patterns of section 2.2 in general form, with the instances as tests:
   - `prev (init : σ) (tr : Trace σ) : Nat → σ`, and `prevOf f init`, the previous
     value of a field.
   - `hold`, the last value of an optional field.
   - `heldFor φ n`: at tick `t`, `φ` held at each of the `n` ticks before `t`, and
     `n ≤ t`. `historicallyIn` does not give this, because it does not count ticks
     before tick 0. At tick `t < n`, it checks only the ticks from 0 to `t`. The three
     instances count differently, and each is `heldFor` at a shifted tick:
     `initFor tr t n` excludes tick `t` and is `heldFor` at `t` with length `n`.
     `idleFor tr t n` includes tick `t` and is `heldFor` at `t + 1` with length
     `n + 1`. `nonDeliveryRun tr t n` is `heldFor` at `t + 1` with length `n`, and it
     also requires that the streak is maximal: tick `t - n` is in run mode, or the
     streak starts at tick 0.
   - `next φ`, "from the next tick".
   - `sumRange` and its lemmas, in `Window.lean`.
   - `untilIn_witness_unique`, the general form of `responds_at`. The witness of
     `untilIn` is not unique in general. It is unique if `ψ` excludes `φ` at each
     tick, as in `responds_at`, where `φ` is "no indication" and `ψ` gives one.
   - The observer lemma of section 2.2.
4. Prove each instance of section 2.2 from the general form, in `Examples.lean`, as a
   check that the general form fits. Each instance is restated there with its device
   type replaced by a small example type.
5. Add CI: `lake build`, a check for `sorry`, `admit` and `axiom`, and a script that
   prints the axioms of the main theorems.
6. Tag the first release `v0.1.0`, and push the tag to
   `Beneficial-AI-Foundation/metric_temporal`. Sections 4.2 and 4.3 fetch the library
   from there. While the repository is private, the CI of each user repository needs
   read access to it, for example a deploy key.

### 4.2 `patients_facing_verif`

1. Add the library to `lakefile.toml`:

   ```toml
   [[require]]
   name = "MetricTemporal"
   git = "https://github.com/Beneficial-AI-Foundation/metric_temporal"
   rev = "v0.1.0"
   ```

   Then run `lake update MetricTemporal`, and commit the new `lake-manifest.json`.
   The manifest of each user repository lists no packages today, and Lake does not
   build a package whose manifest lacks a declared dependency.

2. Delete `DeviceDocs/Time/`. Replace `import DeviceDocs.Time.Trace` and
   `import DeviceDocs.Time.Machine` with the `MetricTemporal` modules in each file that
   has them, `DeviceDocs.lean` included. Add `open MetricTemporal` to each file that
   uses a name of the core without a prefix, also to files that import the core only
   through another file, for example `DeviceDocs/BtIds/Adequacy.lean`.
3. Do not replace the local helpers (`prevMode`, `sumRange` and the others) in this
   step. A replacement changes the definitions that a reviewer checked against the
   source. Each document replaces its helpers in its own pull request, with a proof
   that the old and the new definition agree.
4. `lake build` and `lake env lean scripts/Axioms.lean` must give the same results as
   before. The axioms output of the document theorems must not change. In
   `patients_facing_verif`, `scripts/Axioms.lean` prints only document theorems.
5. Update `docs/method.md` (section "Time model" and the list of limits),
   `CLAUDE.md` (the rule about the time core) and the layout table in `README.md`.
   The new rule: if the library lacks a lemma, add the lemma in the document directory.
   Then open an issue in `metric_temporal`, and name the issue in the pull request.

### 4.3 `iot_verif`

The same steps as 4.2, with `IotVerif` for `DeviceDocs`. One difference:
`scripts/Axioms.lean` of `iot_verif` also prints four declarations of the core
(`Machine.invariant` and three others). These lines move to the axioms script of the
library. If `main` has no document yet, the script then also loses its
`open IotVerif`, because no file declares that namespace any more. The output for the
document theorems must not change. The document branches
(`En303645`, `MatterAcl`, `ZwaveS2Inclusion`) are not merged into `main` yet. Two
orders are possible:

- Change `main` first. Each document branch then rebases and changes its imports.
- Merge the document branches first, then change `main` once.

The second order has fewer conflicts. The maintainer selects one.

## 5. Stage 2: timed runs, and LeanAID

1. Copy the generic part of `LeanAID/Time/Run.lean` into `MetricTemporal/Run/`: `Step`,
   `Run`, `Increasing`, `upTo`, `before`, `stateAt`, `sumFrom`,
   `integral` and their lemmas. Make the time type a parameter or keep `Int`, and make
   `msPerHour` a parameter of `integral` with the hypothesis that it is positive (the
   unit belongs to LeanAID, and the bound and nonnegativity lemmas need the
   hypothesis). Copy the `Rat` lemmas that the moved proofs use from
   `LeanAID/Proofs/Rounding.lean`: `div_le_div_of_le` and `div_nonneg'`, and the two
   lemmas that their proofs use, `div_le_iff_le_mul` and `le_div_iff_mul_le`.
   Also move `upTo_split` and `upTo_take` from `LeanAID/Time/Pump.lean`, stated for
   `Run ε` instead of `Run Event`. `Status` and `stateBefore` have no users in
   LeanAID. Leave them out until a finite run has a stated meaning (section 6, point 5).
   Tag the release `v0.2.0`, and push the tag.
2. In LeanAID, add the library at `v0.2.0` to `lakefile.lean`, run `lake update MetricTemporal`,
   commit the new `lake-manifest.json`, delete the moved definitions from
   `Run.lean`, and let `Run.lean` define only the unit (`msPerHour`) and the
   specialized names. No theorem statement in LeanAID changes in this stage.
3. `lake build` in LeanAID must succeed, and the replay and conformance tests must give
   the same results.

Section 4 of [leanaid-time.md](leanaid-time.md) lists open questions for further work
in LeanAID. That work is not part of stage 2. Stage 2 moves code and changes no
statement.

The runs of LeanAID do not fit `Trace σ := Nat → σ`. Their times are irregular, they
are finite, and the pump rate is a function of each millisecond. So the library has
two models side by side in stage 2, and stage 4 connects them.

## 6. Stage 3: notation and a deep layer

The tick core is a shallow embedding: each operator is a Lean function, and its
definition is its semantics. It has no formula type. So it cannot state a theorem
about all formulas, for example the correctness of a monitor or of a translation. The
document requirements also go beyond MTL. `BtIds` quantifies over writes, which is
first-order. Atoms such as `prevDev` and `lastRx` depend on the past, and `Sr2011` sums
over windows. The shallow layer stays the reference semantics for these requirements.

1. Notation. Add notation such as `G[a,b] φ` and `φ U[a,b] ψ` for the shallow
   operators. The proofs do not change.
2. A deep layer for MFOTL. Copy the formula type, the intervals and the semantics
   `sat` of the AFP entry `MFOTL_Monitor` (section 2.2 of
   [related-work.md](related-work.md)), so that a reviewer can compare the two
   definitions one clause at a time. Variables use de Bruijn indices, as in that
   entry. Define `eval` from a formula and a variable assignment to a `TProp`, as `sat` takes
   an environment. Prove that `eval` agrees with the shallow operators for bounds with
   `a ≤ b`. The theorem needs an encoding of a tick state as a set of events, because a
   predicate of `sat` tests whether an event is in the set at the current point. An interval of the AFP entry is never empty, but `alwaysIn 1 0 φ` is true
   for each `φ`. So the agreement theorem has the hypothesis `a ≤ b`, or the
   translation states what an empty interval becomes. A tick trace is the case in which the time stamp of point `i`
   is `i`.
3. Aggregation and `LET`, as in `MFODL_Monitor_Optimized` and VeriMon 2.0, are a later
   step. The window sums of `Sr2011` and P6 of LeanAID need aggregation. `LET` binds
   a named predicate, and derived state such as `lastRx` can need it.
4. Export. Print a formula, a signature and a log in the format of MonPoly, and monitor
   the replays of LeanAID with VeriMon 2.0. The printer emits only a fragment that
   VeriMon accepts. VeriMon 2.0 accepts more than the AFP entry
   `MFODL_Monitor_Optimized` defines, for example `LETPAST`, so the fragment is
   checked against the tool. The printer
   and the conversion of time stamps are trusted. VeriMon gives verdicts, not Lean
   proofs.
5. Finite traces. Open question: which semantics does the library give to a finite
   trace? Section 4, question 4 of [leanaid-time.md](leanaid-time.md) lists the
   options, and MLTL (section 2.1 of [related-work.md](related-work.md)) is one of
   them.

A Lean port of the verified monitor of VeriMon is not part of this plan. It is large,
and the Isabelle tool exists. A port becomes useful only if a Lean proof needs the
verdict of a monitor.

## 7. Stage 4: the link between the two models

This stage is research. Nothing in it is designed in detail or tested.

A tick trace can sample a timed run: given a tick length `δ`, each tick gets a state
of the run. The open questions are:

- What does a tick record: the state at its end, or also the events inside it? A
  state at the end of a tick can lose a change that lasts less than one tick.
- For which properties does a property of the run carry over to the sampled trace,
  and with which bound on the time? Bounded response is the first candidate. Its
  conditions are open.
- Which properties do not carry over? Two events in one tick have no order unless a
  convention gives one. `BtIds` in `patients_facing_verif` puts the write before the
  indication, and its `docs/method.md` records that a protocol needs such conventions.
- Can a document result then apply to code? A requirement of a document is a property
  of tick traces. A theorem about the code is a property of runs. A sampling theorem
  can connect the two, if the questions above have answers.

The first deliverable of the stage is a design note in this repository, with the
definitions of `sample` and one proved instance (bounded response). The design note
also decides whether the library needs finite tick traces, or only infinite tick
traces and finite runs.

## 8. Releases and review

- The library has releases with tags `v0.x.y`. Each user pins one tag in its Lake
  file. A user updates the tag in its own pull request.
- A change that renames or removes a definition is a new minor version, and the
  release notes list the change.
- The Lean toolchain of the library and of all users is the same. A toolchain update
  starts in the library.
- Each stage is one pull request in this repository, and one in each user that the
  stage changes. The review
  of the library is separate from the review of the documents. Its questions: Is each
  operator the standard one of MTL, or is the difference stated? Does each general
  definition give the instances of section 2.2? Is each theorem what its name says?

## 9. Decisions for the maintainer

1. The order for `iot_verif` (section 4.3).
2. The time type of runs: `Int` milliseconds as in LeanAID, or a type parameter.
3. Whether stages 3 and 4 start before stage 2 is complete.
4. Whether the library also gives finite tick traces (section 7), and whether a closed
   run ends or repeats its last state (section 6, point 5).
5. Which questions of section 4 of [leanaid-time.md](leanaid-time.md) LeanAID takes
   up, and in which order.
