# Metric temporal logics in Lean

A Lean 4 library for timed properties of systems. It gives two models of time and the
link between them:

- Tick traces. A trace gives the observed state at each tick (`Nat → σ`). Timed
  properties use the bounded operators of metric temporal logic (MTL). This model is
  for reference documents, which state requirements in ticks or in open time bounds.
- Timed runs. A run is a finite list of steps with timestamps. This model is for code
  and for logs of real devices.

The tick model starts as a shallow embedding of discrete-time MTL with past operators:
each operator is a Lean function on traces, and its definition is its semantics. It
covers a fragment of MTL: unbounded `always` and `eventually`, bounded always,
eventually and until, and bounded past operators. It has no formula type, no since
operator and no unbounded until. A later stage adds a deep embedding of MFOTL that
follows the Isabelle entry `MFOTL_Monitor`.

Stage 1 is in `MetricTemporal/Tick/`: the tick core of the document repositories, and
the general forms of their helpers (`Past.lean`, `Future.lean`, `Window.lean`).
`MetricTemporal/Examples.lean` proves the helpers of the documents from the general
forms. The plan is in [docs/plan.md](docs/plan.md). The analysis of the time model in LeanAID is in
[docs/leanaid-time.md](docs/leanaid-time.md). The existing work in Isabelle and Lean
is in [docs/related-work.md](docs/related-work.md).

## Users

| Repository | Uses |
|---|---|
| `patients_facing_verif` | Tick traces, for medical device documents |
| `iot_verif` | Tick traces, for IoT protocol documents and standards |
| `LeanAID` | Timed runs, for the oref0 dosing algorithm and its replay logs |

## Build

```bash
lake build
```

```bash
lake env lean scripts/Axioms.lean
```
