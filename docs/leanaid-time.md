# Time in LeanAID: analysis and questions

Status: analysis of LeanAID at commit 9632f00, read on 2026-11-23. Sections 1 to 3
state what the repository has. Each exact statement is in the file that the text names,
and this document does not repeat the hypotheses. Section 4 is a list of open
questions, not a design. Paths are relative to the LeanAID repository.

## 1. The time model

- Time is `Int` epoch milliseconds (`LeanAID/Time/Run.lean`). Rates are `Rat` in U/h.
  UPPAAL models use seconds.
- A run is a finite list of steps, and a step is a time and a list of events (`Step`,
  `Run` in `Run.lean`). `stateAt` folds an update function over the steps up to a
  time.
- `rateAt` (`LeanAID/Time/System.lean`) is the pump rate at each millisecond, also
  after the last step. It can change without an event, for example at the deadline of
  a temp basal.
- `Legal` (`System.lean`) is the predicate for the runs that most theorems assume.
  Some theorems, such as `p4a_expiry`, need `Increasing` and their own hypotheses,
  but not `Legal`.
  `Legal.cycle` gives the conditions of each cycle.
- `integral` (`Run.lean`) sums a rate in U/h over the milliseconds of a window and
  divides by `msPerHour`, so the result is in units of insulin. The sum is exact.

## 2. How the timed properties are stated

LeanAID defines no temporal operator. Each timed property states its own quantifiers
over the cycles of a run or over milliseconds. The proved parts of the timed properties P1
to P6 are in five files. `Lift.lean` has `p1_faithful`, `p1_derived`, `p2_rate_bound`
and `p5_faithful`. `Duration.lean` has `p3_temp_ok`. `Pump.lean` has `p4a_expiry`,
`temp_bound` and `p4b_fail_safe`. `Delivery.lean` has `rate_envelope` and `p6_basal`.
`SmbSpacing.lean` has `smb_spacing`, a part of P5 about one cycle and its bolus
history. `docs/mtl-catalog.md`
gives the intended MTL reading of each property, in prose.

`docs/LOG.md` and `docs/FINDINGS.md` list the timed properties that are not proved, with
the reasons.

## 3. Why time in LeanAID looks ad hoc

`docs/timing-plan.md` chose to add a general tool only for a theorem that needs it,
and to postpone a formula type. The repository followed that choice. The result:

1. No operator layer. No lemma about operators can be shared between properties.
2. One proof pattern twice. `inv_take` (`Pump.lean`) and `invRate_take`
   (`Delivery.lean`) both prove an invariant of the fold over a prefix of the run, by
   induction. Their callers then use `upTo_take` and `Increasing` to get an invariant
   of `stateAt`.
3. General lemmas in specific files. `upTo_split` and `upTo_take` (`Pump.lean`) are
   about runs in general, but they are typed for `Run Event`.
4. Units as inline constants. Most conversions between milliseconds, minutes and
   hours are literals such as `60000`. `msPerHour` (`Run.lean`) is one of the few
   named constants.
5. The meaning of finite runs only in prose. `docs/mtl-catalog.md` states how closed
   and observed runs decide an obligation. No Lean definition uses it: `Status` and
   `stateBefore` (`Run.lean`) have no users.

The theorems are proved, and LeanAID's documents record each limit. The cost appears
in two cases: a new property needs the same work again, or a result must transfer to
UPPAAL or to a document.

LeanAID also does several things well. It has one explicit transition system, and
`Legal.cycle` makes the lift of a per-call theorem to a run short. The integral is
exact. The documents record each item that is not proved, with its reason.

## 4. Open questions for a formal time layer

These questions build on the library of [plan.md](plan.md). None of them is answered.

1. Can one lemma replace `inv_take` and `invRate_take`? The two differ in the
   premises for each step, and the premises of `invRate_take` refer to the state
   just before each cycle, after the earlier events of the same step. The general lemma must allow that.
2. Can the timed properties be stated with operators of the library? `docs/mtl-catalog.md`
   names two semantics, over a sequence of timed states and over a function of time.
   Which properties need which semantics, and what links the two?
3. For which properties does the operator form follow from the existing theorem, so
   that the old proof stays? `p1_derived` is an example where it does not follow
   directly: it bounds the age of a reported date, not of a reading event.
4. Which Lean semantics does the library give to a finite run? `docs/mtl-catalog.md`
   gives LeanAID's meaning in prose. A semantics for the library can let a closed run
   end, or repeat its last state, and the two give different verdicts. An observed run needs a semantics over its
   extensions, or three truth values. The choice is open (section 9 of
   [plan.md](plan.md)).
5. Can sums over windows be checked at finitely many points? Task T7 of
   `docs/timing-plan.md` plans a window reduction lemma. Which horizon and which
   facts about the basal schedule does a statement over all times need?
6. Named units, with lemmas that the conversions are exact.
7. How does the sampling of stage 4 in [plan.md](plan.md) relate the millisecond view
   of LeanAID to the minute and second views of oref0 and UPPAAL?
8. The refinement to UPPAAL is level 3 in `docs/uppaal-plan.md`, section 7. It is the
   largest step.

A possible order: question 1 first, because it removes a duplicate proof with little
risk. Then questions 2, 3 and 6. Questions 4, 5, 7 and 8 are research.
