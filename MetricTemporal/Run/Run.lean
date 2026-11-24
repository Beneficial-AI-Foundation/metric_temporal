/-!
# Finite timed runs

Time is `Int`. LeanAID uses epoch milliseconds. Let `ε` be an event type.

- `Step ε`: an ordered list of events at one time. `Run ε`: a finite list of steps.
- `Increasing r`: the step times of `r` increase strictly.
- `upTo r t`: the steps at or before `t`. `before r t`: the steps strictly before `t`.
- `stateAt init upd r t`: the fold of `upd` over `upTo r t`, from `init`.
- `upTo_split`: on an increasing run, for `t ≤ k`, `upTo r k` is `upTo r t` followed by the
  steps in `(t, k]`.
- `upTo_take`: on an increasing run, `upTo r k` is a prefix `r.take n`.

From `LeanAID/Time/Run.lean` and `LeanAID/Time/Pump.lean`.
-/

namespace MetricTemporal

/-- One step of a run: an ordered list of events at one time. -/
structure Step (ε : Type) where
  /-- the time of the step -/
  time : Int
  /-- the events, in order -/
  events : List ε
  deriving Repr

/-- A run: a finite list of steps. -/
abbrev Run (ε : Type) := List (Step ε)

variable {ε σ : Type}

/-- Step times increase strictly. -/
def Increasing (r : Run ε) : Prop := r.Pairwise (fun a b => a.time < b.time)

/-- The steps at or before time `t`. On an increasing run this is a prefix. -/
def upTo (r : Run ε) (t : Int) : Run ε := r.filter (fun s => decide (s.time ≤ t))

/-- The steps strictly before time `t`. -/
def before (r : Run ε) (t : Int) : Run ε := r.filter (fun s => decide (s.time < t))

/-- The state after the steps at or before `t`, from an initial state and a step
    function. -/
def stateAt (init : σ) (upd : σ → Step ε → σ) (r : Run ε) (t : Int) : σ :=
  (upTo r t).foldl upd init

/-- On an increasing run, for `t ≤ k`, the steps up to `k` are the steps up to `t`
    followed by the steps with time in `(t, k]`. -/
theorem upTo_split {r : Run ε} (hinc : Increasing r) {t k : Int} (htk : t ≤ k) :
    upTo r k = upTo r t ++ r.filter (fun s => decide (t < s.time) && decide (s.time ≤ k)) := by
  induction r with
  | nil => rfl
  | cons st rest ih =>
    unfold Increasing at hinc
    rw [List.pairwise_cons] at hinc
    have ih := ih hinc.2
    unfold upTo at ih ⊢
    by_cases h1 : st.time ≤ t
    · simp [h1, show st.time ≤ k by omega, show ¬ t < st.time by omega, ih]
    · have hrest : ∀ x ∈ rest, t < x.time := fun x hx => by have := hinc.1 x hx; omega
      have e1 : rest.filter (fun s => decide (s.time ≤ t)) = [] := by
        rw [List.filter_eq_nil_iff]; intro x hx; have := hrest x hx; simp; omega
      have e2 : rest.filter (fun s => decide (t < s.time) && decide (s.time ≤ k)) =
          rest.filter (fun s => decide (s.time ≤ k)) := by
        apply List.filter_congr; intro x hx; have := hrest x hx; simp; omega
      by_cases h2 : st.time ≤ k
      · simp [h1, h2, show t < st.time by omega, e1, e2]
      · have e3 : rest.filter (fun s => decide (s.time ≤ k)) = [] := by
          rw [List.filter_eq_nil_iff]; intro x hx; have := hinc.1 x hx; simp; omega
        simp [h1, h2, e1, e3]
        intro x hx _; have := hinc.1 x hx; omega

/-- On an increasing run, the steps up to `k` are a prefix of the run. -/
theorem upTo_take {r : Run ε} (hinc : Increasing r) (k : Int) : ∃ n, upTo r k = r.take n := by
  induction r with
  | nil => exact ⟨0, rfl⟩
  | cons st rest ih =>
    unfold Increasing at hinc
    rw [List.pairwise_cons] at hinc
    obtain ⟨n, hn⟩ := ih hinc.2
    unfold upTo at hn ⊢
    by_cases h : st.time ≤ k
    · exact ⟨n + 1, by simp [h, hn]⟩
    · refine ⟨0, ?_⟩
      have : rest.filter (fun s => decide (s.time ≤ k)) = [] := by
        rw [List.filter_eq_nil_iff]; intro x hx; have := hinc.1 x hx; simp; omega
      simp [h, this]

end MetricTemporal
