import MetricTemporal.Tick.Machine

/-!
# Values of past ticks

The documents define the same few observers of the past again and again. This module
gives them in general form.

- `scan a F tr`: a value defined by recursion over the trace. It is `a` before tick 0,
  and the value before tick `t + 1` is `F` of the value before tick `t` and the state
  at tick `t`.
- `prev init tr`: the state of the previous tick, and `init` before tick 0.
- `prevOf f init tr`: the value of `f` at the previous tick, and `init` before tick 0.
- `hold init f tr`: the last value of the optional field `f`, held until the next
  value. It is `init` before the first value.
- `TProp.heldFor φ n`: at tick `t`, `φ` held at each of the `n` ticks before `t`, and
  `n ≤ t`.
- `TProp.heldForExactly φ n`: `heldFor φ n`, and the streak is maximal: `φ` did not
  hold at the tick before the streak, or the streak starts at tick 0.

Theorems:

- `prev_zero`, `prev_succ`, `prevOf_zero`, `prevOf_succ`, `hold_zero`, `hold_succ`:
  the equations of the definitions.
- `heldFor_iff_historicallyIn`: `heldFor φ n` is `n ≤ t` and `H[1,n] φ`.
- `Machine.scan_eq`, the observer lemma: let a field `g` of the machine state start
  with `a` and follow the step `F`. Then `scan a F tr` equals `g` of the state before
  each tick.
- `Machine.prevOf_eq` and `Machine.prevOf_trace`: the same for `prevOf`.
-/

namespace MetricTemporal

variable {σ α : Type}

/-- A value defined by recursion over the trace: `a` before tick 0, and
`F (scan a F tr t) (tr t)` before tick `t + 1`. -/
def scan (a : α) (F : α → σ → α) (tr : Trace σ) : Nat → α
  | 0 => a
  | t + 1 => F (scan a F tr t) (tr t)

/-- The state of the previous tick. Before tick 0 it is `init`. -/
def prev (init : σ) (tr : Trace σ) : Nat → σ := scan init (fun _ s => s) tr

/-- The value of `f` at the previous tick. Before tick 0 it is `init`. -/
def prevOf (f : σ → α) (init : α) (tr : Trace σ) : Nat → α :=
  prev init (fun s => f (tr s))

/-- The last value of the optional field `f` before tick `t`, held until the next
value. Before the first value it is `init`. -/
def hold (init : α) (f : σ → Option α) (tr : Trace σ) : Nat → α :=
  scan init (fun a s => (f s).getD a) tr

section Equations

variable {a : α} {F : α → σ → α} {tr : Trace σ} {init : σ} {f : σ → α} {i : α}
  {o : σ → Option α} {t : Nat}

@[simp] theorem scan_zero : scan a F tr 0 = a := rfl

@[simp] theorem scan_succ : scan a F tr (t + 1) = F (scan a F tr t) (tr t) := rfl

@[simp] theorem prev_zero : prev init tr 0 = init := rfl

@[simp] theorem prev_succ : prev init tr (t + 1) = tr t := rfl

@[simp] theorem prevOf_zero : prevOf f i tr 0 = i := rfl

@[simp] theorem prevOf_succ : prevOf f i tr (t + 1) = f (tr t) := rfl

@[simp] theorem hold_zero : hold i o tr 0 = i := rfl

theorem hold_succ : hold i o tr (t + 1) = (o (tr t)).getD (hold i o tr t) := rfl

theorem hold_succ_some {v : α} (h : o (tr t) = some v) : hold i o tr (t + 1) = v := by
  simp [hold_succ, h]

theorem hold_succ_none (h : o (tr t) = none) : hold i o tr (t + 1) = hold i o tr t := by
  simp [hold_succ, h]

end Equations

namespace TProp

/-- At tick `t`, `φ` held at each of the `n` ticks before `t`, and the trace is long
enough: `n ≤ t`. Unlike `historicallyIn`, ticks before tick 0 do not count as held. -/
def heldFor (φ : TProp σ) (n : Nat) : TProp σ := fun tr t =>
  n ≤ t ∧ ∀ s, t - n ≤ s → s < t → φ tr s

/-- `heldFor φ n`, and the streak is maximal: it starts at tick 0, or `φ` did not hold
at the tick before it. -/
def heldForExactly (φ : TProp σ) (n : Nat) : TProp σ := fun tr t =>
  heldFor φ n tr t ∧ (n = t ∨ ¬ φ tr (t - n - 1))

theorem heldFor_iff_historicallyIn {φ : TProp σ} {n : Nat} {tr : Trace σ} {t : Nat} :
    heldFor φ n tr t ↔ n ≤ t ∧ historicallyIn 1 n φ tr t := by
  constructor
  · intro ⟨hn, h⟩
    refine ⟨hn, fun d hd1 hd2 _ => h (t - d) (by omega) (by omega)⟩
  · intro ⟨hn, h⟩
    refine ⟨hn, fun s hs1 hs2 => ?_⟩
    have := h (t - s) (by omega) (by omega) (by omega)
    rwa [show t - (t - s) = s by omega] at this

theorem heldFor_zero {φ : TProp σ} {tr : Trace σ} {t : Nat} : heldFor φ 0 tr t :=
  ⟨Nat.zero_le t, fun _ h1 h2 => absurd h2 (by omega)⟩

end TProp

namespace Machine

variable {ι : Type} {τ : Type}

/-- The observer lemma. Let the field `g` of the machine state start with `a` and
follow the step `F` along the trace `tr`. Then the observer `scan a F tr` equals `g` of
the state before each tick. -/
theorem scan_eq (m : Machine ι σ) (inp : Nat → ι) {tr : Trace τ} {g : σ → α} {a : α}
    {F : α → τ → α} (h0 : g m.init = a)
    (hs : ∀ t, g (m.after inp t) = F (g (m.before inp t)) (tr t)) :
    ∀ t, scan a F tr t = g (m.before inp t)
  | 0 => h0.symm
  | t + 1 => by
    show F (scan a F tr t) (tr t) = g (m.after inp t)
    rw [scan_eq m inp h0 hs t, hs t]

/-- The observer lemma for `prevOf`: if `f` of the observed state at tick `t` is `g` of
the state after the activation at tick `t`, and `init` is `g` of the start state, then
`prevOf f init tr` is `g` of the state before each tick. -/
theorem prevOf_eq (m : Machine ι σ) (inp : Nat → ι) {tr : Trace τ} {f : τ → α}
    {g : σ → α} {init : α} (h0 : g m.init = init)
    (hf : ∀ t, f (tr t) = g (m.after inp t)) :
    ∀ t, prevOf f init tr t = g (m.before inp t)
  | 0 => h0.symm
  | t + 1 => hf t

/-- `prevOf_eq` for the observed trace `m.trace inp`. -/
theorem prevOf_trace (m : Machine ι σ) (inp : Nat → ι) (g : σ → α) :
    ∀ t, prevOf (fun o => g o.2) (g m.init) (m.trace inp) t = g (m.before inp t) :=
  prevOf_eq m inp rfl fun _ => rfl

end Machine

end MetricTemporal
