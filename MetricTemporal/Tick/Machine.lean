import MetricTemporal.Tick.Trace

/-!
# Deterministic machines

A machine is the usual way to show that a set of requirements is consistent: define a
machine, and prove that each of its traces satisfies the requirements.

The machine is activated once per tick. At tick `t` it reads the input `inp t` and
moves to a new state.
-/

namespace MetricTemporal

structure Machine (ι σ : Type) where
  init : σ
  step : σ → ι → σ

namespace Machine

variable {ι σ : Type}

/-- The state before the activation at tick `t`. -/
def before (m : Machine ι σ) (inp : Nat → ι) : Nat → σ
  | 0 => m.init
  | t + 1 => m.step (m.before inp t) (inp t)

/-- The state after the activation at tick `t`. -/
def after (m : Machine ι σ) (inp : Nat → ι) (t : Nat) : σ := m.before inp (t + 1)

/-- The observed trace: the input and the state after each activation. -/
def trace (m : Machine ι σ) (inp : Nat → ι) : Trace (ι × σ) :=
  fun t => (inp t, m.after inp t)

theorem after_eq (m : Machine ι σ) (inp : Nat → ι) (t : Nat) :
    m.after inp t = m.step (m.before inp t) (inp t) := rfl

/-- A predicate that holds at the start and that each step keeps holds at every tick. -/
theorem invariant (m : Machine ι σ) (inp : Nat → ι) {P : σ → Prop} (h0 : P m.init)
    (hs : ∀ s i, P s → P (m.step s i)) : ∀ t, P (m.before inp t)
  | 0 => h0
  | t + 1 => hs _ _ (invariant m inp h0 hs t)

end Machine

end MetricTemporal
