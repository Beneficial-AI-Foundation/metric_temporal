import MetricTemporal.Tick.Trace

/-!
# Sums over a window of ticks

- `sumRange f t n`: the sum of `f` over the `n` ticks that start at `t`.
- `sumRange_congr`: equal functions give equal sums.
- `sumRange_zero`: a function that is 0 in the window gives the sum 0.
- `sumRange_le_mul`: a function bounded by `c` gives a sum of at most `n * c`.
-/

namespace MetricTemporal

/-- The sum of `f` over the `n` ticks that start at `t`. -/
def sumRange (f : Nat → Nat) (t : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumRange f t n + f (t + n)

theorem sumRange_congr {f g : Nat → Nat} (h : ∀ s, f s = g s) (t : Nat) :
    ∀ n, sumRange f t n = sumRange g t n
  | 0 => rfl
  | n + 1 => by simp [sumRange, sumRange_congr h t n, h]

theorem sumRange_zero {f : Nat → Nat} (t : Nat) :
    ∀ n, (∀ k, k < n → f (t + k) = 0) → sumRange f t n = 0
  | 0, _ => rfl
  | n + 1, h => by
    simp [sumRange, sumRange_zero t n (fun k hk => h k (by omega)), h n (by omega)]

theorem sumRange_le_mul {f : Nat → Nat} {c : Nat} (h : ∀ s, f s ≤ c) (t : Nat) :
    ∀ n, sumRange f t n ≤ n * c
  | 0 => by simp [sumRange]
  | n + 1 => by
    have := sumRange_le_mul h t n
    have := h (t + n)
    simp only [sumRange, Nat.succ_mul]; omega

end MetricTemporal
