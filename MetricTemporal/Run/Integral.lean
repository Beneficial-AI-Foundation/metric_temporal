/-!
# The integral of a rate over integer time steps

A rate `f` that is constant on each step `[k, k + 1)` has the exact integral
`Σ_{k=a}^{b-1} f k / scale` over `[a, b)`. Here `scale` is the number of time steps in the
unit of the rate. LeanAID measures time in milliseconds and rates in U/h, so its `scale`
is `msPerHour = 3 600 000`.

- `sumFrom f a n`: `Σ_{i<n} f (a + i)`.
- `integral scale f a n`: `sumFrom f a n / scale`.
- `sumFrom_mono`, `sumFrom_const`, `sumFrom_nonneg`, `sumFrom_add`: monotonicity, the sum
  of a constant, nonnegativity, and the split of an interval.
- `integral_le_const`: for `0 < scale`, if `f k ≤ c` for all `k ≥ a`, then
  `integral scale f a n ≤ c · n / scale`.
- `integral_nonneg`: for `0 < scale`, a nonnegative rate has a nonnegative integral.
- The order lemmas on `Rat` that these proofs use: `div_le_iff_le_mul`,
  `le_div_iff_mul_le`, `div_le_div_of_le`, `div_nonneg'`.

From `LeanAID/Time/Run.lean` and `LeanAID/Proofs/Rounding.lean`.
-/

namespace MetricTemporal

/-! ### Order lemmas on `Rat` -/

theorem div_le_iff_le_mul {a b c : Rat} (hb : 0 < b) : a / b ≤ c ↔ a ≤ c * b := by
  constructor
  · intro h; exact Rat.not_lt.mp fun h' => Rat.not_lt.mpr h ((Rat.lt_div_iff hb).mpr h')
  · intro h; exact Rat.not_lt.mp fun h' => Rat.not_lt.mpr h ((Rat.lt_div_iff hb).mp h')

theorem le_div_iff_mul_le {a b c : Rat} (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b := by
  constructor
  · intro h; exact Rat.not_lt.mp fun h' => Rat.not_lt.mpr h ((Rat.div_lt_iff hc).mpr h')
  · intro h; exact Rat.not_lt.mp fun h' => Rat.not_lt.mpr h ((Rat.div_lt_iff hc).mp h')

theorem div_le_div_of_le {a b c : Rat} (hc : 0 < c) (h : a ≤ b) : a / c ≤ b / c := by
  rw [div_le_iff_le_mul hc, Rat.div_mul_cancel (by grind)]; exact h

theorem div_nonneg' {a c : Rat} (hc : 0 < c) (h : 0 ≤ a) : 0 ≤ a / c := by
  rw [le_div_iff_mul_le hc]; grind

/-! ### Sums and the integral -/

/-- `Σ_{i<n} f (a + i)`. -/
def sumFrom (f : Int → Rat) (a : Int) : Nat → Rat
  | 0 => 0
  | n + 1 => sumFrom f a n + f (a + n)

/-- The integral over `[a, a + n)` of a rate `f` that is constant on each time step, with
    `scale` time steps in the unit of the rate: `Σ_{i<n} f (a + i) / scale`. -/
def integral (scale : Rat) (f : Int → Rat) (a : Int) (n : Nat) : Rat := sumFrom f a n / scale

theorem sumFrom_mono {f g : Int → Rat} (a : Int) (h : ∀ k, a ≤ k → f k ≤ g k) :
    ∀ n, sumFrom f a n ≤ sumFrom g a n
  | 0 => Rat.le_refl
  | n + 1 => by
    simp only [sumFrom]
    have := sumFrom_mono a h n
    have := h (a + n) (by omega)
    grind

theorem sumFrom_const (c : Rat) (a : Int) : ∀ n, sumFrom (fun _ => c) a n = c * n
  | 0 => by simp [sumFrom]
  | n + 1 => by
    simp only [sumFrom, sumFrom_const c a n]
    push_cast; grind

theorem sumFrom_nonneg {f : Int → Rat} (a : Int) (h : ∀ k, 0 ≤ f k) : ∀ n, 0 ≤ sumFrom f a n
  | 0 => Rat.le_refl
  | n + 1 => by
    simp only [sumFrom]
    have := sumFrom_nonneg a h n
    have := h (a + n)
    grind

/-- Splitting an interval: `[a, a + m + n) = [a, a + m) ∪ [a + m, a + m + n)`. -/
theorem sumFrom_add (f : Int → Rat) (a : Int) (m : Nat) : ∀ n,
    sumFrom f a (m + n) = sumFrom f a m + sumFrom f (a + m) n
  | 0 => by simp only [sumFrom, Nat.add_zero]; grind
  | n + 1 => by
    rw [← Nat.add_assoc]
    simp only [sumFrom, sumFrom_add f a m n]
    have : a + ((m + n : Nat) : Int) = a + m + n := by push_cast; omega
    rw [this]; grind

/-- If `0 < scale` and `f k ≤ c` for all `k ≥ a`, then `integral scale f a n ≤ c · n / scale`. -/
theorem integral_le_const {scale : Rat} (hs : 0 < scale) {f : Int → Rat} {c : Rat} (a : Int)
    (n : Nat) (h : ∀ k, a ≤ k → f k ≤ c) :
    integral scale f a n ≤ c * n / scale := by
  unfold integral
  have := sumFrom_mono (f := f) (g := fun _ => c) a h n
  rw [sumFrom_const] at this
  exact div_le_div_of_le hs this

/-- If `0 < scale` and `f` is nonnegative, then `integral scale f a n` is nonnegative. -/
theorem integral_nonneg {scale : Rat} (hs : 0 < scale) {f : Int → Rat} (a : Int) (n : Nat)
    (h : ∀ k, 0 ≤ f k) : 0 ≤ integral scale f a n := by
  unfold integral
  exact div_nonneg' hs (sumFrom_nonneg a h n)

end MetricTemporal
