import MetricTemporal.Tick.Trace

/-!
# The next tick, and the witness of `untilIn`

- `TProp.next φ`: `φ` holds at the next tick.
- `TProp.untilIn_witness_unique`: if `ψ` excludes `φ` at each tick, then two witnesses
  of `φ U ψ` are equal. The witness of `untilIn` is not unique in general: if `φ` and
  `ψ` both hold at ticks `t` and `t + 1`, then 0 and 1 are both witnesses.
- `TProp.untilIn_at`: if `φ U[a,b] ψ` holds at `t`, `ψ` excludes `φ`, and `φ` holds at
  each tick before `t + d` but not at `t + d`, then `t + d` is the witness, so `ψ`
  holds there and `d` is in the bounds.
-/

namespace MetricTemporal

namespace TProp

variable {σ : Type} {φ ψ : TProp σ} {tr : Trace σ} {t : Nat}

/-- `X φ`: `φ` holds at the next tick. -/
def next (φ : TProp σ) : TProp σ := fun tr t => φ tr (t + 1)

theorem next_iff : next φ tr t ↔ φ tr (t + 1) := Iff.rfl

theorem always_next (h : always φ tr t) : always (next φ) tr t :=
  fun s hs => h (s + 1) (Nat.le_succ_of_le hs)

/-- Two witnesses of `φ U ψ` are equal if `ψ` excludes `φ` at each tick. -/
theorem untilIn_witness_unique (hx : ∀ u, ψ tr u → ¬ φ tr u) {d d' : Nat}
    (h : ψ tr (t + d) ∧ ∀ e, e < d → φ tr (t + e))
    (h' : ψ tr (t + d') ∧ ∀ e, e < d' → φ tr (t + e)) : d = d' := by
  rcases Nat.lt_trichotomy d d' with hlt | heq | hgt
  · exact absurd (h'.2 d hlt) (hx _ h.1)
  · exact heq
  · exact absurd (h.2 d' hgt) (hx _ h'.1)

/-- If `φ U[a,b] ψ` holds at `t` and `ψ` excludes `φ`, then the first tick at which `φ`
fails is the witness: `ψ` holds there, and its distance from `t` is in `[a, b]`. -/
theorem untilIn_at {a b d : Nat} (hu : untilIn a b φ ψ tr t)
    (hx : ∀ u, ψ tr u → ¬ φ tr u) (hd : ¬ φ tr (t + d))
    (hb : ∀ e, e < d → φ tr (t + e)) : a ≤ d ∧ d ≤ b ∧ ψ tr (t + d) := by
  obtain ⟨d', ha, hb', hψ, hφ⟩ := hu
  have : d' = d := by
    rcases Nat.lt_trichotomy d' d with hlt | heq | hgt
    · exact absurd (hb d' hlt) (hx _ hψ)
    · exact heq
    · exact absurd (hφ d hgt) hd
  subst this
  exact ⟨ha, hb', hψ⟩

end TProp

end MetricTemporal
