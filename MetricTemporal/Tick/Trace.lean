/-!
# Timed properties over discrete traces

A trace gives the observed state at each tick. A tick is the time resolution of the
document under study, for example one thread period or one second. Each document
states its tick length.

The operators are the bounded operators of metric temporal logic (MTL) on discrete
time. They are Lean functions, not a formula type, so a requirement can mix them with
any Lean predicate.
-/

namespace MetricTemporal

/-- The observed state at each tick. -/
abbrev Trace (σ : Type) := Nat → σ

/-- A timed property. `φ tr t` means that `φ` holds on trace `tr` at tick `t`. -/
abbrev TProp (σ : Type) := Trace σ → Nat → Prop

/-- `φ` holds on the whole trace, that is, at tick 0. -/
def Sat {σ : Type} (tr : Trace σ) (φ : TProp σ) : Prop := φ tr 0

namespace TProp

variable {σ : Type}

/-- A predicate on the current state. -/
def now (p : σ → Prop) : TProp σ := fun tr t => p (tr t)

def neg (φ : TProp σ) : TProp σ := fun tr t => ¬ φ tr t

def and (φ ψ : TProp σ) : TProp σ := fun tr t => φ tr t ∧ ψ tr t

def or (φ ψ : TProp σ) : TProp σ := fun tr t => φ tr t ∨ ψ tr t

def imp (φ ψ : TProp σ) : TProp σ := fun tr t => φ tr t → ψ tr t

/-- `G φ`: `φ` holds at every tick from now on. -/
def always (φ : TProp σ) : TProp σ := fun tr t => ∀ t', t ≤ t' → φ tr t'

/-- `F φ`: `φ` holds at some tick from now on. -/
def eventually (φ : TProp σ) : TProp σ := fun tr t => ∃ t', t ≤ t' ∧ φ tr t'

/-- `G[a,b] φ`: `φ` holds at every tick between `a` and `b` ticks from now. -/
def alwaysIn (a b : Nat) (φ : TProp σ) : TProp σ :=
  fun tr t => ∀ d, a ≤ d → d ≤ b → φ tr (t + d)

/-- `F[a,b] φ`: `φ` holds at some tick between `a` and `b` ticks from now. -/
def eventuallyIn (a b : Nat) (φ : TProp σ) : TProp σ :=
  fun tr t => ∃ d, a ≤ d ∧ d ≤ b ∧ φ tr (t + d)

/-- `φ U[a,b] ψ`: `ψ` holds between `a` and `b` ticks from now, and `φ` holds at every
tick before that. -/
def untilIn (a b : Nat) (φ ψ : TProp σ) : TProp σ :=
  fun tr t => ∃ d, a ≤ d ∧ d ≤ b ∧ ψ tr (t + d) ∧ ∀ e, e < d → φ tr (t + e)

/-- Past operator `O[a,b] φ`: `φ` held at some tick between `a` and `b` ticks ago. -/
def onceIn (a b : Nat) (φ : TProp σ) : TProp σ :=
  fun tr t => ∃ d, a ≤ d ∧ d ≤ b ∧ d ≤ t ∧ φ tr (t - d)

/-- Past operator `H[a,b] φ`: `φ` held at every tick between `a` and `b` ticks ago.
Ticks before the start of the trace do not count. -/
def historicallyIn (a b : Nat) (φ : TProp σ) : TProp σ :=
  fun tr t => ∀ d, a ≤ d → d ≤ b → d ≤ t → φ tr (t - d)

/-- Bounded response: each time `φ` holds, `ψ` holds at most `d` ticks later. -/
def leadsToWithin (d : Nat) (φ ψ : TProp σ) : TProp σ :=
  always (imp φ (eventuallyIn 0 d ψ))

variable {φ ψ : TProp σ} {tr : Trace σ} {t : Nat}

theorem always_now (h : always φ tr t) : φ tr t := h t (Nat.le_refl t)

theorem always_of_le {t' : Nat} (h : always φ tr t) (ht : t ≤ t') : always φ tr t' :=
  fun s hs => h s (Nat.le_trans ht hs)

theorem always_mono (h : ∀ tr t, φ tr t → ψ tr t) : always φ tr t → always ψ tr t :=
  fun hφ t' ht => h tr t' (hφ t' ht)

theorem always_and : always (and φ ψ) tr t ↔ always φ tr t ∧ always ψ tr t :=
  ⟨fun h => ⟨fun s hs => (h s hs).1, fun s hs => (h s hs).2⟩,
   fun h s hs => ⟨h.1 s hs, h.2 s hs⟩⟩

theorem alwaysIn_mono {a a' b b' : Nat} (ha : a ≤ a') (hb : b' ≤ b) :
    alwaysIn a b φ tr t → alwaysIn a' b' φ tr t :=
  fun h d hd1 hd2 => h d (Nat.le_trans ha hd1) (Nat.le_trans hd2 hb)

theorem eventuallyIn_mono {a a' b b' : Nat} (ha : a' ≤ a) (hb : b ≤ b') :
    eventuallyIn a b φ tr t → eventuallyIn a' b' φ tr t :=
  fun ⟨d, hd1, hd2, h⟩ => ⟨d, Nat.le_trans ha hd1, Nat.le_trans hd2 hb, h⟩

/-- `F[a,b]` and `G[a,b]` are dual. -/
theorem not_eventuallyIn {a b : Nat} :
    ¬ eventuallyIn a b φ tr t ↔ alwaysIn a b (neg φ) tr t :=
  ⟨fun h d hd1 hd2 hφ => h ⟨d, hd1, hd2, hφ⟩,
   fun h ⟨d, hd1, hd2, hφ⟩ => h d hd1 hd2 hφ⟩

theorem alwaysIn_of_always (h : always φ tr t) (b : Nat) : alwaysIn 0 b φ tr t :=
  fun d _ _ => h (t + d) (Nat.le_add_right t d)

/-- A longer deadline is a weaker requirement. -/
theorem leadsToWithin_mono {d d' : Nat} (hd : d ≤ d') :
    leadsToWithin d φ ψ tr t → leadsToWithin d' φ ψ tr t :=
  fun h s hs hφ => eventuallyIn_mono (Nat.le_refl 0) hd (h s hs hφ)

end TProp

theorem sat_always {σ : Type} {tr : Trace σ} {φ : TProp σ} :
    Sat tr (TProp.always φ) ↔ ∀ t, φ tr t :=
  ⟨fun h t => h t (Nat.zero_le t), fun h t _ => h t⟩

end MetricTemporal
