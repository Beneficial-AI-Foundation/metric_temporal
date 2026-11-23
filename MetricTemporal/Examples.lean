import MetricTemporal.Tick.Past
import MetricTemporal.Tick.Future
import MetricTemporal.Tick.Window

/-!
# The instances of the general forms

Each section restates the helpers of one document with the definitions of the document,
over a small example type instead of the device type. Then it proves that each helper
is the general form of `Past.lean`, `Future.lean` or `Window.lean`, and derives the
lemmas of the document from the general lemmas.

- `RegulatorInit` (`patients_facing_verif`, `DeviceDocs/Example/RegulatorInit/Spec.lean`):
  `prevMode`, `initFor`.
- `Sr2011` (`patients_facing_verif`, `DeviceDocs/Sr2011/`): `prevOwed`, `prevTempRate`,
  `tempCarry`, `idleFor`, `nonDeliveryRun`, `sumRange` and its three lemmas,
  `prevOwed_obs`, `prevTempRate_obs`, `tempCarry_obs`.
- `BtIds` (`patients_facing_verif`, `DeviceDocs/BtIds/`): `prevDev`, `lastTx`,
  `lastRx`, `responds_at`, `responds_next`, `rx_inv`, `tx_inv`.
- `MatterAcl` (`iot_verif`, branch `matter-acl-tip`, `IotVerif/MatterAcl/`): `prevSt`,
  `prevSt_machine`.
-/

namespace MetricTemporal.Examples

open TProp

/-! ## RegulatorInit -/

namespace RegulatorInit

inductive Mode where
  | init
  | normal
  | failed
  deriving DecidableEq

structure Obs where
  status : Bool
  mode : Mode

def prevMode (tr : Trace Obs) : Nat → Mode
  | 0 => .init
  | t + 1 => (tr t).mode

def initFor (tr : Trace Obs) (t n : Nat) : Prop :=
  n ≤ t ∧ ∀ s, t - n ≤ s → s < t → (tr s).mode = .init

theorem prevMode_eq (tr : Trace Obs) : ∀ t, prevMode tr t = prevOf Obs.mode .init tr t
  | 0 => rfl
  | _ + 1 => rfl

theorem initFor_iff (tr : Trace Obs) (t n : Nat) :
    initFor tr t n ↔ heldFor (now fun o => o.mode = .init) n tr t := Iff.rfl

end RegulatorInit

/-! ## Sr2011 -/

namespace Sr2011

inductive Mode where
  | run
  | priming
  | suspended
  deriving DecidableEq

structure Obs where
  mode : Mode
  userAct : Bool
  bolus : Nat
  owed : Nat
  tempLeft : Nat
  tempRate : Nat

structure Params where
  tempHold : Bool

def sumRange (f : Nat → Nat) (t : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumRange f t n + f (t + n)

def prevOwed (tr : Trace Obs) : Nat → Nat
  | 0 => 0
  | t + 1 => (tr t).owed

def tempCarryOf (p : Params) (o : Obs) : Nat :=
  if p.tempHold = true ∧ o.mode = .priming then o.tempLeft else o.tempLeft - 1

def tempCarry (p : Params) (tr : Trace Obs) : Nat → Nat
  | 0 => 0
  | t + 1 => tempCarryOf p (tr t)

def prevTempRate (tr : Trace Obs) : Nat → Nat
  | 0 => 0
  | t + 1 => (tr t).tempRate

def nonDeliveryRun (tr : Trace Obs) (t n : Nat) : Prop :=
  n ≤ t + 1 ∧ (∀ s, t + 1 - n ≤ s → s ≤ t → (tr s).mode ≠ .run) ∧
    (n = t + 1 ∨ (tr (t - n)).mode = .run)

def idleFor (tr : Trace Obs) (t n : Nat) : Prop :=
  n ≤ t ∧ ∀ d, d ≤ n → (tr (t - d)).userAct = false

theorem sumRange_eq (f : Nat → Nat) (t : Nat) :
    ∀ n, sumRange f t n = MetricTemporal.sumRange f t n
  | 0 => rfl
  | n + 1 => by simp [sumRange, MetricTemporal.sumRange, sumRange_eq f t n]

/-- The three lemmas of the document, from the general lemmas. -/
theorem sumRange_congr {f g : Nat → Nat} (h : ∀ s, f s = g s) (t n : Nat) :
    sumRange f t n = sumRange g t n := by
  rw [sumRange_eq, sumRange_eq]; exact MetricTemporal.sumRange_congr h t n

theorem sumRange_zero {f : Nat → Nat} (t n : Nat) (h : ∀ k, k < n → f (t + k) = 0) :
    sumRange f t n = 0 := by
  rw [sumRange_eq]; exact MetricTemporal.sumRange_zero t n h

theorem sumRange_le_mul {f : Nat → Nat} {c : Nat} (h : ∀ s, f s ≤ c) (t n : Nat) :
    sumRange f t n ≤ n * c := by
  rw [sumRange_eq]; exact MetricTemporal.sumRange_le_mul h t n

theorem prevOwed_eq (tr : Trace Obs) : ∀ t, prevOwed tr t = prevOf Obs.owed 0 tr t
  | 0 => rfl
  | _ + 1 => rfl

theorem tempCarry_eq (p : Params) (tr : Trace Obs) :
    ∀ t, tempCarry p tr t = prevOf (tempCarryOf p) 0 tr t
  | 0 => rfl
  | _ + 1 => rfl

theorem prevTempRate_eq (tr : Trace Obs) : ∀ t, prevTempRate tr t = prevOf Obs.tempRate 0 tr t
  | 0 => rfl
  | _ + 1 => rfl

/-- `idleFor` includes tick `t`, so it is `heldFor` at `t + 1` with length `n + 1`. -/
theorem idleFor_iff (tr : Trace Obs) (t n : Nat) :
    idleFor tr t n ↔ heldFor (now fun o => o.userAct = false) (n + 1) tr (t + 1) := by
  constructor
  · intro ⟨hn, h⟩
    refine ⟨by omega, fun s hs1 hs2 => ?_⟩
    have := h (t - s) (by omega)
    rwa [show t - (t - s) = s by omega] at this
  · intro ⟨hn, h⟩
    exact ⟨by omega, fun d hd => h (t - d) (by omega) (by omega)⟩

/-- `nonDeliveryRun` is `heldForExactly` at `t + 1` with length `n`. -/
theorem nonDeliveryRun_iff (tr : Trace Obs) (t n : Nat) :
    nonDeliveryRun tr t n ↔ heldForExactly (now fun o => o.mode ≠ .run) n tr (t + 1) := by
  have hsub : t + 1 - n - 1 = t - n := by omega
  simp only [nonDeliveryRun, heldForExactly, heldFor, now, hsub, Decidable.not_not]
  constructor
  · intro ⟨hn, h, hm⟩
    exact ⟨⟨hn, fun s hs1 hs2 => h s hs1 (by omega)⟩, hm⟩
  · intro ⟨⟨hn, h⟩, hm⟩
    exact ⟨hn, fun s hs1 hs2 => h s hs1 (by omega), hm⟩

/-! A small machine with the fields of the document that the observers follow. -/

structure St where
  obs : Obs

def initSt : St := ⟨⟨.run, false, 0, 0, 0, 0⟩⟩

/-- Any step: the observer lemmas do not depend on it. -/
def machine (step : St → Obs → St) : Machine Obs St := ⟨initSt, step⟩

def obs (step : St → Obs → St) (inp : Nat → Obs) : Trace Obs :=
  fun t => ((machine step).after inp t).obs

variable {step : St → Obs → St} {inp : Nat → Obs}

theorem prevOwed_obs :
    ∀ t, prevOwed (obs step inp) t = ((machine step).before inp t).obs.owed := by
  intro t
  rw [prevOwed_eq]
  exact Machine.prevOf_eq (machine step) inp (tr := obs step inp) (g := fun s : St => s.obs.owed)
    rfl (fun _ => rfl) t

theorem prevTempRate_obs :
    ∀ t, prevTempRate (obs step inp) t = ((machine step).before inp t).obs.tempRate := by
  intro t
  rw [prevTempRate_eq]
  exact Machine.prevOf_eq (machine step) inp (tr := obs step inp)
    (g := fun s : St => s.obs.tempRate) rfl (fun _ => rfl) t

theorem tempCarry_obs (p : Params) :
    ∀ t, tempCarry p (obs step inp) t = tempCarryOf p ((machine step).before inp t).obs := by
  intro t
  rw [tempCarry_eq]
  refine Machine.prevOf_eq (machine step) inp (tr := obs step inp)
    (g := fun s : St => tempCarryOf p s.obs) ?_ (fun _ => rfl) t
  show tempCarryOf p initSt.obs = 0
  simp [tempCarryOf, initSt]

end Sr2011

/-! ## BtIds -/

namespace BtIds

/-- The device state, as one number. -/
abbrev Dev := Nat

structure Write where
  crcOk : Bool
  counter : Option Nat

structure Ind where
  body : Nat
  counter : Nat

structure Obs where
  write : Option Write
  ind : Option Ind
  dev : Dev

def nextCounter (c : Nat) : Nat := c % 255 + 1

def e2eOk (last : Nat) (w : Write) : Bool :=
  w.crcOk && w.counter == some (nextCounter last)

def lastRx (tr : Trace Obs) : Nat → Nat
  | 0 => 255
  | t + 1 =>
    match (tr t).write with
    | some w => if e2eOk (lastRx tr t) w then nextCounter (lastRx tr t) else lastRx tr t
    | none => lastRx tr t

def lastTx (tr : Trace Obs) : Nat → Nat
  | 0 => 255
  | t + 1 =>
    match (tr t).ind with
    | some i => i.counter
    | none => lastTx tr t

def prevDev (tr : Trace Obs) : Nat → Dev
  | 0 => (tr 0).dev
  | t + 1 => (tr t).dev

def Responds (D : Nat) (P : Dev → Nat → Dev → Prop) : TProp Obs := fun tr t =>
  TProp.untilIn 0 D (TProp.now fun o => o.ind = none)
    (fun tr u => ∃ i, (tr u).ind = some i ∧ P (prevDev tr u) i.body (tr u).dev) tr (t + 1)

/-- The step of `lastRx`. -/
def rxStep (r : Nat) (o : Obs) : Nat :=
  match o.write with
  | some w => if e2eOk r w then nextCounter r else r
  | none => r

theorem lastRx_eq (tr : Trace Obs) : ∀ t, lastRx tr t = scan 255 rxStep tr t
  | 0 => rfl
  | t + 1 => by
    simp only [lastRx, scan_succ, rxStep, ← lastRx_eq tr t]

theorem lastTx_eq (tr : Trace Obs) :
    ∀ t, lastTx tr t = hold 255 (fun o => o.ind.map Ind.counter) tr t
  | 0 => rfl
  | t + 1 => by
    rw [hold_succ, ← lastTx_eq tr t]
    simp only [lastTx]
    cases (tr t).ind <;> rfl

theorem prevDev_eq (tr : Trace Obs) : ∀ t, prevDev tr t = prevOf Obs.dev (tr 0).dev tr t
  | 0 => rfl
  | _ + 1 => rfl

variable {D : Nat} {tr : Trace Obs}

/-- `responds_at` of the document, from `untilIn_at`. -/
theorem responds_at {P : Dev → Nat → Dev → Prop} {t d : Nat} {i : Ind}
    (hp : Responds D P tr t) (hi : (tr (t + 1 + d)).ind = some i)
    (hb : ∀ e, e < d → (tr (t + 1 + e)).ind = none) :
    P (prevDev tr (t + 1 + d)) i.body (tr (t + 1 + d)).dev := by
  have hx : ∀ u, (∃ i, (tr u).ind = some i ∧ P (prevDev tr u) i.body (tr u).dev) →
      ¬ (tr u).ind = none := by
    intro u ⟨j, hj, _⟩ h; rw [hj] at h; cases h
  have hd : ¬ (tr (t + 1 + d)).ind = none := by rw [hi]; intro h; cases h
  obtain ⟨-, -, j, hj, hP⟩ := untilIn_at hp hx hd hb
  rw [hi] at hj; cases hj
  exact hP

theorem responds_next {P : Dev → Nat → Dev → Prop} {t : Nat} {i : Ind}
    (hp : Responds D P tr t) (hi : (tr (t + 1)).ind = some i) :
    P (tr t).dev i.body (tr (t + 1)).dev :=
  responds_at (d := 0) hp hi (fun e he => absurd he (Nat.not_lt_zero e))

/-! A small machine with the counter fields of the document. A write that passes the
E2E check starts a procedure, and its indication comes in the next tick. -/

structure In where
  write : Option Write
  dev : Dev

structure St where
  rx : Nat
  tx : Nat
  pending : Option Nat
  dev : Dev
  ind : Option Ind

def step (s : St) (i : In) : St :=
  { rx := rxStep s.rx ⟨i.write, none, i.dev⟩
    tx :=
      match s.pending with
      | some _ => nextCounter s.tx
      | none => s.tx
    pending :=
      match i.write with
      | some w => if e2eOk s.rx w then some i.dev else none
      | none => none
    dev := i.dev
    ind := s.pending.map fun b => ⟨b, nextCounter s.tx⟩ }

def machine : Machine In St := ⟨⟨255, 255, none, 0, none⟩, step⟩

def obs (inp : Nat → In) : Trace Obs := fun t =>
  let s := machine.after inp t
  ⟨(inp t).write, s.ind, s.dev⟩

variable {inp : Nat → In}

/-- `rx_inv` of the document, from the observer lemma. -/
theorem rx_inv (t : Nat) : (machine.before inp t).rx = lastRx (obs inp) t := by
  rw [lastRx_eq]
  exact (Machine.scan_eq machine inp (g := St.rx) rfl (fun _ => rfl) t).symm

/-- `tx_inv` of the document, from the observer lemma. -/
theorem tx_inv (t : Nat) : (machine.before inp t).tx = lastTx (obs inp) t := by
  rw [lastTx_eq]
  refine (Machine.scan_eq machine inp (g := St.tx) rfl (fun u => ?_) t).symm
  show (step (machine.before inp u) (inp u)).tx =
    ((step (machine.before inp u) (inp u)).ind.map Ind.counter).getD _
  simp only [step]
  cases (machine.before inp u).pending <;> rfl

end BtIds

/-! ## MatterAcl -/

namespace MatterAcl

/-- The state of the node, as one number. -/
abbrev St := Nat
abbrev Op := Nat
abbrev Res := Bool

abbrev Obs := Op × Res × St

def prevSt (s0 : St) (tr : Trace Obs) : Nat → St
  | 0 => s0
  | t + 1 => (tr t).2.2

theorem prevSt_eq (s0 : St) (tr : Trace Obs) :
    ∀ t, prevSt s0 tr t = prevOf (fun o => o.2.2) s0 tr t
  | 0 => rfl
  | _ + 1 => rfl

/-- Any machine whose state is a result and a node state, as in the document. -/
def machine (s0 : St) (step : Res × St → Op → Res × St) : Machine Op (Res × St) :=
  ⟨(true, s0), step⟩

/-- `prevSt_machine` of the document, from `Machine.prevOf_trace`. -/
theorem prevSt_machine (s0 : St) (step : Res × St → Op → Res × St) (inp : Nat → Op) :
    ∀ t, prevSt s0 ((machine s0 step).trace inp) t = ((machine s0 step).before inp t).2 := by
  intro t
  rw [prevSt_eq]
  exact Machine.prevOf_trace (machine s0 step) inp Prod.snd t

end MatterAcl

end MetricTemporal.Examples
