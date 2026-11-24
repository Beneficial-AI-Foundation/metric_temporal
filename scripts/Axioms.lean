import MetricTemporal

/-! Prints the axioms that the main theorems use. Operate it with
`lake env lean scripts/Axioms.lean`. No theorem may use `sorryAx`. -/

open MetricTemporal

-- The core, moved from the document repositories
#print axioms sat_always
#print axioms TProp.not_eventuallyIn
#print axioms TProp.leadsToWithin_mono
#print axioms Machine.invariant

-- The general forms
#print axioms TProp.heldFor_iff_historicallyIn
#print axioms TProp.untilIn_witness_unique
#print axioms TProp.untilIn_at
#print axioms Machine.scan_eq
#print axioms Machine.prevOf_eq
#print axioms Machine.prevOf_trace
#print axioms sumRange_congr
#print axioms sumRange_zero
#print axioms sumRange_le_mul

-- Timed runs, moved from LeanAID
#print axioms upTo_split
#print axioms upTo_take
#print axioms div_le_div_of_le
#print axioms div_nonneg'
#print axioms sumFrom_mono
#print axioms sumFrom_const
#print axioms sumFrom_nonneg
#print axioms sumFrom_add
#print axioms integral_le_const
#print axioms integral_nonneg

-- The instances
#print axioms Examples.RegulatorInit.prevMode_eq
#print axioms Examples.RegulatorInit.initFor_iff
#print axioms Examples.Sr2011.idleFor_iff
#print axioms Examples.Sr2011.nonDeliveryRun_iff
#print axioms Examples.Sr2011.sumRange_le_mul
#print axioms Examples.Sr2011.prevOwed_obs
#print axioms Examples.Sr2011.prevTempRate_obs
#print axioms Examples.Sr2011.tempCarry_obs
#print axioms Examples.BtIds.lastRx_eq
#print axioms Examples.BtIds.lastTx_eq
#print axioms Examples.BtIds.responds_at
#print axioms Examples.BtIds.rx_inv
#print axioms Examples.BtIds.tx_inv
#print axioms Examples.MatterAcl.prevSt_machine
