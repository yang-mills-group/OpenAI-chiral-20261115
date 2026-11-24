import YM.CF.Scree.Brief

/-!
# Raised support rates

We use the higher rate only in Reg budgeting. We won't feed a raised-rate
Reg to a meter calibrated differently; this is for incidence credit on
the ordinary arrays, in particular in consultations inside the step.
The angular, endpoint, measurability etc. tests remain exactly the same.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Zephyr
open Scree Skye RG Lattice Fock Pastry Finset
open scoped ContDiff

def rerate (P : BudgetPoint) (a : ℝ) (ha : 0 < a) : BudgetPoint :=
  { P with supportExponent := a, exponent_pos := ha }

/-- One unit of extra support rate. -/
abbrev plusP (P : BudgetPoint) :=
  rerate P (P.supportExponent + 1) (add_pos P.exponent_pos zero_lt_one)

variable {n : Side} (P T : BudgetPoint)

structure SameReads : Prop where
  scale : P.threshold = T.threshold
  grow : P.power = T.power
  probe : P.order = T.order

variable {P T}
namespace SameReads
theorem symm (p : SameReads P T) : SameReads T P :=
  ⟨p.1.symm, p.2.symm, p.3.symm⟩

variable {o : Seat n} {h c : ℝ}
theorem tariff_eq (p : SameReads P T) (o : Seat n) (h : ℝ) :
    tariff P o h = tariff T o h := by
  funext i
  simp only [tariff, p.grow]


theorem signsof {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    {F : tangD n → N} (p : SameReads P T) (s : Signs P o F c) :
    Signs T o F c := by
  refine ⟨s.grade, p.probe ▸ s.paid, fun j g k u => s.token j (g.trans p.probe.ge) k ?_⟩
  simpa only [BudgetPoint.dirBound, p.grow, p.scale] using u

theorem press {i : Hub n} {F : InkD n}
    (p : SameReads P T) (s : PressB P i F h c) :
    PressB T i F h c := by
  obtain ⟨b,x,g,t⟩ := s.worth
  refine ⟨s.term, s.fitted, s.measureV, s.gaugeV, b, x, fun V w j => p.signsof (g V ?_ j), ?_⟩
  · simpa only [p.scale] using w
  simpa only [p.tariff_eq] using t
end SameReads

theorem readsplus (P : BudgetPoint) : SameReads P (plusP P) := ⟨rfl, rfl, rfl⟩

#print axioms SameReads.press
end YM.CF.Zephyr
