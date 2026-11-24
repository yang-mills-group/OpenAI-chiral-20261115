import GaugeFieldConstruction.CloverSymmetryWeyl
import GaugeFieldConstruction.MapleStemPV
/-! # No cross-read of spin-two with spin ≤ 1 at pure-time separation in a covariant system

Explicit proper cube movers for each current vs each spin-2 generator. Includes aligning
arbitrary two-point separation vector without using reflections.
-/
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option synthInstance.maxSize 6000
set_option maxRecDepth 5000
noncomputable section
namespace YM.GaugeFieldConstruction.Stage.CloverSymmetry
open Calibration Calibration.RawBank Floor Cauchy Row Phys Function Set Filter Wide Cell
open Matter (FlavorIndex)
open scoped BigOperators Topology Matrix Matrix.Norms.Frobenius
open Angles Flux One
attribute [local instance] Stage.iA Stage.iG Stage.iX
def move_H01: Signed := ⟨1, ![true,true,false,false]⟩
def move_H02: Signed := ⟨1, ![true,false,true,false]⟩
def move_H12: Signed := ⟨1, ![false,true,true,false]⟩
def move_Q01: Signed := ⟨⟨![1,0,2,3],![1,0,2,3], by intro i; fin_cases i <;> rfl, by intro i; fin_cases i <;> rfl⟩, ![true,false,false,false]⟩
def move_Q02: Signed := ⟨⟨![2,1,0,3],![2,1,0,3], by intro i; fin_cases i <;> rfl, by intro i; fin_cases i <;> rfl⟩, ![true,false,false,false]⟩
def move_Q12: Signed := ⟨⟨![0,2,1,3],![0,2,1,3], by intro i; fin_cases i <;> rfl, by intro i; fin_cases i <;> rfl⟩, ![false,true,false,false]⟩

macro "axis_acts" : tactic => `(tactic|
   simp only [ show move_H01.perm 0 = 0 from rfl,
      show move_H01.flip 0 = true from rfl,
      show move_H01.perm 1 = 1 from rfl,
      show move_H01.flip 1 = true from rfl,
      show move_H01.perm 2 = 2 from rfl,
      show move_H01.flip 2 = false from rfl,
      show move_H01.perm 3 = 3 from rfl,
      show move_H01.flip 3 = false from rfl,
      show move_H02.perm 0 = 0 from rfl,
      show move_H02.flip 0 = true from rfl,
      show move_H02.perm 1 = 1 from rfl,
      show move_H02.flip 1 = false from rfl,
      show move_H02.perm 2 = 2 from rfl,
      show move_H02.flip 2 = true from rfl,
      show move_H02.perm 3 = 3 from rfl,
      show move_H02.flip 3 = false from rfl,
      show move_H12.perm 0 = 0 from rfl,
      show move_H12.flip 0 = false from rfl,
      show move_H12.perm 1 = 1 from rfl,
      show move_H12.flip 1 = true from rfl,
      show move_H12.perm 2 = 2 from rfl,
      show move_H12.flip 2 = true from rfl,
      show move_H12.perm 3 = 3 from rfl,
      show move_H12.flip 3 = false from rfl,
      show move_Q01.perm 0 = 1 from rfl,
      show move_Q01.flip 0 = true from rfl,
      show move_Q01.perm 1 = 0 from rfl,
      show move_Q01.flip 1 = false from rfl,
      show move_Q01.perm 2 = 2 from rfl,
      show move_Q01.flip 2 = false from rfl,
      show move_Q01.perm 3 = 3 from rfl,
      show move_Q01.flip 3 = false from rfl,
      show move_Q02.perm 0 = 2 from rfl,
      show move_Q02.flip 0 = true from rfl,
      show move_Q02.perm 1 = 1 from rfl,
      show move_Q02.flip 1 = false from rfl,
      show move_Q02.perm 2 = 0 from rfl,
      show move_Q02.flip 2 = false from rfl,
      show move_Q02.perm 3 = 3 from rfl,
      show move_Q02.flip 3 = false from rfl,
      show move_Q12.perm 0 = 0 from rfl,
      show move_Q12.flip 0 = false from rfl,
      show move_Q12.perm 1 = 2 from rfl,
      show move_Q12.flip 1 = true from rfl,
      show move_Q12.perm 2 = 1 from rfl,
      show move_Q12.flip 2 = false from rfl,
      show move_Q12.perm 3 = 3 from rfl,
      show move_Q12.flip 3 = false from rfl,
      show Bool.xor false false=false from rfl, show Bool.xor false true=true from rfl, show Bool.xor true false=true from rfl, show Bool.xor true true=false from rfl, Bool.true_xor,Bool.false_xor,Bool.xor_true,Bool.xor_false,Bool.not_true,Bool.not_false,
      pay_false,pay_true])
lemma H02_dPlus00 : spinFrame four move_H02 dPlus00 = dPlus00 := by
  unfold dPlus00
  simp only [map_add,map_sub,map_nsmul,map_neg,ffMotion]; axis_acts <;> clovers_norm
  all_goals abel
lemma Q02_dPlus00 : spinFrame four move_Q02 dPlus00 = -dPlus00 := by
  unfold dPlus00
  simp only [map_add,map_sub,map_nsmul,map_neg,ffMotion]; axis_acts <;> clovers_norm
  all_goals abel
lemma H12_dPlus11 : spinFrame four move_H12 dPlus11 = dPlus11 := by
  unfold dPlus11
  simp only [map_add,map_sub,map_nsmul,map_neg,ffMotion]; axis_acts <;> clovers_norm
  all_goals abel
lemma Q12_dPlus11 : spinFrame four move_Q12 dPlus11 = -dPlus11 := by
  unfold dPlus11
  simp only [map_add,map_sub,map_nsmul,map_neg,ffMotion]; axis_acts <;> clovers_norm
  all_goals abel
lemma H01_dPlus01 : spinFrame four move_H01 dPlus01 = dPlus01 := by
  unfold dPlus01
  simp only [map_add,map_sub,map_nsmul,map_neg,ffMotion]; axis_acts <;> clovers_norm
  all_goals abel
lemma Q01_dPlus01 : spinFrame four move_Q01 dPlus01 = -dPlus01 := by
  unfold dPlus01
  simp only [map_add,map_sub,map_nsmul,map_neg,ffMotion]; axis_acts <;> clovers_norm
  all_goals abel
lemma H02_dPlus02 : spinFrame four move_H02 dPlus02 = dPlus02 := by
  unfold dPlus02
  simp only [map_add,map_sub,map_nsmul,map_neg,ffMotion]; axis_acts <;> clovers_norm
  all_goals abel
lemma Q02_dPlus02 : spinFrame four move_Q02 dPlus02 = -dPlus02 := by
  unfold dPlus02
  simp only [map_add,map_sub,map_nsmul,map_neg,ffMotion]; axis_acts <;> clovers_norm
  all_goals abel
lemma H12_dPlus12 : spinFrame four move_H12 dPlus12 = dPlus12 := by
  unfold dPlus12
  simp only [map_add,map_sub,map_nsmul,map_neg,ffMotion]; axis_acts <;> clovers_norm
  all_goals abel
lemma Q12_dPlus12 : spinFrame four move_Q12 dPlus12 = -dPlus12 := by
  unfold dPlus12
  simp only [map_add,map_sub,map_nsmul,map_neg,ffMotion]; axis_acts <;> clovers_norm
  all_goals abel
lemma H02_dMinus00 : spinFrame four move_H02 dMinus00 = dMinus00 := by
  unfold dMinus00
  simp only [map_add,map_sub,map_nsmul,map_neg,ffMotion]; axis_acts <;> clovers_norm
  all_goals abel
lemma Q02_dMinus00 : spinFrame four move_Q02 dMinus00 = -dMinus00 := by
  unfold dMinus00
  simp only [map_add,map_sub,map_nsmul,map_neg,ffMotion]; axis_acts <;> clovers_norm
  all_goals abel
lemma H12_dMinus11 : spinFrame four move_H12 dMinus11 = dMinus11 := by
  unfold dMinus11
  simp only [map_add,map_sub,map_nsmul,map_neg,ffMotion]; axis_acts <;> clovers_norm
  all_goals abel
lemma Q12_dMinus11 : spinFrame four move_Q12 dMinus11 = -dMinus11 := by
  unfold dMinus11
  simp only [map_add,map_sub,map_nsmul,map_neg,ffMotion]; axis_acts <;> clovers_norm
  all_goals abel
lemma H01_dMinus01 : spinFrame four move_H01 dMinus01 = dMinus01 := by
  unfold dMinus01
  simp only [map_add,map_sub,map_nsmul,map_neg,ffMotion]; axis_acts <;> clovers_norm
  all_goals abel
lemma Q01_dMinus01 : spinFrame four move_Q01 dMinus01 = -dMinus01 := by
  unfold dMinus01
  simp only [map_add,map_sub,map_nsmul,map_neg,ffMotion]; axis_acts <;> clovers_norm
  all_goals abel
lemma H02_dMinus02 : spinFrame four move_H02 dMinus02 = dMinus02 := by
  unfold dMinus02
  simp only [map_add,map_sub,map_nsmul,map_neg,ffMotion]; axis_acts <;> clovers_norm
  all_goals abel
lemma Q02_dMinus02 : spinFrame four move_Q02 dMinus02 = -dMinus02 := by
  unfold dMinus02
  simp only [map_add,map_sub,map_nsmul,map_neg,ffMotion]; axis_acts <;> clovers_norm
  all_goals abel
lemma H12_dMinus12 : spinFrame four move_H12 dMinus12 = dMinus12 := by
  unfold dMinus12
  simp only [map_add,map_sub,map_nsmul,map_neg,ffMotion]; axis_acts <;> clovers_norm
  all_goals abel
lemma Q12_dMinus12 : spinFrame four move_Q12 dMinus12 = -dMinus12 := by
  unfold dMinus12
  simp only [map_add,map_sub,map_nsmul,map_neg,ffMotion]; axis_acts <;> clovers_norm
  all_goals abel

def timeHolds (s : Signed) := signBit s=false ∧ s.flip 3=false ∧ s.perm 3=3
lemma holdsBasis (s : Signed) (h : timeHolds s) (t : ℝ) : Ortho.move s.ortho (t • basis 3) = t • basis 3 := by
  have hc: Ortho.motion s.ortho (basis 3) = basis 3 := by
    ext a
    rw [Ortho.motion_at, Ortho.move,M4.move_basis]
    change s.matrix a 3 = basis 3 a
    rw [Signed.matrix_at, h.2.1,h.2.2]
    by_cases e:a=3 <;> simp [e,eq_comm]
  change Ortho.motion s.ortho _ = _; rw [map_smul,hc]

section
variable (L : UV four →ₗ[ℂ] CogPV →ₗ[ℂ] ℂ)
  (family : ∀ (s : Signed), timeHolds s → ∀ v w, L v w = L (spinFrame four s v) (spinFrame three s w))
include family

lemma discordPlus (v w) (s : Signed) (h : timeHolds s)
    (p : spinFrame four s v = v) (q : spinFrame three s w = -w) : L v w = 0 := by
  have z := family s h v w; rw [p,q,map_neg] at z
  linear_combination z / 2
lemma discordMinus (v w) (s : Signed) (h : timeHolds s)
    (p : spinFrame four s v = -v) (q : spinFrame three s w = w) : L v w = 0 := by
  have z := family s h v w; rw [p,q,map_neg, LinearMap.neg_apply] at z
  linear_combination z / 2
lemma axialCost_dPlus00 : L dPlus00 = 0 := by
  apply lectPV
  · exact discordMinus L family _ _ move_Q02 ⟨by decide,rfl,rfl⟩ Q02_dPlus00 (Empire.sends_1 ..)
  intro i a; rcases show a=0 ∨ a=1 ∨ a=2 ∨ a=3 from (by fin_cases a <;> decide) with rfl|rfl|rfl|rfl
  · apply discordPlus L family _ _ move_H02 ⟨by decide,rfl,rfl⟩ H02_dPlus00; rw [vFramePV _ _ _ (by decide)]; try rfl
  · apply discordMinus L family _ _ move_Q02 ⟨by decide,rfl,rfl⟩ Q02_dPlus00; rw [vFramePV _ _ _ (by decide)]; try rfl
  · apply discordPlus L family _ _ move_H02 ⟨by decide,rfl,rfl⟩ H02_dPlus00; rw [vFramePV _ _ _ (by decide)]; try rfl
  · apply discordMinus L family _ _ move_Q02 ⟨by decide,rfl,rfl⟩ Q02_dPlus00; rw [vFramePV _ _ _ (by decide)]; try rfl
lemma axialCost_dPlus11 : L dPlus11 = 0 := by
  apply lectPV
  · exact discordMinus L family _ _ move_Q12 ⟨by decide,rfl,rfl⟩ Q12_dPlus11 (Empire.sends_1 ..)
  intro i a; rcases show a=0 ∨ a=1 ∨ a=2 ∨ a=3 from (by fin_cases a <;> decide) with rfl|rfl|rfl|rfl
  · apply discordMinus L family _ _ move_Q12 ⟨by decide,rfl,rfl⟩ Q12_dPlus11; rw [vFramePV _ _ _ (by decide)]; try rfl
  · apply discordPlus L family _ _ move_H12 ⟨by decide,rfl,rfl⟩ H12_dPlus11; rw [vFramePV _ _ _ (by decide)]; try rfl
  · apply discordPlus L family _ _ move_H12 ⟨by decide,rfl,rfl⟩ H12_dPlus11; rw [vFramePV _ _ _ (by decide)]; try rfl
  · apply discordMinus L family _ _ move_Q12 ⟨by decide,rfl,rfl⟩ Q12_dPlus11; rw [vFramePV _ _ _ (by decide)]; try rfl
lemma axialCost_dPlus01 : L dPlus01 = 0 := by
  apply lectPV
  · exact discordMinus L family _ _ move_Q01 ⟨by decide,rfl,rfl⟩ Q01_dPlus01 (Empire.sends_1 ..)
  intro i a; rcases show a=0 ∨ a=1 ∨ a=2 ∨ a=3 from (by fin_cases a <;> decide) with rfl|rfl|rfl|rfl
  · apply discordPlus L family _ _ move_H01 ⟨by decide,rfl,rfl⟩ H01_dPlus01; rw [vFramePV _ _ _ (by decide)]; try rfl
  · apply discordPlus L family _ _ move_H01 ⟨by decide,rfl,rfl⟩ H01_dPlus01; rw [vFramePV _ _ _ (by decide)]; try rfl
  · apply discordMinus L family _ _ move_Q01 ⟨by decide,rfl,rfl⟩ Q01_dPlus01; rw [vFramePV _ _ _ (by decide)]; try rfl
  · apply discordMinus L family _ _ move_Q01 ⟨by decide,rfl,rfl⟩ Q01_dPlus01; rw [vFramePV _ _ _ (by decide)]; try rfl
lemma axialCost_dPlus02 : L dPlus02 = 0 := by
  apply lectPV
  · exact discordMinus L family _ _ move_Q02 ⟨by decide,rfl,rfl⟩ Q02_dPlus02 (Empire.sends_1 ..)
  intro i a; rcases show a=0 ∨ a=1 ∨ a=2 ∨ a=3 from (by fin_cases a <;> decide) with rfl|rfl|rfl|rfl
  · apply discordPlus L family _ _ move_H02 ⟨by decide,rfl,rfl⟩ H02_dPlus02; rw [vFramePV _ _ _ (by decide)]; try rfl
  · apply discordMinus L family _ _ move_Q02 ⟨by decide,rfl,rfl⟩ Q02_dPlus02; rw [vFramePV _ _ _ (by decide)]; try rfl
  · apply discordPlus L family _ _ move_H02 ⟨by decide,rfl,rfl⟩ H02_dPlus02; rw [vFramePV _ _ _ (by decide)]; try rfl
  · apply discordMinus L family _ _ move_Q02 ⟨by decide,rfl,rfl⟩ Q02_dPlus02; rw [vFramePV _ _ _ (by decide)]; try rfl
lemma axialCost_dPlus12 : L dPlus12 = 0 := by
  apply lectPV
  · exact discordMinus L family _ _ move_Q12 ⟨by decide,rfl,rfl⟩ Q12_dPlus12 (Empire.sends_1 ..)
  intro i a; rcases show a=0 ∨ a=1 ∨ a=2 ∨ a=3 from (by fin_cases a <;> decide) with rfl|rfl|rfl|rfl
  · apply discordMinus L family _ _ move_Q12 ⟨by decide,rfl,rfl⟩ Q12_dPlus12; rw [vFramePV _ _ _ (by decide)]; try rfl
  · apply discordPlus L family _ _ move_H12 ⟨by decide,rfl,rfl⟩ H12_dPlus12; rw [vFramePV _ _ _ (by decide)]; try rfl
  · apply discordPlus L family _ _ move_H12 ⟨by decide,rfl,rfl⟩ H12_dPlus12; rw [vFramePV _ _ _ (by decide)]; try rfl
  · apply discordMinus L family _ _ move_Q12 ⟨by decide,rfl,rfl⟩ Q12_dPlus12; rw [vFramePV _ _ _ (by decide)]; try rfl
lemma axialCost_dMinus00 : L dMinus00 = 0 := by
  apply lectPV
  · exact discordMinus L family _ _ move_Q02 ⟨by decide,rfl,rfl⟩ Q02_dMinus00 (Empire.sends_1 ..)
  intro i a; rcases show a=0 ∨ a=1 ∨ a=2 ∨ a=3 from (by fin_cases a <;> decide) with rfl|rfl|rfl|rfl
  · apply discordPlus L family _ _ move_H02 ⟨by decide,rfl,rfl⟩ H02_dMinus00; rw [vFramePV _ _ _ (by decide)]; try rfl
  · apply discordMinus L family _ _ move_Q02 ⟨by decide,rfl,rfl⟩ Q02_dMinus00; rw [vFramePV _ _ _ (by decide)]; try rfl
  · apply discordPlus L family _ _ move_H02 ⟨by decide,rfl,rfl⟩ H02_dMinus00; rw [vFramePV _ _ _ (by decide)]; try rfl
  · apply discordMinus L family _ _ move_Q02 ⟨by decide,rfl,rfl⟩ Q02_dMinus00; rw [vFramePV _ _ _ (by decide)]; try rfl
lemma axialCost_dMinus11 : L dMinus11 = 0 := by
  apply lectPV
  · exact discordMinus L family _ _ move_Q12 ⟨by decide,rfl,rfl⟩ Q12_dMinus11 (Empire.sends_1 ..)
  intro i a; rcases show a=0 ∨ a=1 ∨ a=2 ∨ a=3 from (by fin_cases a <;> decide) with rfl|rfl|rfl|rfl
  · apply discordMinus L family _ _ move_Q12 ⟨by decide,rfl,rfl⟩ Q12_dMinus11; rw [vFramePV _ _ _ (by decide)]; try rfl
  · apply discordPlus L family _ _ move_H12 ⟨by decide,rfl,rfl⟩ H12_dMinus11; rw [vFramePV _ _ _ (by decide)]; try rfl
  · apply discordPlus L family _ _ move_H12 ⟨by decide,rfl,rfl⟩ H12_dMinus11; rw [vFramePV _ _ _ (by decide)]; try rfl
  · apply discordMinus L family _ _ move_Q12 ⟨by decide,rfl,rfl⟩ Q12_dMinus11; rw [vFramePV _ _ _ (by decide)]; try rfl
lemma axialCost_dMinus01 : L dMinus01 = 0 := by
  apply lectPV
  · exact discordMinus L family _ _ move_Q01 ⟨by decide,rfl,rfl⟩ Q01_dMinus01 (Empire.sends_1 ..)
  intro i a; rcases show a=0 ∨ a=1 ∨ a=2 ∨ a=3 from (by fin_cases a <;> decide) with rfl|rfl|rfl|rfl
  · apply discordPlus L family _ _ move_H01 ⟨by decide,rfl,rfl⟩ H01_dMinus01; rw [vFramePV _ _ _ (by decide)]; try rfl
  · apply discordPlus L family _ _ move_H01 ⟨by decide,rfl,rfl⟩ H01_dMinus01; rw [vFramePV _ _ _ (by decide)]; try rfl
  · apply discordMinus L family _ _ move_Q01 ⟨by decide,rfl,rfl⟩ Q01_dMinus01; rw [vFramePV _ _ _ (by decide)]; try rfl
  · apply discordMinus L family _ _ move_Q01 ⟨by decide,rfl,rfl⟩ Q01_dMinus01; rw [vFramePV _ _ _ (by decide)]; try rfl
lemma axialCost_dMinus02 : L dMinus02 = 0 := by
  apply lectPV
  · exact discordMinus L family _ _ move_Q02 ⟨by decide,rfl,rfl⟩ Q02_dMinus02 (Empire.sends_1 ..)
  intro i a; rcases show a=0 ∨ a=1 ∨ a=2 ∨ a=3 from (by fin_cases a <;> decide) with rfl|rfl|rfl|rfl
  · apply discordPlus L family _ _ move_H02 ⟨by decide,rfl,rfl⟩ H02_dMinus02; rw [vFramePV _ _ _ (by decide)]; try rfl
  · apply discordMinus L family _ _ move_Q02 ⟨by decide,rfl,rfl⟩ Q02_dMinus02; rw [vFramePV _ _ _ (by decide)]; try rfl
  · apply discordPlus L family _ _ move_H02 ⟨by decide,rfl,rfl⟩ H02_dMinus02; rw [vFramePV _ _ _ (by decide)]; try rfl
  · apply discordMinus L family _ _ move_Q02 ⟨by decide,rfl,rfl⟩ Q02_dMinus02; rw [vFramePV _ _ _ (by decide)]; try rfl
lemma axialCost_dMinus12 : L dMinus12 = 0 := by
  apply lectPV
  · exact discordMinus L family _ _ move_Q12 ⟨by decide,rfl,rfl⟩ Q12_dMinus12 (Empire.sends_1 ..)
  intro i a; rcases show a=0 ∨ a=1 ∨ a=2 ∨ a=3 from (by fin_cases a <;> decide) with rfl|rfl|rfl|rfl
  · apply discordMinus L family _ _ move_Q12 ⟨by decide,rfl,rfl⟩ Q12_dMinus12; rw [vFramePV _ _ _ (by decide)]; try rfl
  · apply discordPlus L family _ _ move_H12 ⟨by decide,rfl,rfl⟩ H12_dMinus12; rw [vFramePV _ _ _ (by decide)]; try rfl
  · apply discordPlus L family _ _ move_H12 ⟨by decide,rfl,rfl⟩ H12_dMinus12; rw [vFramePV _ _ _ (by decide)]; try rfl
  · apply discordMinus L family _ _ move_Q12 ⟨by decide,rfl,rfl⟩ Q12_dMinus12; rw [vFramePV _ _ _ (by decide)]; try rfl
theorem axialCost {v} (hv : v∈ orbitSpin2) (w : CogPV) : L v w = 0 := by
  have h : orbitSpin2 ≤ LinearMap.ker L := by
    apply Submodule.span_le.mpr; rintro x ⟨a,rfl⟩; cases a
    · exact axialCost_dPlus00 L family
    · exact axialCost_dPlus11 L family
    · exact axialCost_dPlus01 L family
    · exact axialCost_dPlus02 L family
    · exact axialCost_dPlus12 L family
    · exact axialCost_dMinus00 L family
    · exact axialCost_dMinus11 L family
    · exact axialCost_dMinus01 L family
    · exact axialCost_dMinus02 L family
    · exact axialCost_dMinus12 L family
  rw [show L v = 0 from h hv]; rfl
end

lemma lowCost (s:SO) (v : CogPV) : ledger All four s (LowIncPV v)=LowIncPV (ledger All three s v) := by
  apply Calibration.inject four
  rw [riseGrade, LowFivePV, LowFivePV,riseGrade]

/-- For ordering poses. Adapt A13.squash using only proper rotors. -/
lemma upToTime (v : E4) : ∃ g : SO, ∃ c : ℝ, Ortho.move g.val v = c • basis 3 := by
  have hu (i : Axis) (v : E4) (s : Finset Axis) (h : i ∉ s) :
      ∃ g ∈ orbit, ∀ j ∈ s, Ortho.move g v j = 0 := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, orbit.one_mem, by simp⟩
    | @insert j s hj ih =>
      obtain ⟨hij, his⟩ := (show i ≠ j ∧ i ∉ s by simpa using h)
      obtain ⟨b, hb, hbs⟩ := ih his
      obtain ⟨t, ht⟩ := YM.Work.A13.plane_eliminates hij (Ortho.move b v)
      let r := Ortho.oneParameter (Ortho.plane i j) t
      have hr : r ∈ orbit := paid _ _
      refine ⟨r * b, orbit.mul_mem hr hb, ?_⟩
      intro k hk
      rw [Ortho.move_mul]
      rcases Finset.mem_insert.mp hk with he | hm
      · subst k; exact ht
      have hki : k ≠ i := fun e => his (e ▸ hm)
      have hkj : k ≠ j := fun e => hj (e ▸ hm)
      exact ((YM.Work.A13.plane_givens hij (Ortho.move b v) t).2.2 k hki hkj).trans (hbs k hm)
  obtain ⟨g,hg,hall⟩ := hu 3 v (Finset.univ.erase 3) (by simp)
  refine ⟨⟨g,hg⟩,Ortho.move g v 3,PiLp.ext ?_⟩
  intro k; by_cases h : k=3
  · subst k; simp
  simp [h, hall k (by simp [h])]

#print axioms axialCost
end YM.GaugeFieldConstruction.Stage.CloverSymmetry
end
