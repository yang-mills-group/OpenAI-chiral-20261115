import GaugeFieldConstruction.AxisTapPV
import GaugeFieldConstruction.GravifierN
import GaugeFieldConstruction.SunfireCell
import GaugeFieldConstruction.Cop
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option synthInstance.maxSize 10050
noncomputable section
namespace YM.GaugeFieldConstruction.Stage
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Ember Ember.Volumetric Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Boundary Finset Mink RawBank Cell
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff
attribute [local instance] Ember.iG Ember.iF Ember.iX Ember.iU -- tune names
open GaugeFieldConstruction.Invoice.curvΝ
-- not just rank certificates from H.World; all vector columns through D3 (NOT saying all D4,5 uncontracted). independence in W under the identification. IdW frame = PH engineering length. not adding axioms beyond closure
abbrev ShIdPV:=Axis×IdWitPV
abbrev RushSlotPV (p:ShIdPV):= SpinSlot3 p.2 p.1
private lemma pullSpanPV (i:Axis)(b:IdWitPV)(c: ShIdPV) (m:UF three)(h:m=(DeckF three).issue (ket i)) : ((WorkHPV i i (RushSlotPV c)).2.2.1 b) = if c=(i,b) then m else 0:=by
 rw [RushSlotPV,WorkPortPV]; by_cases p:c.1=i
 · rw[if_pos p.symm]; unfold SpinSlot3; rw [riseInPV,h]
   by_cases t:c.2=b
   · rw[if_pos t,if_pos (Prod.ext p t)]
   rw[if_neg t,if_neg (fun H=> t (congrArg Prod.snd H))]
 rw[if_neg (Ne.symm p),if_neg fun H=> p (congrArg Prod.fst H)]; rfl
lemma fullRankLipPV (z:ShIdPV→ℂ)(u:ℂ)(h: u • one three+∑ i:ShIdPV,z i • RushSlotPV i=0): z=0∧u=0:=by
 have hp(v:ShIdPV): z v=0:=by
    obtain ⟨i,b⟩:=v
    let L:CogPV→ₗ[ℂ] UF three:= (LinearMap.proj (R:=ℂ) b ∘ₗ LinearMap.fst ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _) ∘ₗ WorkHPV i i -- tune typo
    let m:UF three:=(DeckF three).issue (ket i); have hm:m ≠ 0:= by intro e; exact ζτN i ((vValPV i).symm.trans (congrArg Subtype.val e))
    have H:=congrArg L h; rw [map_zero,map_add,map_smul,map_sum] at H -- tune syntax
    rw [show L (one three)=0 from ?_,smul_zero,zero_add] at H
    · have hu(c:ShIdPV):L (RushSlotPV c)=if c=(i,b) then m else 0:= pullSpanPV i b c m rfl; rw[sum_eq_single (i,b)] at H; rw [map_smul,hu,if_pos rfl] at H; exact (smul_eq_zero.mp H).resolve_right hm
      · intro j _ p; rw[map_smul,hu, if_neg p,smul_zero]
      simp
    change (WorkHPV i i (one three)).2.2.1 b= _; rw[WorkOnePV]; rfl
 simp_rw [hp] at h; rw [show (∑ i:ShIdPV,(0:ℂ) • RushSlotPV i)=0 from by simp,add_zero] at h; exact ⟨funext hp,(smul_eq_zero.mp h).resolve_right (fun E=> one_ne_zero (congrArg (readOne three) E))⟩
#print axioms fullRankLipPV
end YM.GaugeFieldConstruction.Stage
end
