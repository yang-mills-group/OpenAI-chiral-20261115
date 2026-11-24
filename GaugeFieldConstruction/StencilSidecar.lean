import GaugeFieldConstruction.StencilForecast
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
open Submodule
-- T abstract n current space with test. finite-dimensional standard constraints. no geometric imports, all symbolic Lie. 
variable {V:Type}[AddCommGroup V][Module ℂ V][FiniteDimensional ℂ V]
abbrev PrismSt (i:Axis): Submodule ℂ CogPV:= LinearMap.range (IronPV i)
variable {W:Axis→ V→ₗ[ℂ] CogPV}
lemma iron_plot_st (i:Axis) : Module.finrank ℂ (PrismSt i) ≤ 18:=by
    let T: (IdWitPV→ℂ)→ₗ[ℂ] CogPV:= ∑ b:IdWitPV,(LinearMap.proj (R:=ℂ) b).smulRight (SpinSlot3 b i)
    have hx(b:IdWitPV): SpinSlot3 b i∈ LinearMap.range T:=by
       use Pi.single b 1; unfold T; rw [LinearMap.sum_apply,sum_eq_single b]; · simp [Pi.single_apply]
       · intro x _ p; simp [Pi.single_apply,p,Ne.symm p]
       simp
    let P:=LinearMap.range T
    have hb:P.mkQ ∘ₗ (IronPV i)=0:=by
       apply lectPV
       · rw [LinearMap.comp_apply,IronOnePV,map_zero,LinearMap.zero_apply]
       intro j b; rw [LinearMap.comp_apply,IronPortPV]; split_ifs with p
       · rw[←p]; exact (Submodule.Quotient.mk_eq_zero _).mpr (hx _) -- tune
       rw[map_zero,LinearMap.zero_apply]
    have h:PrismSt i ≤ P:=fun y ⟨x,h⟩ => h ▸ ((Submodule.Quotient.mk_eq_zero _).1 (LinearMap.congr_fun hb x))
    exact (Submodule.finrank_mono h).trans ((LinearMap.finrank_range_le T).trans (show Module.finrank ℂ (IdWitPV→ℂ) ≤ 18 from by rw [Module.finrank_pi]; decide)) -- tune
variable (χ:∀ v, looksVectorSt (fun i => W i v))(q: ∀ i, Function.Injective (W i))
include χ q
lemma every_trade_st (h:Module.finrank ℂ V=18)(i:Axis): LinearMap.range (W i)=PrismSt i:=by
 have hp: LinearMap.range (W i)≤PrismSt i:=by
    rintro x ⟨v,rfl⟩; exact ⟨_,(ironWakeSt _ (χ v) i i).trans (if_pos rfl)⟩ -- infer
 apply Submodule.eq_of_le_of_finrank_le hp
 rw [LinearMap.finrank_range_of_inj (q i),h]; exact iron_plot_st _
lemma solveNameSt (h:Module.finrank ℂ V=18)(b:IdWitPV): ∃! v:V,∀ i:Axis, SpinSlot3 b i=W i v:=by
 obtain ⟨x,he⟩:= (show SpinSlot3 b 3∈ LinearMap.range (W 3) from ((every_trade_st χ q h 3).symm ▸ ⟨_, (IronPortPV 3 3 b).trans (if_pos rfl)⟩))
 refine ⟨x,fun i=>?_,fun y t=> q 3 ((t 3).symm.trans he.symm)⟩
 calc _ = WorkHPV 3 i (SpinSlot3 b 3):= ((WorkPortPV 3 i 3 b).trans (if_pos rfl)).symm
      _ = _:= by rw [←he]; exact (WorkVector_st _ (χ x) 3 i 3).trans (if_pos rfl)
lemma all_components_trade_st {x:Axis→ V}(h:(∑ i:Axis, W i (x i))=0) : x=0:=by
 ext i; apply q i; rw [Pi.zero_apply,map_zero]
 have h:=congrArg (fun a=> IronPV i a) h; simp only [map_sum, map_zero] at h; rw[sum_eq_single i] at h
 · rwa [show IronPV i (W i (x i))= _ from (ironWakeSt _ (χ (x i)) i i).trans (if_pos rfl)] at h
 · intro j _ e; exact (ironWakeSt _ (χ (x j)) i j).trans (if_neg (Ne.symm e))
 simp
variable (φ:Module.End ℂ CogPV)
-- specialization in Lo labels mastering fare & stars.Across choice. common
#print axioms solveNameSt
#print axioms all_components_trade_st
end YM.GaugeFieldConstruction.Stage
end
