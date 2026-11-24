import GaugeFieldConstruction.AxisTapPV
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
open Mink
lemma legAgePV (p:Lorentz)(x:CogPV):ledgerL All p (LowIncPV x)=LowIncPV (ForecastLPV p x):=by
 suffices H:(ledgerL All p) ∘ₗ LowIncPV = LowIncPV ∘ₗ ForecastLPV p from LinearMap.congr_fun H x
 refine lectPV _ _ ?_ (fun i a=>?_)
 · rw [LinearMap.comp_apply,LinearMap.comp_apply,FogOnePV]; exact ScaleOnePV ..
 rw[LinearMap.comp_apply, RegisterLowPV,ScopeLegPV,LinearMap.comp_apply,FogTaxesPV,map_sum]; simp_rw[map_smul,RegisterLowPV]
lemma legFreePV (p:Lorentz)(U: FreeName three)(x): U.c (ForecastLPV p x)=ForecastLPV p (U.c x):=by
 have H(a b:Axis)(x):U.c (FlagPV a b x)=FlagPV a b (U.c x):=by rw [FlagPV,LinearMap.sub_apply,LinearMap.sub_apply,map_sub,U.h]; rfl
 have V(i:Axis)(x): U.c (IronPV i x)=IronPV i (U.c x):=by simp only [IronPV,LinearMap.smul_apply,Module.End.mul_apply,map_smul,H]
 have payApplyPV(u:Bool)(K: Module.End ℂ CogPV)(x:CogPV): (pay u K) x=pay u (K x):=by cases u <;> rfl
 have G(i j:Axis)(x) : U.c (WorkHPV i j x)=WorkHPV i j (U.c x):=by
    simp only [WorkHPV,payApplyPV,Module.End.mul_apply]; cases ((Count.sw i j).flip i) <;>simp only [pay_false,pay_true,map_neg,U.h,V]
 unfold ForecastLPV; simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,map_sum,map_add,map_smul,G]; rfl
variable {S:City}{P:Axis→Across}{L:Sheds S P}{C:Supplies L}{u:ℕ→Carat} (p:Ticket u C)
open Ember.Volumetric.FirstPackMars
lemma takesGatePV (g:Lorentz)(x:CogPV): SpheruleL p g (LowIncPV x)=LowIncPV (ForecastLPV g x):=by
 let F:=p.path.caller three; let P:=p.path.caller four
 have H(x:CogPV):P.c (LowIncPV x)= LowIncPV (F.c x):=by apply Calibration.inject four; rw [p.path.flight, LowFivePV,LowFivePV,p.path.flight] -- tune orientation
 obtain ⟨z,rfl⟩:= F.c.surjective x; rw [← H (x:=z), SpheruleTravelL, p.active,legAgePV,H,legFreePV] -- H syntax
#print axioms takesGatePV
end YM.GaugeFieldConstruction.Stage
end
