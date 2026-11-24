import GaugeFieldConstruction.IvyMajorL
/-!
# Detecting prices of any U4 cold readers directly

 No rotational conclusions needed. Only same-U4 probes applied. phrase in Test costs so ports align true plenum budgets.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 10050
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Boundary Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Classical
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {n m:ℕ} {S: City} {P:Axis→Across} {L:Sheds S P} {C: Supplies L} {u:ℕ→Carat}
variable (p:Ticket u C) (Y:AreaQc S)
open Wick Mirror Invoice Raster
variable (Z:CloudsL)(v:∀ a b:ΧiMars,ContinuousOn (tastePairL Z a b) (conf 2))(Q:Carat)
include v
noncomputable def valζL (j:ProbeIvL): ΧiMars→ₗ[ℂ]ℂ where
 toFun x:= (Q.u.roll j.1.p).applyTo (tastePairL Z ((Q.G four).c x) ((Q.G four).c j.2))
 map_add' x y:=by
    unfold YM.Test.applyTo; rw[← integral_add ((Q.u.roll j.1.p).smearing (v _ _)) ((Q.u.roll j.1.p).smearing (v _ _))]; apply integral_congr_ae; refine Eventually.of_forall fun r=>?_; simp only; rw [←mul_add]; congr 1; unfold tastePairL
    let F:ΧiMars→ΧiMars:=(Q.G four).c; let K:Fin 2→ ΧiMars:=![F j.2, F x]
    have hm(z:ΧiMars): Function.update K (1:Fin 2) z= ![F j.2,z]:=by funext i; fin_cases i <;> simp [K] -- tune
    rw [map_add]; change (Z 2 r) ![F j.2, F x+F y]= _; rw[←hm, MultilinearMap.map_update_add, hm, hm]
 map_smul' c x:=by
    unfold YM.Test.applyTo; rw [map_smul,RingHom.id_apply,smul_eq_mul,←integral_const_mul]; apply integral_congr_ae; refine Eventually.of_forall fun r=>?_ ; simp only
    let F:ΧiMars→ΧiMars:=(Q.G four).c; let K:Fin 2→ ΧiMars:=![F j.2,F x]
    have hm(z:ΧiMars): Function.update K (1:Fin 2) z= ![F j.2,z]:=by funext i; fin_cases i <;> simp [K]
    unfold tastePairL; change _ * Z 2 r ![F j.2,c • F x]= _; rw [←hm, MultilinearMap.map_update_smul,hm,smul_eq_mul,mul_left_comm]
noncomputable abbrev valΩL: ΧiMars→ₗ[ℂ] ProbeIvL→ℂ:= LinearMap.pi (valζL Z v Q)
lemma valKnownL (x:ΧiMars)(u:ProbeIvL): valΩL Z v Q x u=(Q.u.roll u.1.p).applyTo (tastePairL Z ((Q.G four).c x) ((Q.G four).c u.2)):= rfl
lemma varianceUL (p:Scores ℂ atTop prismColdL (fun i:ℕ=>valΩL Z v (u i))): uncloudL Z:= by
 obtain ⟨x,e⟩:= (insight rainColdL p).1.exists; intro z hp; apply ((u x).G four).c.symm.injective; rw[map_zero]; refine (detect _).1 e _ (fun b=>?_); rw[valKnownL, LinearEquiv.apply_symm_apply]; exact ((YM.Test.weak_null (v _ _)).mpr (hp _)) _
#print axioms varianceUL
end YM.GaugeFieldConstruction.Ember.Volumetric
