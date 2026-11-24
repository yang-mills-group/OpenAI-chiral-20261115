import Merino.JadeEye.Dup

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.JadeEye
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Swell

open scoped ContDiff
variable {V W : Type}[NormedAddCommGroup V][NormedSpace ℝ V]
 [NormedAddCommGroup W][NormedSpace ℝ W]

variable {C t:ℝ}{J:V→ℂ}
lemma ferment (u:0≤t)(p:t≤1)(v:∀ x:V,‖x‖≤t→Jet.Allows 6 J x C)
     (d:fderiv ℝ J 0 = 0) (z:V)(q:‖z‖≤t)(L: W→L[ℝ]V)(m:‖L‖≤t):
  Jet.Allows 6 (fun y=>J (z+L y)) 0 (‖J 0‖+C*t^2):=by
 let S:=closedBall (0:V) t
 have w:=convex_closedBall (0:V) t
 have e: (0:V)∈S:=mem_closedBall_self u
 have g:0≤C:=(v z q).nonneg
 have h(x:V)(hx:x∈S): ‖x‖≤t:=by unfold S at hx; simpa using hx
 have a(x:V)(hx:x∈S): ‖fderiv ℝ J x‖≤C*t:=by
   have y := w.norm_image_sub_le_of_norm_fderiv_le
      (f:=fderiv ℝ J) (𝕜:=ℝ)
      (C:=C)
      (fun y k=> (((v y (h _ k)).smooth.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num)))
      (fun y k=>by rw [← norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]; exact (v y (h _ k)).norm_le _ (by decide))
      e hx
   rw [d,sub_zero,sub_zero] at y; exact y.trans (mul_le_mul_of_nonneg_left (h _ hx) g)


 have k:z∈S:=by unfold S; simpa using q
 let K:=fun x=>J (z+x)
 have f:ContDiffAt ℝ (6:ℕ) K (L (0:W)):=
   (show ContDiffAt _ _ J (z+L (0:W)) from by rw [L.map_zero,add_zero]; exact (v z q).smooth).comp _ (contDiffAt_const.add contDiffAt_id)
 refine ⟨f.comp 0 L.contDiff.contDiffAt,?_⟩
 intro j hj
 by_cases b:j=0
 · have r:=w.norm_image_sub_le_of_norm_fderiv_le (f:=J) (𝕜:=ℝ)
     (fun y k=> (v y (h _ k)).smooth.differentiableAt (by norm_num)) a e k
   rw [b,norm_iteratedFDeriv_zero,map_zero,add_zero]
   rw [sub_zero] at r
   calc
    _ = ‖J 0+(J z-J 0)‖:=by rw [add_sub_cancel]
    _ ≤ ‖J 0‖+‖J z-J 0‖:= norm_add_le ..
    _ ≤ _:= add_le_add le_rfl ((r.trans (mul_le_mul_of_nonneg_left q (by positivity))).trans_eq (by ring))
 change ‖iteratedFDeriv ℝ j (K ∘ L) 0‖≤_
 rw [Push.Uniform.iter_lin_at (L:=L) (k:=j) (f.of_le (by exact_mod_cast hj))]
 refine le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..) (le_trans ?_ (le_add_of_nonneg_left (norm_nonneg _)))
 rw [prod_const,card_univ,Fintype.card_fin]
 unfold K
 rw [iteratedFDeriv_comp_add_left,L.map_zero,add_zero]
 by_cases r:j=1
 · rw [r,pow_one,norm_iteratedFDeriv_one,pow_two,←mul_assoc]
   exact mul_le_mul (a z k) m (norm_nonneg _) (by positivity)
 have l:‖L‖^j≤t^2:=(pow_le_pow_left₀ (norm_nonneg _) m j).trans (pow_le_pow_of_le_one u p (by omega))
 exact mul_le_mul ((v z q).norm_le _ hj) l (by positivity) g
