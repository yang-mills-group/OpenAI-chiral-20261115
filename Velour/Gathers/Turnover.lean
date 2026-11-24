import Velour.Gathers.Totty
import Velour.Quilt.Edging

set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 28000
noncomputable section
namespace YM.Velour
open Function Filter TopologicalSpace Metric Set Complex
open scoped NNReal Topology 
open OS.Semigroup SatinJets
variable {H : Hilbert}{j : Axis} (S : OS.Semigroup H j) {a d:ℝ≥0}








lemma turnover (h:0<a): ‖mesh_diff S d * S.E a‖≤1/((a:ℝ)/2):=by
 let U: Set ℂ:= {x | (a:ℝ) ≤ x.re}
 have v:Convex ℝ U:= (convex_Ici _).linear_preimage Complex.reLm
 have y(z:ℂ)(t:z∈U):0<z.re:=
    (NNReal.coe_pos.mpr h).trans_le t
 rw [mesh_form,norm_smul, ← S.roots_heat (add_pos_of_pos_of_nonneg h zero_le),
      ←S.roots_heat h]
 have g:= v.norm_image_sub_le_of_norm_deriv_le (f:=S.F)
        (fun z t=>(S.localHeat _ (y z t)).differentiableAt)
        (fun z t=>le_trans (CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.deriv_heat_cost S z (y z t))
                  (show 1/(z.re/2) ≤ 1 / ((a:ℝ) / 2) by
                     gcongr; exact t))
        (show duration a ∈ U from le_refl (a:ℝ))
        (show duration (a+d) ∈ U by
           change _ ≤ Complex.re _
           simp [duration])
 rw [show duration (a+d)-duration a=duration d by simp [duration]] at g
 by_cases e:duration d=0
 · rw [e]; simp; positivity
 rw [norm_inv,mul_comm]
 exact inv_eq_one_div (‖duration d‖) ▸
     le_trans (mul_le_mul_of_nonneg_right g (by positivity))
         (le_of_eq (by field_simp))


variable (τ:ℕ→ℝ) {L:ℝ} (y:∀k,0<τ k)(r:1≤L)(u:∀k,L^k*τ k=τ 0)
    (c:ℕ→ℝ≥0)
include y r u

lemma turnover_shell:Costly H (fun k i=> shell S c (τ k) i):=by
 let B:=8/τ 0
 refine ⟨max B 1,L,le_max_right ..,r,fun k i=>?_⟩
 set b:=τ k/4 with e; have p:0<b:=by have := y k; positivity
 apply le_trans (turnover S (Real.toNNReal_pos.mpr p))
 rw [Real.coe_toNNReal _ p.le]
 suffices 1/(b/2)=B * L^k from this.le.trans
    (mul_le_mul_of_nonneg_right (le_max_left ..) (pow_nonneg (zero_le_one.trans r) _))
 have h:=y k; have h':0<L:=zero_lt_one.trans_le r
 rw [show B=8/τ 0 from rfl,e,←u k]
 field_simp
 ring


lemma turnover_quilt (V:ℕ→ℕ→H.Op)(h:Costly H V):
    Costly H (fun k i=> quilt S c (fun _=>V k) (τ k) i):=by
 let g:= turnover_shell S τ y r u c
 have b: Costly H (fun k (_:ℕ)=> S.E (Real.toNNReal (τ k / 4))):=
   Costly.bdd 1 fun _ _=>S.shrinks _
 exact (((g.mul h).mul b).sub ((b.mul h).mul g))
end YM.Velour
