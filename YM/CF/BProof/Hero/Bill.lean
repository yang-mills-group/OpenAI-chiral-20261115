import YM.CF.BProof.Dream.Shift
import YM.CF.BProof.Single.Coat
import YM.CF.Scroll.Loma

/-! Pay motion speed. Estimates measured in physical scaling of gauge chord.
Keep Spin/Tape centered at gauge variables not SU/Fock quotient. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Hero
open Function Dream Cube Spin Extension Metric Dial Lat Tulip Tenant Branch Fock SU
open scoped Topology Matrix Matrix.Norms.L2Operator ContDiff Classical BigOperators
attribute [local instance] opCStarAlgebra

abbrev Xd(x y:Ballot):ℝ:= ‖x.val-y.val‖
def xm := max 2 Spin.viewCost.choose
lemma xm_t:2≤xm:= le_max_left ..
lemma xm_low:1≤ xm:= le_trans one_le_two xm_t
lemma xm_p : 0<xm:=zero_lt_one.trans_le xm_low
lemma optic(U V:E) : Spin.scenery U V ≤ xm*cd group U V:= (Spin.viewCost.choose_spec.2.1 U V).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (cd_nonneg ..))
lemma scenic (U V:E) : cd group U V≤ xm*Spin.scenery U V:= (Spin.viewCost.choose_spec.2.2 U V).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (norm_nonneg _))
lemma optic₁(U V:E) : ‖fund U-fund V‖≤ xm*cd group U V:=(le_max_right ..).trans (optic U V)
lemma optic₂(U V:E) : ‖(matter U).val-(matter V).val‖≤ xm*cd group U V:=(le_max_left ..).trans (optic U V)
lemma Xd_triangle (x y z:Ballot): Xd x z≤ Xd x y+Xd y z:= norm_sub_le_norm_sub_add_norm_sub ..
lemma Xd_meta (x y:Ballot) : Dist.dist x y=Xd x y:=by rw [Subtype.dist_eq,dist_eq_norm]
lemma Xd_norm (x y:Ballot):0≤Xd x y:= norm_nonneg _
lemma scale_dist_t (U:E)(x y:Ballot): Xd (scaledV U x) (scaledV U y)=Xd x y:=by unfold Xd scaledV; dsimp only; rw [←turn_sub,turn_norm]
@[simp] lemma scaled_one : scaledV 1=id:=funext fun x=> Subtype.ext (act_one ..)
lemma scaled_seq (U V:E)(x:Ballot): scaledV (U*V) x=scaledV U (scaledV V x):=Subtype.ext (turn_seq ..)
lemma Xd_rate(U V:E)(x: Ballot) : Xd (scaledV U x) (scaledV V x)≤ xm*cd group U V:=by
 let X:=x.val; let A:=fund U-fund V; unfold Xd scaledV turn acts; dsimp only; rw [← ContinuousLinearMap.sub_apply, ← map_sub (Matrix.toEuclideanCLM (n:= F) (𝕜:=ℂ))]; exact (ContinuousLinearMap.le_opNorm ..).trans (by rw [vote_unit x,Matrix.l2_opNorm_toEuclideanCLM,mul_one]; exact optic₁ ..)
lemma Xd_bits(U V:E)(x y:Ballot): Xd (scaledV U x) (scaledV V y)≤ Xd x y+xm*cd group U V:= (Xd_triangle _ (scaledV U y) _).trans (add_le_add (scale_dist_t ..).le (Xd_rate ..))
lemma Xd_h(x y:Ballot): Xd x y≤ xm:= (norm_sub_le _ _).trans (by rw [vote_unit,vote_unit,show (1:ℝ)+1=2 by norm_num]; exact xm_t)
lemma trStamp (X:Stamp) : ‖Xᵀ‖= ‖X‖:=by rw [←Scroll.norm_cc Xᵀ, show cc Xᵀ=star X from rfl, norm_star]
lemma seat_rate(U V:E)(X:Stamp){v:ℝ}(h:‖X‖≤v): ‖motion U X-motion V X‖ ≤ 2*xm*cd group U V*v:=by
 let A:=(matter U).val; let B:=(matter V).val; let T:=xm*cd group U V; have he:‖A-B‖≤T:= optic₂ ..; have hv:0≤T:= mul_nonneg xm_p.le (cd_nonneg ..); have ha:‖A‖=1:= CStarRing.norm_of_mem_unitary (matter U).property; have hb:‖B‖=1:= CStarRing.norm_of_mem_unitary (matter V).property
 change ‖A*X*Aᵀ-B*X*Bᵀ‖≤_; rw [show A*X*Aᵀ-B*X*Bᵀ=A*X*(A-B)ᵀ+(A-B)*X*Bᵀ from (by rw [Matrix.transpose_sub,mul_sub,sub_mul,sub_mul]; abel)]
 apply (norm_add_le ..).trans; rw [mul_assoc 2,mul_assoc 2,two_mul]; apply add_le_add
 · rw [mul_comm _ v]; apply (norm_mul_le ..).trans (mul_le_mul ((norm_mul_le ..).trans (by rw [ha,one_mul]; exact h)) ((trStamp ..).le.trans he) (norm_nonneg _) ((norm_nonneg _).trans h))
 exact (norm_mul_le ..).trans (by rw [trStamp,hb,mul_one]; exact (norm_mul_le ..).trans (mul_le_mul he h (norm_nonneg _) hv))
lemma seat_co (U V:E)(X Y:Stamp){v:ℝ}(h:‖Y‖≤v): ‖motion U X-motion V Y‖ ≤ ‖X-Y‖ +2*xm*cd group U V*v:= (norm_sub_le_norm_sub_add_norm_sub _ (motion U Y) _).trans (add_le_add (motion_frame ..).le (seat_rate _ _ _ h))
lemma seat_norm(U:E)(X:Stamp): ‖motion U X‖=‖X‖:= congr_norm ..
lemma full_o (u:ℝ) (h:0<u) : ∃ q:ℝ,0<q ∧ ∀ (x y:Ballot), Xd x y ≤ q→‖Pair.fullM x.val-Pair.fullM y.val‖≤u := by
 obtain ⟨q,p,Q⟩:= Metric.uniformContinuousOn_iff.mp Pair.full_uniform u h; refine ⟨q/2,half_pos p,fun x y t=>?_⟩; rw [←dist_eq_norm]; exact (Q _ (vote_unit x) _ (vote_unit y) (by rw [dist_eq_norm]; exact (show ‖_‖≤_ from t).trans_lt (half_lt_self p))).le -- tune
end YM.CF.BProof.Hero
