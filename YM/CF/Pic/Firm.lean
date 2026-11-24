import YM.CF.Pic.Realm
import YM.CF.Sods.Knot
import YM.Push.STATIONARY_UNIFORM.FrameMin
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pic
open Function Filter Metric Finset NormedSpace Lattice Laurent Kea Lat Fir Tulip Rush Cube Jill Ember SU Dial Thera Fock Peaks Cascade Flare Scroll Spire Sods
open scoped Topology BigOperators Matrix MatrixOrder ContDiff InnerProductSpace NNReal
local notation "G"=> SU.group
open scoped Matrix.Norms.Frobenius in
lemma zeta:∃ C:ℝ,0<C∧∀ (u:E)(k:ℝ), (∀ i j, ‖fund u i j-(1:Op SU.F) i j‖≤k)→ SU.group.chord u≤ C*k:=by
 refine ⟨5/Real.sqrt SU.group.repDim,div_pos (by norm_num) SU.group.colorScale_pos,fun u k h=>?_⟩; have hp:0≤k:=(norm_nonneg _).trans (h 0 0)
 unfold Gauge.chord; rw [div_mul_eq_mul_div]; apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _); let A:=fund u-1; change ‖A‖≤ 5*k; apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).1;
 rw [Gauge.frob_sq]; unfold Matrix.trace; simp_rw [Complex.re_sum,Matrix.diag_apply,Matrix.mul_apply,Complex.re_sum]
 refine (sum_le_sum (g:=fun _=>∑ _:SU.F,k^2) fun i _=> sum_le_sum (fun j _=>?_)).trans_eq (by simp [SU.F]; ring); rw [show star A j i = (starRingEnd ℂ) (A i j) from rfl]; change (A i j *star (A i j)).re ≤ _; rw [show (A i j *star (A i j)).re= _ from inner_self_eq_norm_sq (𝕜:=ℂ) (A i j)]; exact pow_le_pow_left₀ (norm_nonneg _) (h i j) _
open scoped Matrix.Norms.Frobenius in
lemma helio(i j:SU.F):ContDiff ℝ 1 (fun x:SU.group.Color=> fund (SU.group.lieExp x) i j):=by
 let L:SU.group.Mat→ₗ[ℝ]ℂ:=⟨⟨fun x=>x i j, fun x y=>rfl⟩,fun x y=>rfl⟩; exact L.toContinuousLinearMap.contDiff.comp (SU.group.exp_jet.of_le le_top)
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
lemma glow:∃ C δ:ℝ,0<C∧0<δ∧∀ (g:E)(p:ℝ),p≤δ→‖fund g-1‖ ≤ p→∃ x:SU.group.Color,SU.group.lieExp x=g ∧ ‖x‖≤ C*p:=by
 obtain ⟨C,d,x,v,V⟩:= Push.Uniform.log_receipt G; obtain ⟨b,g,B⟩:=zeta
 refine ⟨C*b,d/b,mul_pos x g,div_pos v g,fun u p l h=>?_⟩; have hp:=B u p fun i j=> (norm_entry _ i j).trans h; obtain ⟨t,k⟩:=V u (le_trans hp (by rw [mul_comm]; exact (_root_.le_div_iff₀ g).mp l)); exact ⟨_,t,(k.trans (mul_le_mul_of_nonneg_left hp x.le)).trans_eq (by ring)⟩
lemma gulf:∃ C:ℝ,1≤C ∧ ∀ u v:E,Cube.cmp matter u v≤ C * Cube.cmp firstF u v:=by obtain ⟨c,g,Gh⟩:= Sods.opt _ (show ContDiff ℝ 1 triple from Jet.trie); refine ⟨max c 1,le_max_right ..,fun u v=>?_⟩; exact le_trans (Gh u.val v.val) (mul_le_mul_of_nonneg_right (le_max_left ..) (norm_nonneg _))
open CF.Jet
lemma view_b : ContDiff ℝ 1 (fund ∘ SU.group.lieExp):= matt fun i j=> helio i j
lemma town {x y p:ℝ} {F:Type}[NormedAddCommGroup F][NormedSpace ℝ F](f:ℝ→ F)(X:Set ℝ)(g:Convex ℝ X)(h:x∈X)(k:y∈X)(q:∀ x∈X, Jet.Allows 1 f x p): ‖f x-f y‖ ≤ p * |x-y|:=by
 apply g.norm_image_sub_le_of_norm_fderiv_le (fun x p=> (q x p).smooth.differentiableAt (by simp)) _ k h; intro x p; rw [← norm_iteratedFDeriv_one]; exact (q x p).norm_le 1 le_rfl
lemma servo(C:ℝ)(hC:1 ≤ C):∃ T:ℝ,1 ≤ T∧ ∀ u:E,∀ v:SU.group.Color,‖v‖≤C→∀ z:ℝ,|z|≤1→ Allows 1 (fun i:ℝ=> fund (SU.group.lieExp (i • v)*u)) z T:=by
 obtain ⟨A,h,H⟩:= payment_for 1 (S:=closedBall 0 C) (isCompact_closedBall ..) _ (fun i _=>view_b.contDiffAt); let m:= ContinuousLinearMap.mul ℝ (Op SU.F); let T:=2*‖m‖*composeCost 1 A C; refine ⟨max T 1,le_max_right ..,fun u v q z r=>?_⟩
 let L:=ContinuousLinearMap.toSpanSingleton ℝ v; have hp:‖L‖≤C:=by simpa [L] using q
 have he:‖L z‖≤C:= (L.le_opNorm _).trans ((mul_le_mul hp r (norm_nonneg z) (zero_le_one.trans hC)).trans_eq (mul_one _)); have ht:=H (L z) (mem_closedBall_zero_iff.mpr he); have hx:= (ht.comp (f:=L) (allows_linear hp he)).bilinear m (allows_const z (show ‖fund u‖≤1 from (tone u.val).le)) le_rfl; rw [pow_one,mul_one] at hx
 apply Allows.mono (C:=T) _ (le_max_left ..); change Allows _ _ _ T at hx; exact hx
end YM.CF.Pic
