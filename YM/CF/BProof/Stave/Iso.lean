/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Matter.Rep
import YM.Gauge.Colors
-- Basic norms for the eq:fd-V proof. **FROBENIUS**
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mesh.Stave
open Function Filter Topology Set NormedSpace -- Matrix ?
open scoped Matrix Matrix.Norms.Frobenius Topology BigOperators ComplexConjugate Classical
variable {I J K:Type*}[Fintype I][Fintype J][Fintype K]
abbrev plate(I:Type*) := Matrix I (Fin 5) ℂ
abbrev King(I:Type*)[Fintype I] := {A:plate I | Aᴴ*A=1}
lemma size_L (A:Matrix I J ℂ): ‖A‖^2=(A*Aᴴ).trace.re:=by
 rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt]
 swap; · simp_rw [Real.rpow_two]; exact Finset.sum_nonneg fun _ _=> Finset.sum_nonneg fun _ _=>sq_nonneg _
 simp_rw [Real.rpow_two, Matrix.trace, Complex.re_sum, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum, Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
lemma size_R (A:Matrix I J ℂ): ‖A‖^2=(Aᴴ*A).trace.re:= by rw [size_L,Matrix.trace_mul_comm]
lemma size_HH (A:Matrix I J ℂ): ‖Aᴴ‖=‖A‖:=by rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),size_L,size_R,Matrix.conjTranspose_conjTranspose]
lemma size_mul [DecidableEq J] {A:Matrix I J ℂ}(h:Aᴴ*A=1)(B:Matrix J K ℂ): ‖A*B‖=‖B‖:=by rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),size_R,size_R, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ A B,h,Matrix.one_mul]
lemma mul_size [DecidableEq J] {A:Matrix J I ℂ}(h:A*Aᴴ=1)(B:Matrix K J ℂ): ‖B*A‖=‖B‖:=by rw [← size_HH,Matrix.conjTranspose_mul,size_mul (by rw [Matrix.conjTranspose_conjTranspose]; exact h),size_HH]
lemma G_size {A:plate I}(h:A∈ King I): ‖A‖=SU.group.colorScale:=by rw [←sq_eq_sq₀ (norm_nonneg _) SU.group.colorScale_pos.le,size_R,show Aᴴ * A=1 from h, Matrix.trace_one,SU.group.colorScale_sq]; rw [Fintype.card_fin]; rfl
lemma king_le {A:plate I}(h:A∈ King I): ‖A‖≤3:= by rw [G_size h]; have hm:=SU.group.colorScale_sq; change _=(↑(5:ℕ):ℝ) at hm; norm_num at hm; nlinarith
lemma unit_su (g:SU.E) : SU.fund g ∈ King (Fin 5):= SU.group.mat_star_mul _
lemma compact_F (I:Type*)[Fintype I] : IsCompact (King I) := by
 letI : ProperSpace (plate I) := FiniteDimensional.proper ℂ _
 refine (isCompact_closedBall 0 3).of_isClosed_subset ?_ (fun x hx=> ?_)
 · refine isClosed_eq (show Continuous (fun A:plate I=>Aᴴ*A) from ?_) continuous_const
   apply continuous_matrix; intro i j; simp only [Matrix.mul_apply,Matrix.conjTranspose_apply]; fun_prop
 rw [Metric.mem_closedBall,dist_zero_right]; exact king_le hx

/-- Right SU action on ambient -/
def roll (A:plate I) (u:SU.E): plate I:= A * SU.fund u
@[simp] lemma roll_size (A:plate I)(u:SU.E): ‖roll A u‖=‖A‖:= mul_size ((show SU.fund u * (SU.fund u)ᴴ=1 from SU.group.mat_mul_star u)) _
omit [Fintype I] in
lemma roll_sub (A B:plate I)(u:SU.E): roll A u-roll B u=roll (A-B) u:=(Matrix.sub_mul ..).symm
@[simp] lemma roll_dist(A B:plate I)(u:SU.E): dist (roll A u) (roll B u)=dist A B:=by rw [dist_eq_norm,roll_sub,roll_size,dist_eq_norm]
omit [Fintype I] in
@[simp] lemma roll_mul(A:plate I)(g h:SU.E): roll (roll A g) h= roll A (g*h):=by rw [roll,roll,roll,SU.fund_mul,Matrix.mul_assoc]
omit [Fintype I] in
@[simp] lemma roll_one(A:plate I):roll A 1=A:=Matrix.mul_one _
lemma king_roll{A:plate I}(h:A∈ King I)(u:SU.E):roll A u∈ King I:=by
 change (A*SU.fund u)ᴴ *(A*SU.fund u)=1; rw [Matrix.conjTranspose_mul,Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, show Aᴴ*A=1 from h,Matrix.one_mul]; exact SU.group.mat_star_mul _ -- code
/-- even for not quite isometric -/
def Like(d:ℝ)(A B:plate I):=∃ u,dist (roll A u) B≤d
lemma Like.symm{d:ℝ}{A B:plate I}(h:Like d A B): Like d B A:=by
 obtain ⟨u,h⟩:=h; refine ⟨u⁻¹,?_⟩; rw [← roll_dist _ _ u,roll_mul, inv_mul_cancel, roll_one,dist_comm]; exact h
lemma Like.trans{d e:ℝ}{A B C:plate I}(h:Like d A B)(g:Like e B C):Like (d+e) A C:=by
 obtain ⟨u,h⟩:=h; obtain ⟨v,g⟩:=g; refine ⟨u*v,(dist_triangle _ (roll B v) _).trans (add_le_add ?_ g)⟩; rw [← roll_mul,roll_dist]; exact h
lemma Like.weaken {d e:ℝ}{A B:plate I}(h:Like d A B)(g:d≤e):Like e A B:=⟨_,h.choose_spec.trans g⟩
lemma Like.starts {d:ℝ}{A B:plate I}(h:dist A B≤d):Like d A B:=⟨1,by rwa [roll_one]⟩
lemma size_like {d:ℝ}{A B:plate I}(h:Like d A B) (g:A∈King I): ‖B‖≤3+d:=by
 obtain ⟨u,h⟩:=h; rw [dist_comm,dist_eq_norm] at h; exact (norm_le_norm_sub_add _ (roll A u)).trans ((add_le_add h (king_le (king_roll g _))).trans_eq (add_comm ..))
end YM.CF.BProof.Mesh.Stave
