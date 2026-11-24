import YM.SU5.FiniteGaugeData.Largo.Track
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option maxHeartbeats 320000
noncomputable section
namespace YM.CF.Window.Largo
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
/-! rectangular projection interfaces, DL discounts -/
variable {X Y Z A:Type*}{i:X}{j:Y}{k:Z}[DecidableEq X][DecidableEq Y][DecidableEq Z][DecidableEq A][Fintype X][Fintype Y][Fintype Z][Fintype A]
abbrev Ruler(X Y:Type*):= Matrix X Y ℂ -- not square,
variable {δ C:ℝ}
set_option linter.unusedSectionVars false
lemma compass (M:Ruler X Y)(S:Finset X)(i j): (cutM S*M) i j= if i∈ S then M i j else 0:=by by_cases h:i∈S <;> simp [cutM,Matrix.diagonal_mul,h]
lemma compass' (M:Ruler X Y)(S:Finset Y)(i j): (M*cutM S) i j= if j∈ S then M i j else 0:=by by_cases h:j∈S <;> simp [cutM,Matrix.mul_diagonal,h]
lemma cutM_hold(S V:Finset X) : cutM S * cutM V=cutM (S∩V):=by ext i j; rw [compass]; by_cases h:i=j <;> by_cases h':i∈ S <;> by_cases b:i∈V <;> simp_all [cutM]
lemma cutM_com(S V:Finset X): Commute (cutM S) (cutM V):=by unfold Commute SemiconjBy; rw [cutM_hold,cutM_hold,inter_comm]
lemma cutM_read' (S:Finset X) : cutM S+cutM Sᶜ=1 := by ext i j; by_cases h:i=j <;> by_cases h':i∈ S <;> simp_all [cutM,Matrix.one_apply]
lemma cutM_adj(S:Finset X): (cutM S)ᴴ=cutM S:=(cutM_idp _).2
lemma cutM_patch(S T:Finset X)(h:S⊆T)(M:Ruler X Y)(Z:cutM S*M=M):cutM T*M=M:=by nth_rw 1 [←Z]; rw [←Matrix.mul_assoc,cutM_hold,inter_eq_right.mpr h,Z]
-- norm across rectangular cuts. Finrank separately
local notation "ρ" x:max=> ‖x‖
lemma cutBud (S:Finset X): ‖cutM S‖ ≤ 1:= ((cutM_idp _).norm_le _) -- expects Nonempty
variable {S:Finset X}{M:Ruler X Y}
lemma cutBudL : ‖cutM S*M‖ ≤ ‖M‖:= (Matrix.l2_opNorm_mul ..).trans (mul_le_of_le_one_left (norm_nonneg _) (cutBud _))
variable {T:Finset Y}
lemma cutBudR : ‖M*cutM T‖ ≤ ‖M‖:= (Matrix.l2_opNorm_mul ..).trans (mul_le_of_le_one_right (norm_nonneg _) (cutBud _))
lemma cutP_com (S T:Finset X): S ⊆ T → cutM Tᶜ*cutM S=0:=by
 intro h; rw [cutM_hold]; ext i j; by_cases t:i∈S <;> simp [t,(show ∀ i,i∈S→i∈T from fun i=> @h i),cutM,Matrix.diagonal_apply] -- tune
-- Rect selection
abbrev PCLM (X Y:Type*) [Fintype X][Fintype Y]:= Ket Y →L[ℂ] Ket X
abbrev ract: Ruler X Y ≃ₗ[ℂ] PCLM X Y:= (Matrix.toEuclideanLin (𝕜:=ℂ)).trans LinearMap.toContinuousLinearMap
lemma R_at (M:Ruler X Y) (x:Ket Y) (i): (ract M x).ofLp i=(M *ᵥ x.ofLp) i:=rfl
lemma R_basis(i:X)(j:Y)(M:Ruler X Y): (ract M (basisKet j)).ofLp i=M i j:=by rw [R_at]; simp
lemma R_one (x:Ket X): ract (1:Op X) x=x:=act_one _
lemma R_pay (M:Ruler X Y): ‖ract M‖=‖M‖:=rfl
lemma R_mul(M:Ruler X Y)(F:Ruler Y Z)(x:Ket Z): ract (M*F) x=ract M (ract F x):=by apply PiLp.ext; intro i; rw [R_at,R_at,←Matrix.mulVec_mulVec]; rfl
lemma R_adj(M:Ruler X Y)(x:Ket X)(y:Ket Y) : inner ℂ (ract Mᴴ x) y=inner ℂ x (ract M y):=by
 -- mathlib linearIn
 change inner ℂ ((Matrix.toEuclideanLin (𝕜:=ℂ) Mᴴ) x) y= _ -- tune
 rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]; apply LinearMap.adjoint_inner_left
lemma R_cost(A:Ruler X Y)(x:Ket Y): ‖ract A x‖ ≤ ‖A‖ * ‖x‖ := (ract A).le_opNorm _
-- disjoint max (adapted from Brique Cellar for lack of LinearOrder).
lemma cutSpan_comm (A:Op X)(Q:Finset X)(t:∀ i j:X, A i j ≠ 0→ (i∈Q ↔ j∈Q)): Commute (cutM Q) A:=by
 change _*_= _*_; ext i j; rw [compass,compass']; by_cases h:A i j=0; simp [h]; simp [t _ _ h]
lemma lumpC (V: Finset X)(h:Disjoint S V): cutM (S∪V)=cutM S+cutM V:=by
 ext i j; by_cases h:i=j; · subst j; rename_i h; by_cases b:i∈ S <;> by_cases z:i∈V <;> simp [cutM,z,b]; exact (Finset.disjoint_left.mp h b z).elim
 simp [cutM,h]
lemma coast (C D: Ruler X Y)(h:cutM S*C=C)(T:Finset X)(z:cutM T*D=D)(a:Disjoint S T): Cᴴ*D=0:=by
 have he:Cᴴ*cutM S=Cᴴ:=by nth_rw 1 [←cutM_adj S]; rw [←Matrix.conjTranspose_mul,h]
 rw [←he, Matrix.mul_assoc]; nth_rw 1 [←z]; rw [←Matrix.mul_assoc (cutM S),cutM_hold,disjoint_iff_inter_eq_empty.mp a, show _root_.YM.CF.Fock.cutM (∅:Finset X)=0 from (by ext; simp [cutM]), Matrix.zero_mul,Matrix.mul_zero]
lemma pythL (A B:Ruler X Y)(h: Aᴴ*B=0)(x:Ket Y) : ‖ract (A+B) x‖^2= ‖ract A x‖^2 + ‖ract B x‖^2:=by
 simp only [map_add, ContinuousLinearMap.add_apply,sq]; apply norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜:=ℂ); nth_rw 1 [←Matrix.conjTranspose_conjTranspose A]; rw [R_adj,← R_mul,h,map_zero, ContinuousLinearMap.zero_apply,inner_zero_right]
lemma coastPay (C D:Ruler X Y)(s V:Finset X)(v T:Finset Y)(p:cutM s*C=C)(q: C*cutM v=C)(t:cutM V*D=D)(r:D*cutM T=D)(hp:Disjoint s V)(g:Disjoint v T)(u:‖C‖≤δ)(e:‖D‖≤δ): ‖C+D‖ ≤ δ:=by
 have he:0≤δ:=(norm_nonneg _).trans u; rw [← R_pay]; apply ContinuousLinearMap.opNorm_le_bound _ he; intro i; have hx:‖ract (C+D) i‖^2=‖ract C i‖^2+‖ract D i‖^2:=pythL _ _ (coast C D p V t hp) i
 let a:= cutM v; let b:= cutM T; have hk:‖ract a i‖^2+‖ract b i‖^2≤‖i‖^2:=by
    rw [←pythL a b ?_, ← lumpC T g]; swap; · exact (coast a b (cutM_idp v).1 T (cutM_idp T).1 g)
    exact pow_le_pow_left₀ (norm_nonneg _) ((R_cost ..).trans (mul_le_of_le_one_left (norm_nonneg _) (cutBud _))) _
 have htt (A:Ruler X Y)(t:Finset Y)(q:A*cutM t=A)(u:‖A‖≤δ): ‖ract A i‖^2≤δ^2* ‖ract (cutM t) i‖^2:=by
    nth_rw 1 [←q]; rw [R_mul,←mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) ((R_cost ..).trans (mul_le_mul_of_nonneg_right u (norm_nonneg _))) _
 rw [←sq_le_sq₀ (norm_nonneg _) (by positivity),hx,mul_pow]; exact (add_le_add (htt C v q u) (htt D T r e)).trans (by rw [←mul_add]; exact mul_le_mul_of_nonneg_left hk (sq_nonneg _))
lemma coast_sumPay (C:A→Ruler X Y) (Q:A→Finset X)(T:A→Finset Y) (z:0≤δ) (V:Finset A)
  (p:Pairwise (Function.onFun Disjoint Q))(h:Pairwise (Function.onFun Disjoint T)) (c:∀ i∈V, cutM (Q i)*C i=C i)(g:∀ i∈V, C i * cutM (T i)=C i)(w:∀ i∈V,‖C i‖≤δ): ‖∑ i∈ V,C i‖≤δ:=by
 induction V using Finset.induction with
 | empty=> rw [sum_empty,norm_zero]; exact z
 | insert i V v ih=>
    have hl(A:A)(a:A∈V):A∈insert i V:=mem_insert_of_mem a -- shadow
    rw [sum_insert v]; apply coastPay _ _ (Q i) (V.biUnion Q) (T i) (V.biUnion T) (c _ (mem_insert_self ..)) (g _ (mem_insert_self ..)) _ _ _ _ (w _ (mem_insert_self ..)) (ih (fun i t=> c i (hl _ t)) (fun i t=>g i (hl _ t)) (fun i t=>w i (hl _ t)))
    · rw [Matrix.mul_sum]; exact sum_congr rfl fun j e=> cutM_patch (Q j) _ (subset_biUnion_of_mem _ e) _ (c _ (hl j e))
    · rw [Matrix.sum_mul]; refine sum_congr rfl fun j e=>?_ ; let S:= cutM (T j); nth_rw 1 [←g j (hl j e)]; rw [Matrix.mul_assoc,cutM_hold, inter_eq_left.mpr (subset_biUnion_of_mem _ e),g _ (hl j e)]
    · exact (disjoint_biUnion_right ..).mpr fun j e=> p (show i≠j from ne_of_mem_of_not_mem e v |>.symm)
    exact (disjoint_biUnion_right ..).mpr fun j e=> h (show i≠j from ne_of_mem_of_not_mem e v |>.symm)
-- pickV: even seam purchases represented by w.
def grip (f:Y→X)(c:Y→ℂ): Ruler X Y:= Matrix.of fun i j=> if i=f j then c j else 0
lemma on_grip (f:Y→X) (c:Y→ℂ)(M:Ruler Z X)(i j): (M*grip f c) i j=M i (f j)*c j:=by simp [Matrix.mul_apply,grip,mul_ite]
lemma grip_off (f:Y→X)(c:Y→ℂ)(M:Ruler X Z)(i j): ((grip f c)ᴴ*M) i j=star (c i) * M (f i) j:=by simp [Matrix.mul_apply,Matrix.conjTranspose_apply, grip, apply_ite star,ite_mul]
lemma grip_clean (f:Y→X)(c:Y→ℂ)(h:Injective f)(p:∀ i,star (c i)*c i=1): (grip f c)ᴴ*grip f c=1:=by
 ext i j; rw [grip_off]; by_cases t:i=j; · subst j; rw [grip,Matrix.of_apply,if_pos rfl,p,Matrix.one_apply_eq];
 simp [grip, h.eq_iff, t]
lemma grip_pay (M:Ruler X Y)(t:Mᴴ*M=1): ‖M‖ ≤ 1:=by
 rcases isEmpty_or_nonempty Y with h|h; · rw [Subsingleton.elim M 0,norm_zero]; exact zero_le_one
 have he:= Matrix.l2_opNorm_conjTranspose_mul_self M; rw [t,norm_one] at he; nlinarith only [he,norm_nonneg M]
lemma grip_in (f:Y→X)(c:Y→ℂ)(S:Finset X)(p:∀ i,f i∈S): cutM S *grip f c=grip f c:=by ext i j; rw [compass]; by_cases h:i=f j <;> simp [grip,h,p]
end YM.CF.Window.Largo
