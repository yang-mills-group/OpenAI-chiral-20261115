import YM.SU5.FiniteGaugeData.ArchiveK.Latte
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.ArchiveK
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush Largo WithLp
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
attribute [local instance] opCStarAlgebra
set_option linter.unusedSectionVars false
set_option quotPrecheck false
namespace Violas
open LinearMap Submodule Module
variable {X Y Z J:Type*}[Fintype X][Fintype Y][Fintype Z][DecidableEq X][DecidableEq Y][DecidableEq Z]
lemma ker_size (F:Ket X→ₗ[ℂ] Ket Y): page X ≤ dim (ker F)+ page Y:=by have hv:=finrank_range_add_finrank_ker F; have hb:dim (LinearMap.range F) ≤ page Y:= (Submodule.finrank_le ..).trans_eq finrank_euclideanSpace; rw [finrank_euclideanSpace] at hv; unfold page dim at *; omega
lemma roll_comap (F:Ket X →ₗ[ℂ] Ket Y)(U:PlansM Y) : page X + dim U ≤ dim (U.comap F) + page Y := by
 let f:=mkQ U; let Xκ:= ker (f.comp F); have h:U.comap F = Xκ:=by ext x; change F x∈ U↔ f (F x)=0; simp [f] -- tune
 have hp:= Submodule.finrank_quotient_add_finrank U; rw [finrank_euclideanSpace] at hp; let he:= f.comp F; have ht:= he.finrank_range_add_finrank_ker; rw [finrank_euclideanSpace] at ht; have hm:=Submodule.finrank_le (LinearMap.range he); unfold dim; rw [h]; change _≤finrank ℂ (ker he)+_; unfold page; omega
lemma devisor (T:Finset J)(U:PlansM X)(F:J→ Ket X→ₗ[ℂ] Ket Y)(W:J→PlansM Y)(t:ℕ)(p:∀ i∈T, page Y≤dim (W i)+t) :∃ V:PlansM X,V≤U∧ dim U≤ dim V+ t*T.card ∧ ∀ i∈T,V≤Submodule.comap (F i) (W i):=by
 obtain ⟨V,e,h,z⟩:= combine T U (fun i=>Submodule.comap (F i) (W i)) (fun i=>t) (fun i b=> (show page X ≤ dim (Submodule.comap (F i) (W i))+t from (by specialize p i b; have he:=roll_comap (F i) (W i); omega))); exact ⟨V,h,(by simpa [mul_comm] using e),z⟩
lemma ract_in (F:Ruler X Y)(v:Fᴴ*F=1) : Injective (ract F) := Function.LeftInverse.injective (g:=ract Fᴴ) (fun i=>by rw [←Largo.R_mul,v,R_one]) -- tune
lemma ract_orth (F:Ruler X Y)(v:Fᴴ*F=1)(i:Ket Y) : ‖ract F i‖=‖i‖:=by rw [←sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),←gramFee,v]; unfold gas; rw [R_one]; exact inner_self_eq_norm_sq (𝕜:=ℂ) _
lemma ward (P:PlansM X)(n:ℕ)(p:n≤ dim P):∃ M:Ruler X (Fin n), Mᴴ*M=1 ∧ ∀ i:Ket (Fin n),ract M i∈ P:=by
 let e(i:Fin n):= Fin.castLE p i; let f(i:Fin n):= (stdOrthonormalBasis ℂ P (e i)).val; have hb(i j:Fin n): inner ℂ (f i) (f j)= if i=j then 1 else 0:=by change inner ℂ (stdOrthonormalBasis ℂ P (e i)) (stdOrthonormalBasis ℂ P (e j))=_; rw [orthonormal_iff_ite.mp (stdOrthonormalBasis ℂ P).orthonormal]; simp [e]; -- tune
 let M: Ruler X (Fin n):= Matrix.of fun i j=> (f j).ofLp i; have hp(i: Fin n) : ract M (basisKet i)=f i:=by apply PiLp.ext; intro j; rw [R_basis]; rfl
 refine ⟨M,?_,fun i=>?_⟩; · ext i j; rw [← R_basis i j (Mᴴ*M), Matrix.one_apply, ←basis_inner,Largo.R_mul,← adjacent,hp,hp,hb] -- ambiguous
 nth_rw 1 [←basis_expand i]; rw [map_sum]; exact P.sum_mem (fun j _=> by rw [map_smul,hp]; exact P.smul_mem _ (show f j∈ P from Subtype.property _))
lemma ranger(P:PlansM X)(t:∃ f:Ruler X Y,fᴴ*f=1 ∧ ∀ i:Ket Y,ract f i∈ P): page Y≤ dim P:= by obtain ⟨A,p,h⟩:=t; let S: Ket Y →ₗ[ℂ] P:= (ract A).toLinearMap.codRestrict P h; have ht:Injective S:= fun i j v=> ract_in A p (congrArg Subtype.val v); unfold page; rw [← finrank_euclideanSpace (ι:=Y) (𝕜:=ℂ)]; exact finrank_le_finrank_of_injective ht
-- rank of (kernel lim) rectangular. combined.
def found (M:Ruler X Y)(n:ℕ)(z:ℝ):Prop:=∃ P:PlansM Y,n≤dim P∧∀ x∈P,z*‖x‖≤‖ract M x‖
lemma castSense (F: Op X) (W:PlansM X) (n:ℕ)(v:n≤dim W)(a:ℝ)(h:∀ x∈ W,a*‖x‖^2 ≤ gas F x) : found F n a:=by
 refine ⟨W,v,fun x p=>?_⟩; by_cases u:x=0; · subst x; simp
 let V:= ract F x; have ht:gas F x≤ ‖x‖*‖V‖:= (Complex.re_le_norm ..).trans (norm_inner_le_norm ..); refine le_of_mul_le_mul_right ?_ (norm_pos_iff.mpr u); change a*‖x‖*‖x‖ ≤ ‖V‖* ‖x‖; linarith only [h x p,ht]
lemma accrue (M:Ruler X Y)(T:Finset J)(f:J→Ruler Z X)(g:J→Ruler Y Z)(F:Op Z)(H:(∑ i∈T,f i*M*g i)= F)(y b:ℝ)(k:ℕ)(W:PlansM Z)(h: k*T.card<dim W)(e:∀ z∈W,y*‖z‖ ≤ ‖ract F z‖)(v:0≤b)(p:(∑ i∈T,‖f i‖*b*‖g i‖)< y) : found M k b:=by
 obtain ⟨U,L,x,u,t⟩:= frigo M b v; by_cases he:k≤dim U; · exact ⟨U,he,u⟩
 push Not at he; obtain ⟨V,a,j,Y⟩:= devisor T W (fun i=> (ract (g i)).toLinearMap) (fun i=>L) (dim U) (fun i _=> le_of_eq (by rw [←x,add_comm])); obtain ⟨w,hw,r⟩:=fees V (by have hu:= Nat.mul_le_mul_right T.card he.le; omega)
 exfalso; have hz:∀ i∈T,‖ract M (ract (g i) w)‖ ≤ b*‖g i‖*‖w‖:= fun i b'=> (t _ (Y i b' hw)).trans ((mul_le_mul_of_nonneg_left (R_cost ..) v).trans_eq (mul_assoc _ _ _).symm); have hp: ‖ract F w‖ ≤ (∑ i∈ T,‖f i‖*b*‖g i‖)*‖w‖ := by rw [←H,map_sum,ContinuousLinearMap.sum_apply,Finset.sum_mul]; refine (norm_sum_le ..).trans (sum_le_sum fun i t=>?_); rw [Largo.R_mul,Largo.R_mul]; exact (R_cost ..).trans ((mul_le_mul_of_nonneg_left (hz i t) (norm_nonneg _)).trans_eq (by ring))
 exact not_lt_of_ge ((e w (a hw)).trans hp) (mul_lt_mul_of_pos_right p (norm_pos_iff.mpr r))
#print axioms accrue
end Violas
end YM.CF.Window.ArchiveK
