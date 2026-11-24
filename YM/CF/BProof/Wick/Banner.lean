import YM.CF.BProof.Wick.Melt
import YM.CF.BProof.Align.Ins
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! prop:B-bra real log split. Two determinants paid at projected endpoint. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Wick
open Function Filter NormedSpace Fock Thera Finset Branch Align
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type*}[Fintype I][LinearOrder I] {A P Q: Op I} {c:ℝ}
lemma detAccept (p:IsStarProjection P)(q:IsStarProjection Q)(h:P.trace=Q.trace): (P*Q*P+(1-P)).det=(Q*P*Q+(1-Q)).det:=by
 obtain ⟨n,V,W⟩: ∃ n:ℕ,P.trace=(n:ℂ)∧Q.trace=(n:ℂ) :=by obtain ⟨V,S,t⟩:= spot_projection P p; use S.card; rw [←h,t,trace_twist,trace_cut]; exact ⟨rfl,rfl⟩
 let f(A B:Op I)(t:ℂ):=1+(t-1) • A + A*B*A
 have he {A B:Op I}(k:IsStarProjection A)(x:ℂ)(g:x≠0) (u:A.trace=n): (f A B x).det = x^n * (1+x⁻¹ • (A*B*A)).det :=by
    rw [show f A B x=(1+(x-1) • A)*(1+x⁻¹ • (A*B*A)) from ?_,Matrix.det_mul,det_rank (p:=k) n u,add_sub_cancel 1 x]; unfold f; rw [mul_add,mul_one,add_mul,one_mul,Algebra.mul_smul_comm,Algebra.smul_mul_assoc,←mul_assoc A,←mul_assoc A,k.isIdempotentElem,x |> fun _=>smul_smul x⁻¹,show x⁻¹*(x-1)=1-x⁻¹ from (by field_simp)]; rw [sub_smul (1:ℂ) (x⁻¹),one_smul]; abel
 let g(A B:Op I)(x:ℂ):=(f A B x).det; have ht(A B:Op I) : Continuous (g A B):=by unfold g f; fun_prop
 have hy{A B:Op I}(p:IsStarProjection A)(q:IsStarProjection B): A*B*A=(A*B)*(B*A):=by rw [←mul_assoc, mul_assoc A B B,q.isIdempotentElem]
 have hx:g P Q 0=g Q P 0:= by
   apply tendsto_nhds_unique_of_eventuallyEq ((ht P Q).continuousWithinAt (x:=0) (s:={0}ᶜ)) ((ht Q P).continuousWithinAt ..); filter_upwards [self_mem_nhdsWithin] with x hx; unfold g; rw [he p x hx V,he q x hx W,hy p q,hy q p,← Algebra.smul_mul_assoc,← Algebra.mul_smul_comm x⁻¹ (Q*P) (P*Q),Matrix.det_one_add_mul_comm]
 simpa [f,g,sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using hx
lemma detRoom [Nonempty I] (b:Board A P Q c): (entered A (house A P Q 0)).det =(hutch A P).det * (hutch (1-wedgeQ A P) Q).det:=by
 let V:= wedgeP A P; let W:=wedgeQ A P; let L:= space P Q
 have hu(i j:Op I)(p:IsStarProjection i)(q:IsStarProjection j): star (i*j)*(i*j)= j*i*j:=by rw [star_mul,q.isSelfAdjoint,p.isSelfAdjoint,←mul_assoc,mul_assoc j i i,p.isIdempotentElem]
 have hv :star (P*V)*(L*W)=0:=by rw [star_mul, show star P=P from b.p.isSelfAdjoint.star_eq,mul_assoc,← mul_assoc P,show P*L=0 from b.pw]; simp
 have ha : star (house A P Q 0)*house A P Q 0= V*P*V+W*L*W:=by
   have ht:star (L*W)*(P*V)=0:=by rw [← show star (star (P*V))=P*V from star_star _,←star_mul,hv,star_zero]
   rw [b.slot0,star_add,add_mul,mul_add,mul_add, hv, ht,zero_add,add_zero,hu _ _ b.p b.drawn,hu _ _ b.wall b.leaves]
 have hg:W*L*W=W-W*Q*W:= by unfold L space; rw [mul_sub,mul_one,sub_mul,mul_add W, show W*P=0 from b.rimRight,zero_add,show W*W=W from b.leaves.isIdempotentElem]
 let E:= V*P*V; let S:=W*Q*W
 have he : entered A (house A P Q 0)=(E+(1-V))*(1-S):=by
   rw [entered,ha,hg]; have hx : V*S=0:=by unfold S; rw [←mul_assoc,←mul_assoc,show V*W=0 from b.apartR]; simp
   rw [mul_sub,mul_one,add_mul,sub_mul,one_mul,show E*S=0 from (by unfold E; rw [mul_assoc (V*P),hx,mul_zero]),hx, ←show V+W=A from b.bins]; abel
 rw [he,Matrix.det_mul,detAccept b.drawn b.p b.tE] -- tune unfold E V
 rw [show P*V*P=P*A*P from (by rw [mul_assoc,show V*P=A*P from b.shadow, ←mul_assoc]),show hutch (1-W) Q=1-Q*W*Q from by unfold hutch; rw [mul_sub,mul_one,sub_mul,b.q.isIdempotentElem]; abel]; congr 1
 have ht : Q*W*Q=(Q*W)*(W*Q):=by rw [←mul_assoc, mul_assoc Q W W, show W*W=W from b.leaves.isIdempotentElem]
 unfold S; rw [show W*Q*W=(W*Q)*(Q*W) from (by rw [← mul_assoc,mul_assoc W Q Q, b.q.isIdempotentElem]), Matrix.det_one_sub_mul_comm,←ht]
end YM.CF.BProof.Wick
