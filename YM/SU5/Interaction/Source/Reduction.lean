import YM.SU5.Interaction.Source.Mixed
import YM.CF.Reed.Play
/- # Source at the left vacuum bra, Eq.(127) -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.StressExchange
open Function Filter Metric Lattice Finset Fock Lat Spire Scroll Drapes Rush Pastry Thera Sault Proa Hest Scree Reed
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
variable {I : Type*} [LinearOrder I] [Fintype I]
variable (A W : Op I)
/-- Bra projection. In particular not just `dg` of physical stencil. -/
def preJ : FC I := Matrix.trace (A*W) • 1+dg (A*W*(1-A))
variable {A}
lemma sandwichV (p:IsStarProjection A)(b:Commute A W)(x:Wave I)(hx:Sea A x): acts (star (dg W)) x=star ((A*W).trace) • x:=by
 have hu:Commute A (star W):=by have ht:=congrArg star b.eq; simp only [star_mul,p.isSelfAdjoint.star_eq] at ht; exact ht.symm
 rw [←dg_star,Sault.loft_v _ hu p x hx]
 congr 1; rw [←Matrix.trace_conjTranspose]; change _ = Matrix.trace (star (A*W)); rw [star_mul,p.isSelfAdjoint,hu.eq]
lemma preserve_part (p:IsStarProjection A): W=preserve A W+A*W*(1-A)+(1-A)*W*A:=by unfold preserve; simp only [mul_sub,sub_mul,one_mul,mul_one]; abel
lemma bra_ann (p:IsStarProjection A)(x:Wave I)(hx:Sea A x):acts (star (dg ((1-A)*W*A))) x=0:=by
 have hu:(1-A)*A=0:=by rw [sub_mul,one_mul,p.isIdempotentElem.eq,sub_self]
 rw [←dg_star,star_mul,star_mul,p.isSelfAdjoint,star_sub,p.isSelfAdjoint,star_one,←mul_assoc,show 1-A=star (1-A) from p.one_sub.isSelfAdjoint.symm,prizeUV,act_sum]
 apply sum_eq_zero; intro i _; rw [act_mul,tars p hx.1, map_zero]; rw [←act_mul,mul_sub,mul_one,p.isIdempotentElem.eq,sub_self,act_zero] -- tune
lemma bra_eq (p:IsStarProjection A)(x: Wave I)(hx:Sea A x):acts (star (dg W)) x=acts (star (preJ A W)) x:=by
 nth_rw 1 [preserve_part W p]; rw [dg_add,dg_add,star_add,star_add,act_add,act_add,sandwichV _ p (preserve_block W p) x hx,bra_ann W p x hx,add_zero,preJ,star_add,act_add,star_smul,star_one,act_smul,act_one,frozen_trace W p] -- frozen_trace S*W, OK
lemma bra_price (p:IsStarProjection A)(x:Wave I)(hx:Sea A x)(y:Wave I): inner ℂ x (acts (preJ A W) y)=inner ℂ x (acts (dg W) y):=by rw [←act_inner,←act_inner,bra_eq W p x hx]

-- Adaptation of Reed.bilinear. Fine sector for preJ on arbitrary cut.
lemma lives_g (V:Op I)(K L:Finset I)(h:cutM K*V=V)(k:V*cutM Kᶜ=V)(p:cutM L*V*cutM L=V) : Fine K L false (dg V) := by
  unfold dg dyad; apply Fine.sumF; intro i _; apply Fine.sumF; intro j _
  by_cases g : V i j=0
  · rw [g,zero_smul]; exact .empty _
  let s:=K; have hi : i∈s := by
    by_contra u; apply g; rw [←h,cutM, Matrix.diagonal_mul, if_neg u,zero_mul] -- occurrence rw←h repeats
  have hj : j∉s := by
    intro l; apply g; nth_rw 1 [←k]; rw [cutM, Matrix.mul_diagonal, if_neg (fun v=> mem_compl.mp v l),mul_zero]
  have he : i∈L ∧ j∈L := by
    by_contra v; apply g; nth_rw 1 [←p]; rw [cutM, Matrix.mul_diagonal, Matrix.diagonal_mul]; split_ifs <;> first | tauto | simp -- N general
  have hp := Fine.seed (s:=s) i he.1; have hq := Fine.seed (s:=s) j he.2
  rw [show (think s).term i=put i from if_pos hi] at hp; rw [show (think s).term j= -takeF j from if_neg hj] at hq
  have hx : Fine s L true (takeF j) := by simpa using hq.scale (-1)
  exact (hp.grow hx).scale _
lemma inSector (K L:Finset I)(h:cutM L*W*cutM L=W) : Fine K L false (preJ (cutM K) W):=by
 let A:=cutM K; let B:=cutM L; have he:A*A=A:= (cutM_idp _).isIdempotentElem; have ht:B*B=B:=(cutM_idp _).isIdempotentElem; have hv:Commute A B:=by change cutM K*_ = cutM L * cutM K; unfold cutM; dsimp only [B,cutM]; rw [Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]; congr 1; ext i; exact mul_comm .. 
 unfold preJ; refine Fine.add ((Fine.one).scale _) (lives_g _ _ _ ?_ ?_ ?_)
 · rw [←mul_assoc,←mul_assoc,he] -- tune
 · rw [dim_cut,mul_assoc _ (1-A), show (1-A)*(1-A)=1-A from (cutM_idp _).one_sub.isIdempotentElem]
 change B*(A*W*(1-A))*B=_; have hp:(1-A)*B=B*(1-A):= ((Commute.one_left B).sub_left hv).eq
 rw [←mul_assoc, ←mul_assoc, ←hv.eq, mul_assoc A B W,mul_assoc _ (1-A) B,hp,←mul_assoc,mul_assoc _ (B*W) B,h]
end YM.CF.StressExchange
