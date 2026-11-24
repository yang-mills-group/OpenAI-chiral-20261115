import YM.CF.BProof.Align.Ins
/-! Algebra of anti-intertwining, including free-case comparisons not unit preserving. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Align
open Function Filter Fock Finset Branch
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type*}[Fintype I][DecidableEq I]{A P Q C:Op I}
abbrev Twig (C A:Op I):Prop:= A*C=C*cc A
namespace Twig
lemma one (C:Op I): Twig C 1:=by simp [Twig]
lemma sub (h:Twig C A)(p:Twig C P):Twig C (A-P):= by simp only [Twig, sub_mul,cc_sub,mul_sub,h,p]
lemma add (h:Twig C A)(p:Twig C P):Twig C (A+P):=by simp only [Twig,add_mul,cc_add,mul_add,h,p]
lemma mul (h:Twig C A)(p:Twig C P):Twig C (A*P):=by change _=C*cc _; rw [cc_mul,←mul_assoc C,←h,mul_assoc,mul_assoc,p]
lemma smul (h:Twig C A)(p:ℝ): Twig C (p • A):=by simp only [Twig,cc_rsmul,Algebra.mul_smul_comm,Algebra.smul_mul_assoc,h]
lemma inv (h:Twig C A)(p:IsUnit A): Twig C A⁻¹:= by
 have he : cc (A⁻¹)*cc A=1 ∧ cc A * cc (A⁻¹)=1:= by simp only [← cc_mul,(live p).1,(live p).2, cc_one]; tauto
 unfold Twig; rw [← Matrix.inv_eq_left_inv he.1]; exact shiftOn p (live_of he.2) h
end Twig
-- identity tests algebra shared
variable {c:ℝ}[Nonempty I] (b:Board A P Q c)(h:Twig C A)(f:Twig C P)(g:Twig C Q)
include b h f
lemma onWedge : Twig C (wedgeP A P):=by rw [b.wedgePformed]; apply Twig.mul _ (f.mul h); refine (h.mul f).mul (Twig.inv ?_ b.child.active); rw [b.roof]; exact ((f.mul h).mul f).add ((Twig.one C).sub f)
include g
lemma allowHouse (u:ℝ) : Twig C (house A P Q u) ∧ Twig C (star (house A P Q u)) :=by
 let L:=space P Q; let w:=(Twig.one C).sub (f.add g); change Twig C L at w; let S:=L+ u • Q; let T:=P+u • L+u^2 • Q; change Twig C (T*wedgeP A P+S*wedgeQ A P) ∧ Twig C (star (T*wedgeP A P+S*wedgeQ A P)); let y:= onWedge b h f; have hs:= w.add (g.smul u); have hz:Twig C T:=(f.add (w.smul u)).add (g.smul (u^2))
 constructor; exact (hz.mul y).add (hs.mul (h.sub y)); have he : IsSelfAdjoint T:=by unfold T IsSelfAdjoint; rw [star_add,star_add,star_smul,star_smul,star_trivial u,star_trivial (u^2),show star L=L from b.wall.isSelfAdjoint.star_eq,b.p.isSelfAdjoint,b.q.isSelfAdjoint]; -- tune
 rw [star_add,star_mul,star_mul,he.star_eq, b.leaves.isSelfAdjoint, b.drawn.isSelfAdjoint, show star S=S from (by unfold S; rw [star_add,star_smul,star_trivial u,show star L=L from b.wall.isSelfAdjoint.star_eq,b.q.isSelfAdjoint])]; exact (y.mul hz).add ((h.sub y).mul hs)
theorem entersH (u:ℝ)(e:‖u‖≤1): Twig C (floorH A P Q u):=by obtain ⟨prec,H⟩:= allowHouse b h f g u; exact prec.mul ((((H.mul prec).add ((Twig.one C).sub h)).inv (b.houseFit u e).active).mul H)
omit g h b in
lemma shield (bP:IsStarProjection P) : P*C*(1-cc P)=0:=by
 rw [f,mul_assoc,Porth (ccProj bP),mul_zero]
end YM.CF.BProof.Align
