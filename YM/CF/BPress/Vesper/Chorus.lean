import YM.CF.BPress.Vesper.Hearts
/- L before R throughout physical evaluation. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Vesper
open Function Filter NormedSpace MeasureTheory Finset Lattice Branch Push.AbsoluteSums Gas Palmer Fock Pastry Pine Pf Leaves EdgeD
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
variable {K I:Type}[LinearOrder K][Fintype K][Nonempty K][LinearOrder I][Fintype I][Nonempty I]
variable {J : Type}[LinearOrder J][Fintype J][Nonempty J]
variable {B D F Y:Type}[Fintype B][DecidableEq B][Fintype D][DecidableEq D][Fintype F][DecidableEq F][Fintype Y][DecidableEq Y]{S:Branch.Field Y}
-- two species fixed order
abbrev Lens (I J:Type):= I ⊕ₗ J
abbrev leftS (i:I): Lens I J:=toLex (.inl i)
abbrev rightS (j:J): Lens I J:=toLex (.inr j)
abbrev lit {X:Type*}(A:I→X)(B:J→X)(i:Lens I J):X:= Sum.elim A B (ofLex i)
lemma lit_l {X:Type*}(A:I→X)(B:J→X)(i:I): lit A B (leftS i)=A i:= rfl
lemma lit_r {X:Type*}(A:I→X)(B:J→X)(i:J): lit A B (rightS i)=B i:= rfl
lemma lins : Injective (leftS (J:=J) (I:=I)):= toLex.injective.comp Sum.inl_injective
lemma rins : Injective (rightS (I:=I) (J:=J)):= toLex.injective.comp Sum.inr_injective
variable (L: Leaves I D)(R:Leaves J F)
def joinZ: Leaves (Lens I J) (D⊕F) where
 band x := Sum.elim (fun p=>(L.band p).map leftS) (fun p=> (R.band p).map rightS) x
 e x:=by cases x<;>simp [L.e,R.e]
 n x:=by cases x; exact (L.n _).map lins; exact (R.n _).map rins
 rule:= sumR L.rule R.rule
lemma l_r (l:List D): (joinZ L R).textP (l.map .inl)= (L.textP l).map leftS:=by induction l with|nil=>rfl|cons i l ih=> rw [List.map_cons]; unfold textP; simp only [List.map_cons, List.flatten_cons, List.map_append]; exact congrArg ( (L.band i).map leftS ++ · ) ih -- tune
lemma r_r (l:List F): (joinZ L R).textP (l.map .inr)=(R.textP l).map rightS:=by induction l with|nil=>rfl|cons i l ih=> rw [List.map_cons]; unfold textP; simp only [List.map_cons, List.flatten_cons, List.map_append]; exact congrArg ( (R.band i).map rightS ++ · ) ih
abbrev Sworn (p: List I) (s: List J) := p.map (leftS (I:=I) (J:=J)) ++ s.map rightS
variable {E: EdgeD (Lens I J) B Y S}(b:B→ℂ)
structure pays (a c: Wave K)(P:Poly I K)(Q:Poly J K): Prop where
 t (l:List I)(k:List J): wick a c ((l.map P.term).prod*(k.map Q.term).prod)=shape (E.bkg b) (Sworn l k) -- E implicit parameter include? proof
variable {P: Poly I K}{Q: Poly J K}{a c: Wave K}
variable (u:D→ℂ)(v:F→ℂ)(T:Story (D⊕ F) E)
variable (h:T.rule=(joinZ L R).rule) (p:T.word=(joinZ L R).band)(g:pays (E:=E) b a c P Q)
include h p g
lemma total_dual(x:Finset D)(y:Finset F): wick a c (P.cook (tin L.rule (cake L u) x)* Q.cook (tin R.rule (cake R v) y))= T.totalU b (Sum.elim u v) (x.disjSum y) :=by
 have ht:= dual_rule L.rule R.rule x y; have h0: wick a c 0=0:= by simp [wick]
 rw [tin,tin,Story.totalU, h, show (joinZ L R).rule= sumR L.rule R.rule from rfl, ht]
 by_cases f:separated L.rule x <;> by_cases k:separated R.rule y
 pick_goal 4; · simp only [f,k,map_zero,h0, and_false, ↓reduceIte, mul_zero] -- tune
 pick_goal 2; · simp only [f,k,map_zero,h0, and_false, ↓reduceIte, mul_zero]
 pick_goal 2; · simp only [f,k,map_zero,h0, ↓reduceIte, zero_mul,false_and]
 rw [if_pos f,if_pos k,if_pos ⟨f,k⟩]; let l:= x.toList.map (Sum.inl (β:=F)); let m:= y.toList.map (Sum.inr (α:=D)); have hv:T.text (l++m)=Sworn (L.textP x.toList) (R.textP y.toList):=by
    rw [Story.text,p,List.map_append,List.flatten_append, show ((l.map _).flatten)=(L.textP x.toList).map leftS from l_r L R _, show ((m.map _).flatten)=(R.textP y.toList).map rightS from r_r L R _]
 have he : Story.lives (x.disjSum y) (l++m):=by refine ⟨?_ ,?_⟩; ext (i|i)<;> simp [l,m]; rw [List.nodup_append]; refine ⟨?_ ,?_ ,?_ ⟩; exact (Finset.nodup_toList _).map (Sum.inl_injective); exact (Finset.nodup_toList _).map (Sum.inr_injective); intro z h y e p; subst y; obtain ⟨a,_,ha⟩:= List.mem_map.mp h; obtain ⟨b,_,hb⟩:=List.mem_map.mp e; exact Sum.inl_ne_inr (ha.trans hb.symm) -- tune
 rw [L.logic P u x x.toList ⟨by simp, Finset.nodup_toList _⟩, R.logic Q v y y.toList ⟨by simp, Finset.nodup_toList _⟩]; rw [prod_disjSum,← T.projection b _ _ he, hv,←g.t, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, wick.termScale]; simp -- tune
lemma total_duet: wick a c (P.cook (L.snow u)* Q.cook (R.snow v))= T.table b (Sum.elim u v):=by unfold Leaves.snow box Story.table; rw [dual_sum,map_sum,map_sum,sum_mul,wick.termSum]; apply sum_congr rfl; intro x _; rw [mul_sum,wick.termSum]; apply sum_congr rfl; exact fun y _=> total_dual L R b u v T h p g x y
end YM.CF.BPress.Vesper
