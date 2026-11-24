import YM.CF.BPress.Vesper.Canister
import YM.CF.BPress.Pine.Cabin
/-! Ordered outer Wick contractions. Left and Right words use separate grassmann rings. Vertex arithmetic uses commutative rings separately; no passage R→L in true Wick evaluation. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Vesper
open Function Filter NormedSpace MeasureTheory Finset Lattice Branch Push.AbsoluteSums Gas Palmer Fock Pastry Pine Pf
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
variable {K I:Type}[LinearOrder K][Fintype K][Nonempty K][LinearOrder I][Fintype I][Nonempty I]
variable {J : Type}[LinearOrder J][Fintype J][Nonempty J]
variable {B D F Y:Type}[Fintype B][DecidableEq B][Fintype D][DecidableEq D][Fintype F][DecidableEq F][Fintype Y][DecidableEq Y]{S:Branch.Field Y}
def batch (q:ℂ)(l: List I)(h:Even l.length): Dough I:=⟨q • raw l,(lifted l h).1.smul q⟩
lemma glyph_word(L:Poly I K)(l:List I)(h:Even l.length): L.eval (raw l)=(l.map L.term).prod:=by
 generalize z:l.length=n; induction n using Nat.strong_induction_on generalizing l with|h n ih=>
    rcases l with (_|⟨i,t⟩); exact L.eval_one; rcases t with (_|⟨j,t⟩); simp at h
    have ht:Even t.length:=by rw [Nat.even_iff] at h ⊢; rw [List.length_cons,List.length_cons] at h; omega
    obtain ⟨_,v⟩:=lifted t ht; let y:Dough I:=⟨put i*put j,Flour.putPut univ (mem_univ i) (mem_univ j)⟩; rw [List.length_cons,List.length_cons] at z; rw [show raw (i::j::t)=y.val*raw t from (mul_assoc ..).symm, L.eval_mul y (⟨_,(lifted t ht).1⟩:Dough I), show L.eval y.val=_ from L.eval_double i j, ih _ (by omega : t.length<n) t ht rfl,mul_assoc]; rfl
lemma sow (L:Poly I K)(q:ℂ)(l: List I)(h:Even l.length): L.cook (batch q l h)=q • (l.map L.term).prod:=by change L.eval (q • _)=_; rw [map_smul, glyph_word L l h]
structure Leaves (I D:Type) where
 band:D→List I
 e:∀ i,Even (band i).length
 n:∀ i,(band i).Nodup
 rule:D→D→Prop
namespace Leaves
variable (L:Leaves I D)(T:Poly I K)(u:D→ℂ)
-- total values
abbrev textP(l:List D):= (l.map L.band).flatten
abbrev cake(i:D):= batch (u i) (L.band i) (L.e i)
lemma logic (p:Finset D)(l: List D)(h:Story.lives p l): T.cook (∏ i∈p,cake L u i)=(∏ i∈p,u i) • ((L.textP l).map T.term).prod:=by
 rw [← h.1,List.prod_toFinset _ h.2,List.prod_toFinset _ h.2,map_list_prod]; clear h; induction l with|nil=> simp [textP]|cons i l ih=> rw [textP]; simp only [List.map_cons,List.flatten_cons,List.map_append,List.prod_append,List.prod_cons,cake,sow]; rw [ih, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul]; rw [mul_comm ((l.map u).prod)] -- tune
abbrev snow : Dough I:= box L.rule (cake L u)
end Leaves
end YM.CF.BPress.Vesper
