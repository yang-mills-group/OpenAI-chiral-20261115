import YM.SU5.Selected.Lantern.Lore
import YM.SU5.Selected.Lantern.Wedges
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
local notation "I"=>Complex.I
open Stencil
variable {n a d f:Type*}[Fintype n][LinearOrder n][Fintype a][DecidableEq a]
-- even commutative algebra `Fine` at global aperture. Density. Used to evaluate polynomial. No aux.
def Honour(S:Finset n) : Subalgebra ℂ (FC n) where
 carrier:={A | Fine S univ false A}
 add_mem' x y:= Fine.add x y
 mul_mem' x y:= Fine.grow x y
 algebraMap_mem' s:=by rw [Algebra.algebraMap_eq_smul_one]; exact (Fine.one (s:=S)).scale s

-- local needed for simp at Pol; scope.
abbrev House (S:Finset n):=↥(Honour S)
instance (S:Finset n):CommRing (House S) where
 mul_comm x y:=Subtype.ext (fineWise x.2 y.2)

section blend
variable {X A:Type*}[DecidableEq X][Ring A][Algebra ℂ A]
omit [DecidableEq X] in
private lemma line_cost {G:A→ Prop}{c:ℝ}{x:A}(p:Blend G c x): Blend G c (-x):= by simpa using p.smul (-1)
private lemma colour_cost (F:X→ A)(L:List X)(p:L.Nodup) :
   Blend (spool F L.toFinset 1) (3^L.length) (foil (F-1) L-(-1: A)^L.length):=by
 -- recursion: F-1 times residue minus const;if combine e-al cost, C recurrence $3^$
 induction L with
 | nil=> rw [show foil (F-1) []=(1:A) from rfl,List.length_nil,pow_zero,pow_zero,sub_self]; exact Blend.zero.extendsTo (by norm_num)
 |cons v L ih=>
    rcases List.nodup_cons.mp p with ⟨t,q⟩; let X:=L.toFinset; let V:=insert v X; let P:=(spool F V 1); let U:=foil (F-1) L; let J:=(-1:A)^L.length; let R:=(3:ℝ)^L.length; have hx:v∉X:= fun h=>t (List.mem_toFinset.mp h)
    have hh:=ih q; have hv: Blend (spool F {v} 1) 1 (F v):= .item _ ⟨[v],by simp⟩
    have ht(S:Finset _) (p:S⊆ V) : ∀ X, spool F S 1 X→ P X:= fun _ u=>Spool.weaken _ u le_rfl p
    have h: Blend P R (F v * (U-J)):=by
       have hs:({v}:Finset _ ) ∪ X=V:= singleton_union ..; have hg:= Blend.merge _ _ P hv hh (fun a b h t=> Spool.weaken _ (Spool.run _ h t (by rwa [Finset.disjoint_singleton_left])) (by omega) hs.le); simpa only [one_mul] using hg
    let c:ℂ:= (-1)^L.length
    have pp: Blend P 1 (F v * J):=by
      rw [show F v*J=c • F v from ?_]; have he:‖c‖=1:=(by simp [c]); simpa [he] using (hv.mono (ht _ (by unfold V; simp))).smul c
      have hx : algebraMap ℂ A c=J:=by unfold c J; simp
      rw [←hx,Algebra.smul_def,Algebra.commutes c (F v)]
    have hs: Blend P R (-(U-J)):= line_cost (hh.mono (ht _ (subset_insert ..)))
    rw [List.toFinset_cons,show foil (F-1) (v::L) - (-1)^(v::L).length= (F v*(U-J) + F v*J) + -(U-J) from ?_]
    · apply ((h.join pp).join hs).extendsTo; rw [List.length_cons,pow_succ']; linarith [show 1 ≤R from one_le_pow₀ (by norm_num : (1:ℝ) ≤ 3)]
    change (F v-1)*U-_= _; rw [List.length_cons,pow_succ, mul_neg_one]; change _- -J=_; rw [sub_mul,mul_sub,one_mul]; abel
end blend
variable {S:Finset n}
-- Mark vertices b=false, `Bloom`. determinant factoring polynomial. arbitrary b, twin rev. separate SElect.
def rootLetter (X Z:WRect n a)(b:Bool)(S:Finset n)(i:a): FC n:= handy b S (col X i) (col Z i)
def markedArc {q:Type}[Fintype q][DecidableEq q](b:Bool)(L:List q)(S:Finset n)(X Z:WRect n q):= foil (rootLetter X Z b S-1) L
lemma arc_blend {q:Type}[Fintype q][DecidableEq q](L:List q)(p:L.Nodup)(e:L.length=10)(b:Bool)(X Z:WRect n q):
   Blend (spool (rootLetter X Z b S) L.toFinset 1) (3^(10:ℕ)) (markedArc b L S X Z-1):= by
 have v:= colour_cost (rootLetter X Z b S) L p; rw [e,(by decide : Even 10).neg_one_pow (α:=FC n)] at v; exact v
lemma arc_vertex {q:Type}[Fintype q][DecidableEq q](L:List q)(b:Bool)(X Z:WRect n q)(z:hand (!b) (cutM S)*X=X) : markedArc b L S X Z∈ Honour S:=by
 have hx (i:q): (rootLetter X Z b S -1) i ∈ Honour S := Subalgebra.sub_mem _ ((show Fine S univ false (handy b S (col X i) (col Z i)) from fine_arch _ ((col_lim ..).2 z i) _)) (one_mem _)
 induction L with | nil=> exact one_mem _|cons i L ih=> exact mul_mem (hx i) ih
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern
#print axioms arc_vertex
#print axioms arc_blend
