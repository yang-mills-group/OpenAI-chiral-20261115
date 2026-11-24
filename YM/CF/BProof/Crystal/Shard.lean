import YM.CF.BProof.Crystal.Pair
import YM.CF.BProof.Crystal.Sprinkle
/-! Vertex language for equation B-PfC. The order is arbitrary (canonical list
only used to feed the physical Wick identity). Vertex supports assigned later. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Crystal
open Function Filter Fock Finset NormedSpace Garden Align Wick Double Pastry Sprinkle
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
structure Dew(V I:Type) where
 line: V→List I
 even(i): Even (line i).length
 fresh(i): (line i).Nodup
 free: V → V → Prop -- never exclude pairs outside prescribed overlaps
variable {V I U: Type}[Fintype I][LinearOrder I] [Fintype U]
namespace Dew
variable (P:Dew V I){S:Finset V}
abbrev crisp(i:V):Finset I:= (P.line i).toFinset
def grace (i:V) : Dough I:= ⟨word (P.line i),(wordP _ (P.even i) (subset_univ _)).1⟩
lemma graceCost(i:V) : ‖P.grace i‖≤1:=word_pow _
def beam (S: Finset V): Dough I:= ∏ i∈S,P.grace i
def area (S: Finset V): Finset I:= S.biUnion P.crisp
lemma price_1(i:V): Sector (P.crisp i) false (P.grace i).val:=(wordP _ (P.even i) Subset.rfl).2
lemma beamAt[DecidableEq V](S:Finset V) : Sector (P.area S) false (P.beam S).val:=by
 induction S using Finset.induction_on with
 | empty=> unfold beam; rw [prod_empty]; exact Sector.one
 | insert i S k ih=>
   rw [area,Finset.biUnion_insert,beam,prod_insert k]; exact (Garden.scope (P.price_1 _) subset_union_left).mul (Garden.scope ih subset_union_right)
lemma beamMoney[DecidableEq V](S:Finset V) : ‖P.beam S‖≤1:=by induction S using Finset.induction_on with| empty=> simp [beam]| insert i S k ih=> unfold beam; rw [prod_insert k]; exact (norm_mul_le ..).trans (mul_le_one₀ (P.graceCost _) (norm_nonneg _) ih)
def mild (S:Finset V):Prop:= (S:Set V).Pairwise P.free
abbrev terse (S:Finset V): Prop:=Set.PairwiseDisjoint (S:Set V) P.crisp
def magic(C:Op I)(S:Finset V):ℂ:=inner ℂ (pairWave (cc C)) (acts (P.beam S).val (vacuum I))
lemma beamWord[DecidableEq V](l:List V)(p:l.Nodup) : (P.beam l.toFinset).val=word (l.flatMap P.line):=by
 induction l with
 | nil=> unfold beam; rw [List.toFinset_nil,prod_empty,List.flatMap_nil]; rfl
 | cons i l ih=> simp only [List.nodup_cons] at p; simp only [List.toFinset_cons,List.flatMap_cons]; rw [word_ap,←ih p.2]; unfold beam; rw [prod_insert (by simpa using p.1)]; rfl
lemma magicWord [DecidableEq V](C:Op I)(l:List V)(p:l.Nodup) : P.magic C l.toFinset=Nose C (l.flatMap P.line):=by rw [magic,P.beamWord l p]; rfl
lemma beamZero [DecidableEq V](h:¬P.terse S): P.beam S=0:=by
 unfold terse Set.PairwiseDisjoint Set.Pairwise at h; push Not at h; obtain ⟨i,g,j,e,f,t⟩:=h; obtain ⟨x,u,v⟩:=not_disjoint_iff.mp t; have he:P.grace i*P.grace j=0:=Subtype.ext (word_blank _ _ x (List.mem_toFinset.mp u) (List.mem_toFinset.mp v)) -- tune
 unfold beam; rw [←mul_prod_erase _ _ (show i∈S from g), ←mul_prod_erase (S.erase i) _ (mem_erase.mpr ⟨Ne.symm f,show j∈ S from e⟩),←mul_assoc, he,zero_mul]
-- θ assignment over local letters of vertices
abbrev Slots(i:V) := ↑(P.crisp i)
abbrev Lease(i:V)(U:Type) := P.Slots i → Option (I×U)
abbrev Box(U:Type) := Σ i:V,P.Lease i U
variable {P}
def shine (i:I)(o:Option (I×U)): Dough I:= o.elim 1 fun x=> cell i x.1
def charge(F:I→I→U→ℂ)(i:I)(o:Option (I×U)):ℂ:= o.elim 1 (fun x=> if i<x.1 then F i x.1 x.2 else 0)
def shineC(F:I→I→U→ℂ)(i:I)(o:Option (I×U)):= hollow (star (charge F i o))*shine i o
lemma shineCash(i:I)(o:Option (I×U)):‖shine i o‖≤1:=by cases o; exact le_of_eq norm_one; exact cell_money ..
lemma shineLine(C:Op I)(F:I→I→U→ℂ)(h:∀ i j,i<j→ C i j=∑ k:U,F i j k)(i:I): 1+floss C i=∑ j:Option (I×U),shineC F i j:=by
 have hs(a:I→ U→ℂ)(j:I): hollow (n:=I) (star (∑ l:U,a j l))=∑ l:U,hollow (star (a j l)):=by
   apply Subtype.ext; change star (∑ l:U,_) • (1:FC I)=(Dough I).val _; rw [map_sum,star_sum, Finset.sum_smul]; rfl
 have hc : hollow (n:=I) 0=0:=Subtype.ext (zero_smul ..); have hb:hollow (n:=I) 1=1:=Subtype.ext (one_smul ..)
 rw [Fintype.sum_option,Fintype.sum_prod_type]; congr 1; · change 1=hollow (star (1:ℂ)) * (1:Dough I); rw [star_one,hb,mul_one]
 apply sum_congr rfl; intro j _; unfold shineC; by_cases g:i<j; simp only [g,charge,shine,Option.elim_some,if_true]; rw [h _ _ g, hs (F i) j,sum_mul]; simp only [g,charge,shine,Option.elim_some,if_false, star_zero,hc,zero_mul,sum_const_zero]
variable (P)
def flareL(i:P.Box U): Dough I:=∏ k:P.Slots i.1, shine k.val (i.2 k)
def flareC(F:I→I→U→ℂ)(i:P.Box U):ℂ:= ∏ k:P.Slots i.1,charge F k.val (i.2 k)
def flare(F:I→I→U→ℂ)(i:P.Box U): Dough I:= ∏ k:P.Slots i.1,shineC F k.val (i.2 k)
lemma flareCost (i:P.Box U): ‖P.flareL i‖≤1:=by unfold flareL; exact (Finset.norm_prod_le ..).trans (Finset.prod_le_one (fun _ _=>norm_nonneg _) (fun _ _=>shineCash ..))
variable [DecidableEq V][Fintype V]
def light (S:Finset (P.Box U)):=∏ i∈S,P.flareL i
def lc (F:I→I→U→ℂ)(S:Finset (P.Box U)):=∏ i∈S,P.flareC F i
def digest(F:I→I→U→ℂ)(S: Finset (P.Box U)):= ∏ i∈ S,P.flare F i
lemma electrify(C:Op I)(F:I→I→U→ℂ)(h:∀ i j,i<j→ C i j=∑ k:U,F i j k)(S:Finset V)(g:P.terse S): (∏ i∈P.area S,(1+floss C i))=∑ i∈ Sprinkle.span (fun i=>P.Lease i U) S,P.digest F i:=by
 rw [area,prod_biUnion g]; unfold digest; rw [← lifted]; apply prod_congr rfl; intro i _; rw [← Finset.prod_attach, show (P.crisp i).attach=(univ: Finset (P.Slots i)) from rfl]; simp_rw [shineLine C F h, Fintype.prod_sum]; rfl -- rfl sum_λβ
lemma lightcost (S:Finset (P.Box U)) : ‖P.light S‖≤1:=(Finset.norm_prod_le ..).trans (Finset.prod_le_one (fun _ _=> norm_nonneg _) (fun _ _=>P.flareCost _))
end Dew
end YM.CF.BProof.Crystal
