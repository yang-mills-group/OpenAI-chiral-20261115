import YM.SU5.Intrinsic.Coil.Org
import YM.CF.Palot.Jade

/-! # The route through Palot's Canonical gas.

Operators in any chosen tape commute *with multiplication on the outside*, not among
all the operators. We can use by construction when applying Wake insertion expansions.
Also budget ALL terms even though each charge knows flags and priority W only on its OWN
footprint. This lets one carry through local clustered expansions at actual heights. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Coil
open Function Lattice Finset Filter Stilo Palot
open scoped BigOperators Classical
variable {S I E:Type*}[Fintype S][DecidableEq S][Fintype I][DecidableEq I]
    [CommSemiring E]
namespace Album
variable (X:Album I S) (U:I→E→E)
structure LocalAct (Fits:Finset S→ E→Prop):Prop where
 unit (S':Finset S):Fits S' 1
 near (i)(P e):X.seats i⊆ P→ Fits P e→ Fits P (U i e)
 far (i)(P:Finset S)(e f:E):Disjoint (X.seats i) P→ Fits P f→ U i (e*f)=U i e*f

def traverse (P:Finset I)(l:List I):E:= l.foldr (fun i e=>if i∈P then U i e else e) 1 -- no X
lemma traverse_nil(P:Finset I):traverse U P []=1:=rfl
lemma traverse_cons(P:Finset I)(i)(l:List I):traverse U P (i::l)=if i∈P then U i (traverse U P l) else traverse U P l:=rfl
@[simp] lemma traverse_empty (l:List I): traverse U ∅ l=1:=by induction l with| nil=>rfl|cons i l ih=> simp [traverse_cons,ih]

variable {U} {Fits:Finset S→ E→Prop}{X} (p:X.LocalAct U Fits)
include p in
lemma LocalAct.traverse (P:Finset I)(l:List I):Fits (X.foot P) (Album.traverse U P l):=by
 induction l with| nil=> exact p.unit _| cons i l ih=> rw [traverse_cons]; split; exact p.near i _ _ (X.atLine P ‹_›) ih; exact ih
include p in
lemma LocalAct.tour (Ω:Finset S)(l:List I): X.Mounted (Ω:=Ω) (fun i=>Album.traverse U i l):=by
 refine ⟨traverse_empty ..,fun P Q h _ _=>?_⟩
 change Album.traverse _ _ _ = Album.traverse _ _ _ * Album.traverse _ _ _
 have e:= X.occupied P Q h; induction l with
 | nil=> exact (mul_one _).symm
 | cons i l ih=>
    let u:=Album.traverse U P l; let v := Album.traverse U Q l
    rw [traverse_cons,traverse_cons,traverse_cons,ih]
    by_cases g:i∈ P
    · rw [if_pos g, if_neg (Finset.disjoint_left.mp e g),if_pos (mem_union_left _ g)]; exact p.far i _ u v (h.mono_left (X.atLine P g)) (p.traverse ..)
    by_cases t:i∈Q
    · rw [if_pos t, if_neg g, if_pos (mem_union_right _ t),mul_comm u v,mul_comm u (U i v),p.far i _ v u (h.symm.mono_left (X.atLine Q t)) (p.traverse ..)]
    simp [t,g]
end Album

namespace Season
open RG Push.AbsoluteSums Push.AbsoluteSums.Trees
variable {n:Side}
local notation "Y"=> Site n
variable (X:Album I (Site n)) (r:ℝ) (B:ℕ) (w:I→ℝ)

abbrev leafCost (g:Finset I):=∏ i∈g,w i
abbrev bookL (m:ℕ) (g:Finset I)(A: leaf (Site n))(D:Finset (Site n)) := if g.card-1 ≥ m ∧ X.claim g=D ∧ X.melody g=beamH A.val ∧ X.Pairwise g then leafCost w g else (0:ℝ) -- allow ∅ flags
abbrev incubate (m:ℕ)(A:leaf (Site n))(D:Finset (Site n)):= ∑ g:Finset I,bookL X w m g A D
lemma at_most_leaf {g:Finset I}{A:leaf (Site n)}(x:X.melody g=beamH A.val)(p:∀ i,0≤w i)(t:0≤r) (o)(u:o∈A.val):
 leafCost w g * currency B r A.val ≤ touches X.seats B w r o g:=by
 obtain ⟨f,h⟩:= break_h X.seats X.present A g x
 rw [touches, if_pos ⟨f,h.symm ▸ (by assumption)⟩,prod_mul_distrib]
 apply mul_le_mul_of_nonneg_left _ (prod_nonneg (fun i _=>p i)); unfold currency; rw [← Real.exp_sum]; apply Real.exp_monotone; rw [←mul_sum]; apply mul_le_mul_of_nonneg_left _ t; rw [←h]; exact_mod_cast Ac.cover X.seats B f

variable {γ δ q:ℝ}
variable (p:Ready X.seats B w r γ δ q)
variable (m:ℕ)
lemma budget_one (t:0≤r)(g:Finset I)(o:Site n) (u:∀ i,0≤w i):
    (∑ A:leaf (Site n) with o∈A.val,(∑ D:Finset (Site n),bookL X w m g A D)*currency B r A.val)≤ if m≤g.card-1 then touches X.seats B w r o g else 0:=by
 let F(A:leaf (Site n)):=∏ i∈g,w i
 have hp(A:leaf (Site n)): (∑ D:Finset (Site n),bookL X w m g A D)=bookL X w m g A (X.claim g):=by
    rw [sum_eq_single (X.claim g)]
    · intro d _ y; unfold bookL; rw [if_neg]; exact fun e=> y e.2.1.symm
    simp
 simp_rw [hp]
 split; rename_i h
 · by_cases v:∃ A:leaf (Site n),o∈A.val∧X.melody g=beamH A.val
   · obtain ⟨A,v,y⟩:=v; rw [sum_eq_single_of_mem A (mem_filter.mpr ⟨mem_univ _,v⟩)]; apply le_trans _ (at_most_leaf X r B w y u t o v); apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le; unfold bookL; split; exact le_rfl; exact prod_nonneg (fun i _=>u i)
     intro b _ p; unfold bookL; rw [if_neg, zero_mul]; exact fun g=> p (Subtype.ext ((bay_beam b.val).symm.trans ((congrArg Stilo.bay (g.2.2.1.symm.trans y)).trans (bay_beam _))))
   rw [sum_eq_zero]; unfold touches; split; exact prod_nonneg fun i _=> mul_nonneg (u i) (Real.exp_pos _).le; exact le_rfl
   intro a p; unfold bookL; rw [if_neg,zero_mul]; exact fun g=>v ⟨a,(mem_filter.mp p).2,g.2.2.1⟩
 rename_i h; simp [bookL,h]
include p in
lemma budget_tape (t:0≤r)(o:Site n) :
    (∑ A: Palot.leaf (Site n) with o∈A.val, (∑ D:Finset (Site n),incubate X w m A D)*currency B r A.val) ≤ γ*q^m*(1-q)⁻¹:=by
 unfold incubate; have he:= budget_sum (touch_tail X.seats B p o m) univ
 conv_lhs=>
    arg 2; ext A; rw [sum_comm, sum_mul]
 rw [sum_comm]; exact (sum_le_sum fun i _=>budget_one X r B w m t i o p.2.2.2.2.1).trans he
end Season
end YM.CF.Coil
