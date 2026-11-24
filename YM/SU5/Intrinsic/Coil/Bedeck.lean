import YM.SU5.Intrinsic.Coil.Tape
import YM.CF.Mew.Pot
import YM.CF.Vow.Law
import YM.CF.Vow.Grow

set_option linter.unusedSectionVars false
set_option autoImplicit false
noncomputable section
namespace YM.CF.Coil
open Function Lattice Finset Filter Stilo Palot RG Scree Skye
open Fock Tulip
open scoped BigOperators Classical YM.CF.Mew

variable {n:Side} {I J : Type} -- universes actuals

/-- extra witnesses supplying the local germ only for this tile. D includes
all Force bill footprints paid. permit will simulate the function's *use*
not extend it to a different angular lease at each D-in-its own footprint. -/
structure Chart (I:Type)(Y:Type) [DecidableEq Y] where
 space:I→ Finset Y
 anchor:I→ Y
 here(i):anchor i∈ space i
variable [Fintype I][DecidableEq I]
namespace Chart
variable (B:Chart I (Seat n))

open Vow

def ledger : Album (I⊕ Force n) (Seat n) :=
 { seats:= Sum.elim B.space (fun x=> (lordD x).val)
   present:= fun i=> by cases i <;> first | exact ⟨_,B.here _⟩| exact (lordD _).property
   cover:= Sum.elim (fun _=>∅) (fun x=>extraD x)
   sits:= fun i=> by cases i <;> first|exact empty_subset _|rename_i y; exact y.property.2
   meet:= Sum.elim (fun i=>Sum.elim (fun j=> B.anchor i≠ B.anchor j) (fun _=>True)) (fun i=>Sum.elim (fun _=>True) (fun j=>Disjoint (lordD i).val (lordD j).val))
   compatible:= fun i j=> by
       rcases i with i|i<;> rcases j with j|j <;> intro h
       · exact (show B.anchor i≠B.anchor j from fun g=>Finset.disjoint_left.mp (show Disjoint (B.space i) (B.space j) from h) (B.here _) (g.symm ▸ B.here j))
       · trivial
       · trivial
       exact h }
local notation "L"=> B.ledger
variable (S:Finset I)(F:Finset (Force n))

def offices (J:Finset I):Prop:=Set.InjOn B.anchor J
local notation "leg" i:max=> Vow.lordD i
abbrev procession (F: Finset (Force n)):Prop:= Set.PairwiseDisjoint (F:Set (Force n)) (fun i=>i.val.1.val.2)
lemma season_iff : (L).Pairwise (S.disjSum F) ↔ B.offices S ∧ procession F:=by
 constructor
 · intro p; refine ⟨fun i hi j hj z=>?_, fun i hi j hj r=>?_⟩
   · exact by_contra fun v=> (show B.anchor i≠B.anchor j from p _ (inl_mem_disjSum.mpr hi) _ (inl_mem_disjSum.mpr hj) (mt Sum.inl.inj v)) z
   exact p _ (inr_mem_disjSum.mpr hi) _ (inr_mem_disjSum.mpr hj) (mt Sum.inr.inj r)
 rintro ⟨h,t⟩; intro i v j p q; cases i<;>cases j
 · rename_i i j; apply (show (B.anchor i≠ B.anchor j)→_ from id); exact fun x=> q (congrArg Sum.inl (h (inl_mem_disjSum.mp v) (inl_mem_disjSum.mp p) x))
 · trivial
 · trivial
 exact t (inr_mem_disjSum.mp v) (inr_mem_disjSum.mp p) (mt (congrArg Sum.inr) q)

lemma claim_tape : (L).claim (S.disjSum F)=F.biUnion Vow.extraD:= by
 ext i; constructor <;> intro v
 · obtain ⟨j,p,q⟩:= mem_biUnion.mp v; cases j
   · exact False.elim ((notMem_empty i) q)
   exact mem_biUnion.mpr ⟨_,inr_mem_disjSum.mp p,q⟩
 obtain ⟨j,p,q⟩:=mem_biUnion.mp v; exact mem_biUnion.mpr ⟨_,inr_mem_disjSum.mpr p,q⟩

lemma fuel_iff (V:Pane n) (p:BudgetPoint):
 RG.flags p.threshold V⊆ (L).foot (S.disjSum F) ∧ (L).Pays (RG.flags p.threshold V) (S.disjSum F) ↔ B.offices S∧coverF p F V ∧ procession F:=by
 let Ω:= flags p.threshold V; let K:=(L).foot (S.disjSum F); have h:=B.claim_tape S F
 constructor
 · rintro ⟨t,v,H⟩; obtain ⟨s,f⟩:= (B.season_iff _ _).mp v; rw [inter_eq_right.mpr t,h] at H; exact ⟨s,H.symm,f⟩
 rintro ⟨s,v,f⟩; let Q:= S.disjSum F; have v:(L).claim Q=Ω:= h.trans v
 have ht:Ω⊆ K:= v ▸ (L).claims Q; exact ⟨ht,(B.season_iff S F).mpr ⟨s,f⟩,(inter_eq_right.mpr ht).trans v.symm⟩

/-- Ensure during lit comparisons all old-Force apertures use exactly their own flags. -/
lemma sure_Flag {Ω : Finset (Seat n)}{T:Finset (I⊕Force n)}(h:(L).Pays Ω T)(y:Scree.Force n)(p:Sum.inr y∈T):
 (leg y).val∩ Ω = y.val.2:=by
 ext i; constructor
 · intro m; obtain ⟨v,z⟩:= mem_inter.mp m
   obtain ⟨a,u,b⟩:= mem_biUnion.mp (show i∈(L).claim T from h.known ▸ mem_inter.mpr ⟨((L).atLine T p) v,z⟩);
   cases a <;> rename_i q; exact False.elim (notMem_empty i b)
   by_cases z:q=y; · subst q; exact b
   exact False.elim (Finset.disjoint_left.mp (show Disjoint (leg q).val (leg y).val from h.allowed _ u _ p (mt Sum.inr.inj z)) (q.property.2 b) v)
 intro m; exact mem_inter.mpr ⟨y.property.2 m,(mem_inter.mp (h.known.symm ▸ (show i∈ (L).claim T from mem_biUnion.mpr ⟨_,p,m⟩))).2⟩
-- (!) remove F phantom.

open Pastry

private def Fits (A:Finset (Seat n))(p:Cipher n):Prop:= Pastry.Flour (camp A) p.val
variable (U:I→ Cipher n →ₗ[ℂ] Cipher n) (P: Force n→Cipher n)
structure Mild (B:Chart I (Seat n)) (U:I→ Cipher n →ₗ[ℂ] Cipher n) : Prop where
 nearT (i X)(g:Cipher n):B.space i⊆X→ Pastry.Flour (camp X) g.val→ Pastry.Flour (camp X) (U i g).val
 farT(i X)(e f:Cipher n):Disjoint (B.space i) X→ Pastry.Flour (camp X) f.val→ U i (e*f)=U i e*f
local notation "I_"=> I ⊕ Force n
local notation "act" => Album.traverse
noncomputable abbrev readAt (U:I→ Cipher n →ₗ[ℂ] Cipher n)(P:Force n → Cipher n) (T:I⊕ Force n) : Cipher n → Cipher n := Sum.elim (fun (i:I)=> (fun u:Cipher n=>U i u)) (fun i=> fun e:Cipher n=> P i*e) T
variable (Tape':List I)(Deck:List (Force n))
abbrev together := Tape'.map Sum.inl ++ (Deck.map Sum.inr : List (I⊕ Force n))
abbrev script(Ω:Finset (Seat n))(U:I→Cipher n →ₗ[ℂ] Cipher n)(P:Force n→ Cipher n):Finset (Seat n) → Cipher n:=B.ledger.compact (fun i=>act (readAt (I:=I) U P) i (together Tape' Deck)) Ω
lemma moving_germ (h:B.Mild U)(p:∀ i,Pastry.Flour (camp (lordD i).val) (P i).val) : (L).LocalAct (readAt U P) Fits:=by
 refine ⟨fun _=> Flour.grainE, ?_,?_⟩
 · intro i S t b g; cases i; exact h.nearT _ _ _ b g; rename_i i; exact ((p i).lift (fun j u=>mem_filter.mpr ⟨mem_univ _,b (mem_filter.mp u).2⟩)).mul (show Pastry.Flour (camp S) t.val from g)
 intro i R e f p h'; cases i; exact h.farT _ R e f p h'; exact (mul_assoc ..).symm -- direction? P*(e*f)=(P*e)*f yes

-- root traversal as linear operators for all the coalitions
abbrev sail (U:I→ Cipher n →ₗ[ℂ] Cipher n)(P:Finset I)(t:List I): Cipher n →ₗ[ℂ] Cipher n := (t.foldr (fun i p=>if i∈P then (U i).comp p else p) LinearMap.id)
lemma execute (d:Deck.Nodup)(z:Deck.toFinset=univ) : act (readAt U P) (S.disjSum F) (together Tape' Deck)=sail U S Tape' (∏ i∈ F,P i):=by
 have hp (l:List (Force n))(u:l.Nodup) : act (readAt U P) (S.disjSum F) (l.map Sum.inr) =∏ i∈ (F∩ l.toFinset), P i:=by
    induction l with
    | nil => simp [Album.traverse] -- fix
    | cons i l ih=>
       obtain ⟨a,b⟩:= List.nodup_cons.mp u; rw [List.map_cons,Album.traverse_cons, ih b,List.toFinset_cons]
       by_cases t:i∈F
       · rw [if_pos (inr_mem_disjSum.mpr t),show F ∩ insert i l.toFinset=insert i (F ∩ l.toFinset) from Finset.inter_insert_of_mem t,Finset.prod_insert (fun p=>a (List.mem_toFinset.mp (mem_inter.mp p).2))]; rfl
       rw [if_neg (mt inr_mem_disjSum.mp t), Finset.inter_insert_of_notMem t]
 induction Tape' with
 | nil=> rw [sail,List.foldr_nil,LinearMap.id_apply, together,List.map_nil,List.nil_append,hp _ d,z,inter_univ]
 | cons i l ih=>
    rw [show together (i::l) Deck=Sum.inl i :: together l Deck from rfl, Album.traverse_cons,ih]; unfold sail; rw [List.foldr_cons]; by_cases g:i∈S; · rw [if_pos g, if_pos (inl_mem_disjSum.mpr g)]; rfl
    rw [if_neg g,if_neg (mt inl_mem_disjSum.mp g)]
-- no price for changing old-Gram witness at this genesis
#print axioms readAt
#print axioms moving_germ
#print axioms execute
#print axioms ledger
#print axioms Mild
#print axioms sure_Flag
#print axioms script
end Chart
end YM.CF.Coil
