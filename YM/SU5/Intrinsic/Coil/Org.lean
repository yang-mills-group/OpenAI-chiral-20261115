import YM.CF.Palot.Sparkle

/-
# XXI Mark inlet: hard-core component identity

Variant of (74). At fixed priorities and old Force collection, and after
pull-through of the vacuum and Reg factors, the insertions expand into an
array of EVEN operations on the board. Here we do *not* make a long
history of derivatives attached to operations. Give an actual ordinal tape
for the tiles (includes all optional pieces of all the queries). For each
choice of mark at a root have distinct tickets for all its terms. Also give
tickets for the OLD Forces maybe to be purchased. Process keeping all
of the tiles DISTINCT, ordered on the tape. (Because supports of ALL
options in one query include the root, can even run as a square-free
perturbation in that Key *without refolding* here.) Factor in a restricted
new way: require disjointness across *all* components, even if no flags
bought. Hence the canonical logarithm & curvature redistribution techniques
are available in this pricing. The connected-family costs require NO
partition-factorial with v in the volume, just enumerating this tape with
Distinct.Finset prices. Follows `Palot.Pal,Jade` in reindexing.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Coil
open Function Lattice Finset Filter Stilo Palot
open scoped BigOperators Classical
variable {S I E:Type*}[Fintype S][DecidableEq S][Fintype I][DecidableEq I]
    [CommSemiring E]

/-- Stamps and contacts. Includes old Force **IDs** claims, the seat
flags covered, and all key-varying charges. -/
structure Album (I S : Type*) [DecidableEq S] where
  seats : I → Finset S
  present(i:I):(seats i).Nonempty
  cover : I → Finset S
  sits(i:I):cover i⊆seats i
  meet:I→I→Prop
  compatible(i j:I):Disjoint (seats i) (seats j) → meet i j

variable (X:Album I S)
namespace Album
abbrev foot(S':Finset I):= S'.biUnion X.seats
abbrev claim(S':Finset I):= S'.biUnion X.cover
abbrev melody(S':Finset I):= rhythm X.seats S'

@[simp] lemma tune (P:Finset I):bay (X.melody P)=X.foot P:= Palot.beats ..
lemma atLine(P:Finset I){x:I}(p:x∈P):X.seats x⊆ X.foot P:= Finset.subset_biUnion_of_mem _ p
lemma hasPoint(P:Finset I){x:I}(p:x∈P):beamH (X.seats x)≤ X.melody P := Finset.le_sup (f:=fun i=>beamH (X.seats i)) p
lemma claims(P:Finset I): X.claim P⊆ X.foot P:=by apply Finset.biUnion_mono; exact fun x _=> X.sits x
lemma occupied(P Q:Finset I)(u:Disjoint (X.foot P) (X.foot Q)):Disjoint P Q :=by
 refine Finset.disjoint_left.mpr fun {y} a b=>?_ ; obtain ⟨i,v⟩:= X.present y; exact Finset.disjoint_left.mp u (X.atLine P a v) (X.atLine Q b v)

def Pairwise(P:Finset I):Prop:=∀ i∈P,∀ j∈P,i≠j→X.meet i j
variable {X}
lemma Pairwise.part {P Q:Finset I}(u:X.Pairwise P)(t:Q⊆ P):X.Pairwise Q:= fun i a j b=>u i (t a) j (t b)
lemma Pairwise.union {P Q:Finset I}(t:Disjoint (X.foot P) (X.foot Q))
 (p:X.Pairwise P)(q:X.Pairwise Q): X.Pairwise (P∪Q):=by
    intro i u j v a; rcases mem_union.mp u with u|u<;>rcases mem_union.mp v with v|v
    exact p i u j v a
    exact X.compatible i j (t.mono (X.atLine P u) (X.atLine Q v))
    exact X.compatible i j (t.symm.mono (X.atLine Q u) (X.atLine P v))
    exact q i u j v a
variable (X)
-- specify actual Ω and extra separately. Archive on torus;
-- in application D determined by the vertex set, no sum over tag choices.
structure Pays (Ω:Finset S)(P:Finset I) : Prop where
 allowed:X.Pairwise P
 known:X.foot P∩Ω=X.claim P

variable {X} {Ω:Finset S}
lemma Pays.union {P Q:Finset I}(t:Disjoint (X.foot P) (X.foot Q))(p:X.Pays Ω P)(q:X.Pays Ω Q): X.Pays Ω (P∪Q):=by
 refine ⟨p.allowed.union t q.allowed,?_⟩
 simp only [foot,claim,Finset.union_biUnion,Finset.union_inter_distrib_right]; rw [p.known,q.known] -- simp abbrev
lemma Pays.smaller {P Q:Finset I}(p:X.Pays Ω (P∪Q))(t:Disjoint (X.foot P) (X.foot Q)): X.Pays Ω P:=by
 refine ⟨p.allowed.part subset_union_left,?_⟩; have hi:=p.known
 unfold foot claim at hi ⊢; rw [Finset.union_biUnion,Finset.union_biUnion] at hi
 ext i; constructor
 · intro h; obtain ⟨u,w⟩:= mem_inter.mp h; let g:=X.foot P∪ X.foot Q
   have h:i∈ X.claim P∪ X.claim Q:= hi ▸ (show i∈g∩Ω from mem_inter.mpr ⟨mem_union_left _ u,w⟩)
   exact (mem_union.mp h).resolve_right fun l=>Finset.disjoint_left.mp t u (X.claims Q l)
 intro h; exact mem_inter.mpr ⟨X.claims P h,(mem_inter.mp (show i∈(X.foot P∪ X.foot Q)∩Ω from hi.symm ▸ mem_union_left _ h)).2⟩

variable (X:Album I S)
variable (F:Finset I→E)
structure Mounted : Prop where
 even : F ∅=1
 act(P Q:Finset I):Disjoint (X.foot P) (X.foot Q)→ X.Pays Ω P → X.Pays Ω Q → F (P∪Q)=F P*F Q

def read (Ω:Finset S) (P:Finset I) (H:Crowd S) := if X.melody P=H∧ X.Pays Ω P then F P else 0
variable (p:Mounted X F (Ω:=Ω))
include p
lemma org : Org (fun i=> (⟨X.seats i,X.present i⟩: Palot.leaf S)) (X.read F Ω) :=by
 refine ⟨fun i h v a t=> ?_,?_, ?_⟩
 · unfold read at v; split at v; next w=> exact w.1 ▸ X.hasPoint i t
   contradiction
 · have h:X.Pays Ω ∅:=⟨fun i t=>False.elim (notMem_empty _ t),by simp [foot,claim]⟩; simp [read,melody,rhythm,h,p.even]
 intro H R P Q u a b
 have hP:X.melody P≤ H:= Finset.sup_le fun i hi=> a i hi
 have hQ:X.melody Q≤ R:= Finset.sup_le fun i hi=> b i hi
 have h:Disjoint (X.foot P) (X.foot Q):= Disjoint.mono ((X.tune P) ▸ bay_m hP) ((X.tune Q) ▸ bay_m hQ) u
 unfold read; rw [show X.melody (P∪Q)=X.melody P⊔ X.melody Q from Finset.sup_union]
 by_cases v:X.melody P⊔X.melody Q= H⊔ R
 · obtain ⟨w,t⟩:=splits_eq u hP hQ v; have hc:X.Pays Ω (P∪Q) ↔ X.Pays Ω P∧ X.Pays Ω Q:=⟨fun p=>⟨p.smaller h,(show X.Pays Ω (Q∪P) from Q.union_comm P ▸ p).smaller h.symm⟩,fun ⟨a,b⟩=> a.union h b⟩
   simp only [hc,w,t,true_and]; by_cases E:X.Pays Ω P <;> by_cases D:X.Pays Ω Q <;> simp [E,D]; exact p.act P Q h E D
 rw [if_neg fun g=> v g.1]; split_ifs with g k a
 · exact False.elim (v (by rw [g.1,k.1]))
 all_goals simp

abbrev compact (Ω:Finset S)(L:Finset S):E:= mintF (X.read F Ω) (beamH L)
-- Full powers paid, not truncated
lemma gas_identity : (∑ i:Finset I with Ω⊆ X.foot i ∧ X.Pays Ω i,F i)= hGas Ω (fun i=> X.compact F Ω i.val):=by
 rw [←chimeU Ω (X.org F p), Finset.sum_filter]; apply Finset.sum_congr rfl; intro i _; rw [eq_comm]
 by_cases l:Ω⊆ X.foot i ∧ X.Pays Ω i
 · rw [if_pos l,sum_eq_single_of_mem (X.melody i) (mem_filter.mpr ⟨mem_univ _,(X.tune i).symm ▸ l.1⟩)]; exact if_pos ⟨rfl,l.2⟩
   intro j _ v; exact if_neg fun g=> v g.1.symm
 rw [if_neg l]; apply sum_eq_zero; intro H h; apply if_neg; intro e; exact l ⟨X.tune i ▸ (e.1.symm ▸ (mem_filter.mp h).2),e.2⟩
end Album
end YM.CF.Coil
