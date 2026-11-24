import YM.CF.Palot.Rosa
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Palot
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo
open scoped Classical
open RG Push Push.AbsoluteSums Push.AbsoluteSums.Ursell Push.AbsoluteSums.Graph Push.AbsoluteSums.Coef Push.AbsoluteSums.Gas
open Trees
variable {n:Side}{ι E: Type*}[Fintype ι][NormedCommRing E][NormOneClass E][NormedAlgebra ℝ E][CompleteSpace E]
abbrev Duo(n:Side):= Y n ⊕ Y n
def dock(D:Duo n):Y n:=Sum.elim id id D
abbrev beatB(P: Finset (Duo n)):=rhythm (stern ∘ dock) P
local notation "bay"=> Stilo.bay
def mine(O:Support n)(T: Finset (Duo n)) : Prop:= flow (Site n) T.toLeft ∧ raisedH O T.toLeft ∧ raisedH (robe T.toLeft) T.toRight ∧ O∩bay (beatB T)⊆robe T.toLeft
def jewel(O:Support n)(F W:Y n→ E)(T:Finset (Duo n))(H:Crowd (Site n)):= if beatB T=H∧ mine O T then ∏ i∈T,Sum.elim F W i else 0
def shim(D S: hook (Site n)):Prop:= Disjoint (robe D) (robe S)
variable {O:Support n}{Q T:Finset (Duo n)}{R S:Crowd (Site n)}
lemma rim_beat : robe T.toLeft ∪ robe T.toRight=bay (beatB T):=by
 rw [beatB, beats]; ext i; simp only [robe,mem_union,mem_biUnion]; constructor
 · intro h; rcases h with ⟨a,t,h⟩|⟨a,t,h⟩; exact ⟨_,mem_toLeft.mp t,(show i∈ (stern ∘ dock) (Sum.inl a) from h)⟩; exact ⟨_,mem_toRight.mp t,(show i∈ (stern ∘ dock) (Sum.inr a) from h)⟩
 rintro ⟨a,l,v⟩; cases a with| inl i=> exact Or.inl ⟨i,mem_toLeft.mpr l,v⟩| inr i=> exact Or.inr ⟨i,mem_toRight.mpr l,v⟩
lemma trem (h:Disjoint (bay (beatB T)) (bay (beatB Q)))(p:mine O (T∪Q)):mine O T:=by
 rw [mine,toLeft_union,toRight_union, show beatB (T∪Q)=beatB T⊔beatB Q from (by simp [beatB,rhythm,Finset.sup_union]), joinsB,show robe (T.toLeft∪Q.toLeft)= robe T.toLeft ∪ robe Q.toLeft from (by simp [robe,Finset.union_biUnion])] at p
 obtain ⟨l,v,w,b⟩:=p; refine ⟨flow_m l subset_union_left, fun i p=> v i (mem_union_left _ p),?_,?_ ⟩
 · intro i u; obtain ⟨y,x,p⟩:=not_disjoint_iff.mp (w i (mem_union_left _ u)); have ht:y∈ bay (beatB T):= rim_beat ▸ mem_union_right _ (show y∈ robe T.toRight from mem_biUnion.mpr ⟨_,u,x⟩); exact not_disjoint_iff.mpr ⟨_,x,(mem_union.mp p).resolve_right fun g=> Finset.disjoint_left.mp h ht (rim_beat ▸ mem_union_left _ g)⟩
 intro i p; obtain ⟨g,u⟩:= mem_inter.mp p; exact (mem_union.mp (b (mem_inter.mpr ⟨g,mem_union_left _ u⟩))).resolve_right fun k=> Finset.disjoint_left.mp h u (rim_beat ▸ mem_union_left _ k)
lemma seam_b (T:Finset (Duo n))(i:Y n)(h:i∈ T.toLeft) : i.val⊆ bay (beatB T):=fun x p=> rim_beat ▸ mem_union_left _ (show x∈ robe T.toLeft from mem_biUnion.mpr ⟨_,h,p⟩)
lemma trumpet(h:Disjoint (bay (beatB T)) (bay (beatB Q)))(p:mine O T)(q:mine O Q):mine O (T∪Q):=by
 rw [mine,toLeft_union,toRight_union,show beatB (T∪Q)=beatB T⊔beatB Q from (by simp [beatB,rhythm,Finset.sup_union]),joinsB,show robe (T.toLeft∪Q.toLeft)=robe T.toLeft∪ robe Q.toLeft from (by simp [robe,Finset.union_biUnion])]; obtain ⟨l,v,w,b⟩:=p; obtain ⟨j,f,g,u⟩:=q
 refine ⟨?_,fun i p=> (mem_union.mp p).elim (v i) (f i),fun i p e=> (mem_union.mp p).elim (fun t=> w _ t (Disjoint.mono_right subset_union_left e)) (fun t=> g _ t (Disjoint.mono_right subset_union_right e)),fun i p=>?_⟩
 · intro i t k q e; rcases mem_union.mp t with p|p<;> rcases mem_union.mp q with q|q; exact l _ p _ q e; exact Disjoint.mono (seam_b _ _ p) (seam_b _ _ q) h; exact Disjoint.mono (seam_b _ _ p) (seam_b _ _ q) h.symm; exact j _ p _ q e
 obtain ⟨x,v⟩:=mem_inter.mp p; exact mem_union.mpr ((mem_union.mp v).imp (fun i=> b (mem_inter.mpr ⟨x,i⟩)) fun i=> u (mem_inter.mpr ⟨x,i⟩))
lemma flameR : fits dock T S ↔ beatB T≤ S:=by unfold fits beatB rhythm; rw [Finset.sup_le_iff]; rfl
lemma orgG(O:Support n)(F W:Y n→ E): Org dock (jewel O F W):=by
 refine ⟨fun s t p=>?_,?_,?_ ⟩
 · by_cases h:beatB s=t; exact flameR.mpr h.le; exact False.elim (p (if_neg fun u=> h u.1))
 · unfold jewel; simp [mine,beatB,rhythm,flow,raisedH,robe,bayB]
 intro H S i j p l t; have he : Disjoint i j:= Finset.disjoint_left.mpr fun {x} k g=>fits_i (l _ k) (t _ g) p
 have hu:= flameR.mp l; have hp:= flameR.mp t
 have ht:= Disjoint.mono (bay_m hu) (bay_m hp) p; unfold jewel; rw [prod_union he,show beatB (i∪j)=beatB i⊔beatB j from (by simp [beatB,rhythm,Finset.sup_union])]; by_cases v:beatB i⊔beatB j=H⊔S
 · obtain ⟨g,r⟩:=splits_eq p hu hp v; have hq: mine O (i∪j) ↔ mine O i ∧ mine O j :=⟨fun a=> ⟨trem ht a,trem ht.symm (union_comm i j ▸ a)⟩, fun a=> trumpet ht a.1 a.2⟩; simp only [v,g,r,hq,true_and]; split_ifs <;> simp_all
 rw [if_neg (fun u=>v u.1)]; split_ifs with a b c; · exact False.elim (v (by rw [a.1,b.1]))
 all_goals simp
lemma jackF (O: Support n)(F W:Y n→ E)(T: leaf (Site n))(h:mintF (jewel O F W) (beamH T.val)≠0):fuelH O T:=by
 obtain ⟨i,-,v⟩:=exists_ne_zero_of_sum_ne_zero h; unfold jewel at v; split at v; swap; · contradiction
 rename_i l; obtain ⟨u,f,g,p⟩:= l.2; intro y; change Disjoint T.val O at y
 have hl:i.toLeft=∅:= eq_empty_iff_forall_notMem.mpr fun j a=> f j a (Disjoint.mono_left ?_ y)
 · have he:i.toRight=∅:=eq_empty_iff_forall_notMem.mpr fun j a=>g j a (by rw [hl]; simp [robe]); obtain ⟨x,v⟩:= T.property; have hh := rim_beat (T:=i); rw [l.1,bay_beam,he,hl] at hh; simp only [robe,biUnion_empty,union_empty] at hh; exact notMem_empty _ (hh.symm ▸ v)
 exact (seam_b _ _ a).trans_eq ((congrArg _ l.1).trans (bay_beam _))
end YM.CF.Palot
