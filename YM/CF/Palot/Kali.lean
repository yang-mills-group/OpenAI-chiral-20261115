import YM.CF.Hake.Sea
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
variable {A Y E:Type*}[Fintype A][DecidableEq A]
local notation "bay"=> Stilo.bay
abbrev leaf(A:Type*):= {x:Finset A//x.Nonempty}
def rowT (H: Harper A)(i:A):Finset A:= univ.filter fun j=> rail H i j
lemma row_mem {H:Harper A}{i j:A}: j∈ rowT H i ↔ rail H i j:= by rw [rowT,mem_filter,and_iff_right (mem_univ _)]
lemma row_pos (H:Harper A)(i:A)(p:i∈bay H):(rowT H i).Nonempty:=⟨i,row_mem.mpr (bayH.mp p)⟩
def flow (A:Type*)[DecidableEq A](S:Finset (leaf A)):Prop:=∀ i∈S,∀ j∈S,i≠j→Disjoint i.val j.val
def tally(H: Harper A):Finset (leaf A):=(bay H).attach.image fun i=> ⟨rowT H i.val,row_pos H i.val i.property⟩
lemma tal_m {H:Harper A}{x:leaf A}:x∈ tally H↔ ∃ i∈bay H,rowT H i=x.val:=by
 constructor
 · intro p; obtain ⟨i,-,v⟩:=mem_image.mp p; exact ⟨i.val,i.property,congrArg Subtype.val v⟩
 rintro ⟨i,t,v⟩; exact mem_image.mpr ⟨⟨i,t⟩, Finset.mem_attach ..,Subtype.ext v⟩
lemma equal_m (H:Harper A)(x y:A)(p:rail H x y):rowT H x=rowT H y:= Finset.ext fun i=> row_mem.trans ((show rail H x i ↔ rail H y i from ⟨H.tran (H.flip p),H.tran p⟩).trans row_mem.symm)
lemma flagship(H:Harper A):flow A (tally H):=by
 intro i t j l v; obtain ⟨x,-,hx⟩:=tal_m.mp t; obtain ⟨y,-,hy⟩:= tal_m.mp l; rw [←hx,←hy]; refine Finset.disjoint_left.mpr fun {z} k u=>?_ ; exact v (Subtype.ext (hx.symm.trans ((equal_m H x y (H.tran (row_mem.mp k) (H.flip (row_mem.mp u)))).trans hy)))
lemma bay_beam(S: Finset A):bay (beamH S)=S:= Finset.ext fun i=> bayH.trans (mem_product.trans ⟨fun h=>h.1,fun h=>⟨h,h⟩⟩)
lemma bay_hat {H R: Harper A}(p:Disjoint (bay H) (bay R)):bay (H⊔R)=bay H ∪ bay R:= Finset.ext fun i=> by rw [bayH,hut p,mem_union,bayH,bayH]
lemma tal_rail (H:Harper A)(x y:A): rail H x y ↔ ∃ i∈ tally H,x∈i.val∧y∈i.val:=by
 constructor
 · intro h; have ht:=(tract _ _ h).1; let i:leaf A:=⟨rowT H x,row_pos H x ht⟩; exact ⟨i,tal_m.mpr ⟨x,ht,rfl⟩,row_mem.mpr (bayH.mp ht),row_mem.mpr h⟩
 rintro ⟨i,p,l,t⟩; obtain ⟨j,g,v⟩:=tal_m.mp p; rw [←v] at l t; exact H.tran (H.flip (row_mem.mp l)) (row_mem.mp t)
lemma bay_t(H:Harper A):bay H=(tally H).biUnion Subtype.val:= Finset.ext fun i=> by rw [bayH,tal_rail,mem_biUnion]; simp
lemma tal_inj: Injective (tally (A:=A)):=by
 intro i j p; apply harp_ext; ext ⟨x,y⟩ : 1; change rail i x y ↔ rail j x y; rw [tal_rail,tal_rail,p]
def weighH(S:Finset (leaf A)): Harper A:= S.sup fun i=> beamH i.val
def robe(S:Finset (leaf A)):=S.biUnion Subtype.val
lemma flow_m{S T:Finset (leaf A)}(p:flow A S)(h:T⊆S): flow A T:=fun _ g _ l=> p _ (h g) _ (h l)
lemma flow_d{S:Finset (leaf A)}{i:leaf A}(p:flow A (insert i S))(v:i∉S):Disjoint i.val (robe S):=by
 refine Finset.disjoint_left.mpr fun {y} g l=>?_; obtain ⟨j,hx,b⟩:=mem_biUnion.mp l; exact Finset.disjoint_left.mp (p i (mem_insert_self ..) j (mem_insert_of_mem hx) (fun u=>v (u.symm ▸ hx))) g b
lemma weigh_i{S:Finset (leaf A)}(p:flow A S): bay (weighH S)=robe S∧∀ i j:A, rail (weighH S) i j ↔∃ x∈S,i∈x.val ∧j∈x.val:=by
 induction S using Finset.induction_on with
 | empty=> constructor; · rw [weighH,sup_empty,bayB]; simp [robe]
           intro i j; rw [weighH,sup_empty]; exact ⟨fun p=>False.elim (notMem_empty _ p),by simp⟩
 | @insert i S q ih=>
    have ph:= flow_m p (subset_insert i S); obtain ⟨l,u⟩:= ih ph; have ht: Disjoint (bay (beamH i.val)) (bay (weighH S)):=by rw [bay_beam,l]; exact flow_d p q
    rw [weighH, sup_insert]; change bay (_ ⊔ weighH S)=_ ∧ _
    constructor
    · rw [bay_hat ht,l,bay_beam,robe,robe, biUnion_insert]
    intro a b; change rail (beamH i.val ⊔ weighH S) a b↔_; rw [hut ht,u]; have hx: rail (beamH i.val) a b ↔ a∈i.val ∧ b∈i.val:= mem_product; rw [hx]; simp
lemma emblem{S:Finset (leaf A)}(p:flow A S):tally (weighH S)=S:=by
 obtain ⟨l,t⟩:=weigh_i p; let H:= weighH S; have he (x:leaf A)(hx:x∈S)(i:A)(ht:i∈ x.val):rowT H i=x.val:=by
   ext y; rw [row_mem,t]; constructor; swap; · exact fun v=> ⟨_,hx,ht,v⟩
   rintro ⟨w,v,i,g⟩; rw [show x=w from by by_contra q; exact Finset.disjoint_left.mp (p x hx w v q) ht i]; exact g
 ext i : 1; rw [tal_m]; constructor
 · rintro ⟨y,h,u⟩; rw [l] at h; obtain ⟨z,v,b⟩:= mem_biUnion.mp h; exact (show z=i from Subtype.ext ((he z v y b).symm.trans u)) ▸ v
 intro b; obtain ⟨y,v⟩:= i.property; exact ⟨y,l.symm ▸ Finset.mem_biUnion.mpr ⟨i,b,v⟩,he i b y v ⟩
lemma tale_H(H: Harper A):weighH (tally H)=H:= tal_inj (emblem (flagship H))
lemma singHs(S:leaf A):tally (beamH S.val)={S}:=by
 have hp:flow A {S}:=by intro i p j l; rw [mem_singleton] at p l; rw [p,l]; simp
 simpa [weighH] using emblem hp -- tune
end YM.CF.Palot
