import YM.CF.BPress.Palmer.Basics
import YM.CF.BPress.Locale.Atlas
/-! Core selections via overlap graph on radius-r block balls. ! -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Contour
open RG Wilson Lattice Finset Function Branch Locale Cube Palmer Grid
open scoped Classical BigOperators
-- caution `BranchC` lives in Palmer.School. core set as plain finite sets (exists finite options); avoid decidabilities
variable {Y:Type}[DecidableEq Y][Fintype Y]
def Core (Z:Y→ Seal Y)(Q:Seal Y) := Spark Z Q
def station (Z:Y→ Seal Y)(o:Seal Y):= o.biUnion Z
variable {Z:Y→ Seal Y}
def Visible (Z:Y→Seal Y) (T:Finset Y)(E:Finset Y) := (Parts Z E).filter fun Q=>¬ Disjoint (station Z Q) T
abbrev watches (Z:Y→Seal Y)(T:Finset Y)(E:Finset Y) : Finset Y:= T∪ (Visible Z T E).biUnion (station Z)
abbrev Crew (Z:Y→Seal Y)(Q:Seal Y) := Core Z Q
variable (h:∀ i,i∈Z i)
lemma pins (Q:Seal Y)(h:∀ i,i∈ Z i): Q⊆ station Z Q:= fun i g=> mem_biUnion.mpr ⟨i,g,h _⟩
variable {P Q E S:Finset (Finset Y)}(Z)
def Fleet (P:Finset (Finset Y)) :Prop:= (∀ i∈ P, Core Z i) ∧ (↑P : Set _).PairwiseDisjoint (station Z)
abbrev floor (P:Finset (Finset Y)):= P.biUnion id
abbrev berth (P:Finset (Finset Y)):= P.biUnion (station Z)
lemma gathering (Q:Finset Y): Fleet Z (Parts Z Q):= ⟨fun i l=> lives Z Q l|>.2, separate Z Q⟩
variable {Z}
lemma Fleet.singleton {q: Finset Y}(p:Core Z q):Fleet Z {q}:= ⟨fun i l=> mem_singleton.mp l ▸ p,fun _ va _ vb e=> False.elim (e ((mem_singleton.mp va).trans ((mem_singleton.mp vb).symm)))⟩
lemma Fleet.empty : Fleet Z ∅:= ⟨fun _ h=>False.elim (notMem_empty _ h), fun i h=>False.elim (notMem_empty _ h)⟩
lemma Fleet.subs (h:Fleet Z P)(v:S⊆P): Fleet Z S:= ⟨fun i u=> h.1 i (v u), fun i l j t e=> h.2 (v l) (v t) e⟩
lemma Fleet.stays (p:Fleet Z P): Parts Z (floor P)= P:=separates Z _ p.1 p.2
lemma Fleet.grow (h:Fleet Z P)(p:Fleet Z Q)(g:Disjoint (berth Z P) (berth Z Q)):Fleet Z (P∪Q):=by
 refine ⟨fun i v=>(mem_union.mp v).elim (h.1 i) (p.1 i), fun i v j l e=>?_⟩; rcases mem_union.mp v with v|v <;> rcases mem_union.mp l with l|l; exact h.2 v l e; exact g.mono (subset_biUnion_of_mem _ v) (subset_biUnion_of_mem _ l); exact g.symm.mono (subset_biUnion_of_mem _ v) (subset_biUnion_of_mem _ l); exact p.2 v l e
lemma Fleet.saw {T:Finset Y}(p:Fleet Z (P∪Q))(h:Disjoint (berth Z Q) T): Visible Z T (floor (P∪Q))= Visible Z T (floor P):=by
 rw [Visible,Visible,p.stays,(p.subs subset_union_left).stays]; ext i; refine ⟨fun v=> ?_,fun v=>?_⟩; obtain ⟨a,b⟩:= mem_filter.mp v; exact mem_filter.mpr ⟨(mem_union.mp a).resolve_right (fun v=> b (h.mono_left (subset_biUnion_of_mem _ v))),b⟩; exact filter_subset_filter _ subset_union_left v -- tune
lemma view_inside (Z:Y→Seal Y)(T E:Finset Y) : Visible Z T E ⊆ Parts Z E:= filter_subset ..
-- characterize geometry. intersection iff...
variable {s:Side}{b:BandWidth}(X:Bands s b)(R:Hangar s)(r:ℕ)
abbrev Gilt : SiteX X R → Seal (SiteX X R):= fun i=> bay (shape X R) i r
lemma approach (i j:SiteX X R)(m n:ℕ)(h:(shape X R).span i j ≤ m+n):∃ y:SiteX X R, (shape X R).span i y ≤m∧ (shape X R).span y j≤ n:=by
 induction n generalizing j with
 |zero=> exact ⟨j,h,(shape X R).reflex j|>.le⟩
 |succ n ih=> obtain ⟨z,q,e⟩:= in_shape X R i j (m+n) ((bay_mem _).mpr h); obtain ⟨x,p,t⟩:= ih z ((bay_mem _).mp q); exact ⟨x,p,(shape X R).tri x z j|>.trans (add_le_add t e)⟩
lemma meets_core (i j:SiteX X R) : ¬ Disjoint (Gilt X R r i) (Gilt X R r j) ↔ (shape X R).span i j≤ r+r:=by
 rw [Finset.not_disjoint_iff]; let Z:=shape X R; constructor; · rintro ⟨i,t,v⟩; exact (Z.tri _ i _).trans (add_le_add ((bay_mem _).mp t) ((Z.sym ..).le.trans ((bay_mem _).mp v))) -- tune shadows
 intro e; obtain ⟨z,p,q⟩:= approach X R i j r r e; exact ⟨z,(bay_mem _).mpr p,(bay_mem _).mpr (((shape X R).sym ..).le.trans q)⟩
lemma own_gilt (i:SiteX X R): i∈ Gilt X R r i:= (bay_mem _).mpr (((shape X R).reflex _).le.trans (Nat.zero_le _))
lemma gilt_far {P Q : Seal (SiteX X R)}{i j : SiteX X R}(di:Disjoint (station (Gilt X R r) P) (station (Gilt X R r) Q))(hp:i∈ P)(ht:j∈ Q): r+r < (shape X R).span i j:= lt_of_not_ge fun v=> meets_core X R r i j|>.mpr v (di.mono (subset_biUnion_of_mem _ hp) (subset_biUnion_of_mem _ ht)) -- pipe tune
end YM.CF.BPress.Contour
