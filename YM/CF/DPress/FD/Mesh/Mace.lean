import YM.CF.DPress.FD.Law.Muse


set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Lattice Finset Cash
open scoped Topology BigOperators ENNReal NNReal Classical
variable {n:Side} {r k:ℕ}
open Bifold Deck
namespace Hue
abbrev sizeQ:=Fintype.card Signed
abbrev Koran(p r:ℕ):= 2*(p*r)
abbrev pal (U:Deck r) :Finset (Deck r):= univ.image (fun s:Signed=> δPsi s U)
lemma size_p : 0<sizeQ:=Fintype.card_pos
lemma value_cap (U:Deck r): (pal U).card ≤ sizeQ:= card_image_le.trans_eq card_univ -- replace
lemma pal_t(s:Signed)(U:Deck r): pal (δPsi s U)= pal U:=by
 ext i; rw [pal,pal,mem_image,mem_image]; constructor<;> rintro ⟨x,t,v⟩
 · exact ⟨s*x,mem_univ _,by rw [δΨ_add]; exact v⟩
 exact ⟨s⁻¹*x,mem_univ _,by rw [←δΨ_add,mul_inv_cancel_left]; exact v⟩
lemma own(U:Deck r): U∈ pal U:= mem_image.mpr ⟨1,mem_univ _, δΨ_id _⟩
abbrev clear (m k:ℕ) := m=k -- remove
variable {I:Type*} (d: Site n→ I)
def next (r:ℕ)(F:Support n):Support n:=Finset.univ.filter (fun i=>∃ j∈ F,separation i j≤ r∧ d j=d i)
local notation "Z'"=> Site n
abbrev twinr (r:ℕ)(D:Z')(V:Z'):Prop:= separation D V ≤ r∧ d D=d V
def cluster (r:ℕ)(i : Z') : ℕ→Support n
| 0=>{i}
| j+1=> (Hue.next d r (cluster r i j))
lemma memo (S: Support n) (t v: Z') : t∈Hue.next d r S ↔∃ i∈ S,separation t i≤r∧d i=d t:=by simp [Hue.next]
lemma spread (F:Support n):F⊆ Hue.next d r F:=by intro i t; exact (memo d F i i).2 ⟨i,t,separation_self i |>.trans_le (Nat.zero_le r),rfl⟩
lemma grow {S T:Support n}(t:S⊆T) : Hue.next d r S ⊆ Hue.next d r T:=by intro i p; obtain ⟨j,v,w⟩:= (memo d S i i).1 p; exact (memo d T i i).2 ⟨j,t v,w⟩
variable {i j: Site n}
lemma head (k:ℕ): i∈cluster d r i k:=by
 induction k with
 | zero=> exact mem_singleton_self _
 | succ k h=> exact spread d _ h
lemma side_t (x:Support n) (p:∀ y∈ x,d y=d i∧ separation i y≤k)(z:Z')(u:z ∈ Hue.next d r x) : d z=d i ∧ separation i z ≤ k+r:=by obtain ⟨j,b,t,h⟩:= (memo d x z z).1 u; obtain ⟨x,p⟩:=p j b; exact ⟨h.symm.trans x,(separation_triangle i j z).trans (Nat.add_le_add p ((separation_comm ..).trans_le t))⟩
lemma side_C (k:ℕ)(j:Z')(u:j∈ cluster d r i k):d j=d i∧ separation i j≤k*r:=by
 induction k generalizing j with|zero=> rw [show j=i from mem_singleton.mp u,separation_self]; simp|succ k h=> rw [add_mul,one_mul]; exact side_t d _ h _ u
lemma stick (t:cluster d r i k=(cluster d r i (k+1))){m:ℕ}(p:k≤m) : cluster d r i m=cluster d r i (m+1):=by
 induction m,p using Nat.le_induction with|base=> exact t|succ i p h=> exact congrArg (Hue.next d r) h
lemma bigger : Monotone (fun k=>cluster d r i k):= monotone_nat_of_le_succ (fun i=> spread d _)
lemma ahead(k:ℕ)(t:twinr d r i j) : cluster d r i k⊆ cluster d r j (k+1):=by
 induction k with|zero=> exact singleton_subset_iff.mpr ((memo d _ i i).2 ⟨j,mem_singleton_self _,t.1,t.2.symm⟩)|succ k ih=> exact grow d ih
open Deck
variable {pQ:ℕ} (m: 2*Koran pQ r<n.val)(X: Deck.X m) (hc:sizeQ≤pQ)
abbrev ψ(x: Site n):= pal (host m X x)
abbrev heap(s: Site n):= cluster (ψ m X) r s pQ
local notation "D"=> ψ m X
include hc
lemma compact(y:Z'): (heap m X y).card ≤ pQ:=by
 let S:= heap m X y; let f:=host m X; have h : Set.InjOn f S:= by
    intro i p j v e; by_contra z; refine Deck.merit m _ _ z (show _≤ Koran pQ r from ?_) X e
    have he:separation i y ≤pQ*r:= (separation_comm ..).trans_le (side_C D _ i p).2; have hp:=(side_C D (i:=y) pQ j (v : j∈S)).2; unfold Koran; exact (separation_triangle i y j).trans (by omega)
 -- pos.H.Bary.Any.Partition.
 refine ((card_image_iff ..).2 h).symm.trans_le ((card_le_card (show Finset.image f S⊆ D y from ?_)).trans ((value_cap (f y)).trans hc))
 intro t hp; obtain ⟨i,p,rfl⟩:=mem_image.mp hp; exact (side_C D pQ i p).1 ▸ own (f i)
lemma verdict(y:Z'): heap m X y= cluster D r y (pQ+1):=by
 let f:= cluster D r y; by_contra! q; have he(i:ℕ)(t:i≤pQ): f i<f (i+1):=by
    apply lt_of_le_of_ne (spread D _); exact fun v=> q (stick D v t) -- signature eq
 have hp(k:ℕ)(h:k≤pQ): k<(f k).card :=by induction k with|zero=> change 0<({y}:Finset _).card; simp|succ k ih=> have hr:= ih (by omega); have hx:= Finset.card_lt_card (he k (by omega)); omega
 exact not_le.mpr (hp pQ le_rfl) (compact m X hc y)
lemma herd (h:twinr D r i j):heap m X i=heap m X j:=Subset.antisymm ((verdict m X hc j).symm ▸ (ahead D pQ h)) ((verdict m X hc i).symm ▸ (ahead D pQ (show twinr D r j i from ⟨(separation_comm ..).trans_le h.1,h.2.symm⟩)))
end Hue
end YM.CF.DPress.FD
