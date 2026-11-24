import YM.SU5.Selected.Lantern.Lore
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
-- adapt `Emperor` for Cab. Ordered List and geometrical partitions. Treat Mark support votes even.
variable {n:Side}(L:List (Cab n)) {U P:List (Cab n)}
    (M:Tulip.Male)(j w t :ℕ)(τ η ξ J R δ:ℝ)(q:Type)[Fintype q][DecidableEq q](r:ℕ)
abbrev Resort := List.foldr (fun A S=>A.broad ∪ S) ∅ L -- abbrev not needed
abbrev guest : Buffered.Mark n:= (L.map Cab.frame).prod
structure Service (L:List (Cab n)): Prop where
 guests : ∀ A∈L, Lounge M j w t τ η ξ J R δ q r A
 border: L.Pairwise (fun A B=> Disjoint A.broad B.broad)
variable {L M j w t τ η ξ J R δ q r}
lemma resident (z:Seat n) : z∈ Resort L↔∃ i∈L,z∈ i.broad:=by induction L with|nil=> simp [Resort]|cons i L ih=>change z ∈ i.broad ∪ Resort L ↔ _; simpa [ih,or_and_right,exists_or]
lemma resort_duc (L U:List (Cab n)) : Resort (L++U)= Resort L∪Resort U:=by ext; simp only [resident,List.mem_append,mem_union,or_and_right,exists_or]
lemma broad_dine {A:Cab n}(h:A∈L): A.broad⊆ Resort L:= fun x p=> resident ..|>.mpr ⟨_,h,p⟩
lemma guest_comb (L U:List (Cab n)): guest (L++U)=guest L*guest U:=by unfold guest; rw [List.map_append,List.prod_append]
lemma visits_C (x:Fields n)(L:List (Cab n)) : guest L x= fo (fun i=> i.frame x) L:=by induction L with|nil=>rfl|cons A L h=>rw [show guest _ x=A.frame x*guest L x from rfl,h]; rfl
namespace Service
variable (p: Service M j w t τ η ξ J R δ q r L)
include p
lemma less (h:U.Sublist L): Service M j w t τ η ξ J R δ q r U:=⟨fun i e=>p.guests i (h.mem e), p.border.sublist h⟩ -- signature
lemma append (u:Service M j w t τ η ξ J R δ q r U) (z:Disjoint (Resort L) (Resort U)) : Service M j w t τ η ξ J R δ q r (L++U):= ⟨fun A p'=> (List.mem_append.mp p').elim (p.guests A) (u.guests A),List.pairwise_append.mpr ⟨p.border,u.border,fun a i b t=>z.mono (broad_dine i) (broad_dine t)⟩⟩
lemma apart {A B:Cab n}(h:A∈L)(t:B∈L)(e:A≠B): Disjoint A.broad B.broad:= by
 have g:=p.border; clear p; induction L with
 | nil=> simp at h
 | cons T L ih=>
    rcases List.pairwise_cons.mp g with ⟨u,v⟩; rcases List.mem_cons.mp h with h|h <;> rcases List.mem_cons.mp t with t|t
    · exact False.elim (e (h.trans t.symm))
    · subst A; exact u _ t
    · subst B; exact (u _ h).symm
    exact ih h t v
lemma nodup : L.Nodup:=by
 induction L with
 | nil=>exact List.nodup_nil
 | cons A L ih=>
    refine List.nodup_cons.mpr ⟨fun h=>?_,ih (p.less (by simp))⟩; obtain ⟨v,hp⟩:= (p.guests A List.mem_cons_self).shape; exact disjoint_left.mp ((List.pairwise_cons.mp p.border).1 _ h) hp hp
lemma permit {T:Finset (Seat n)}(u:Resort L⊆ T): AtSupport false T (guest L):=by
 induction L with
 | nil=>exact AtSupport.oneM _
 | cons A L ih=>
    change A.broad∪Resort L⊆T at u; exact (((p.guests _ List.mem_cons_self).env.mono (subset_trans subset_union_left u)).mulM (ih (p.less (by simp)) (subset_trans subset_union_right u)))
lemma guests_v (x:Fields n)(u:0≤J):‖guest L x‖ ≤ J^(L.length*r):=by
 induction L with
 |nil => simp [guest]
 |cons A L ih=>
    rw [show guest _ x=A.frame x*guest L x from rfl,List.length_cons, Nat.add_mul,one_mul, pow_add,mul_comm]; apply (norm_mul_le ..).trans; exact mul_le_mul ((p.guests _ List.mem_cons_self).expense x) (ih (p.less (by simp))) (norm_nonneg _) (by positivity)
omit p in
lemma alone {A:Cab n}(p: Lounge M j w t τ η ξ J R δ q r A): Service M j w t τ η ξ J R δ q r [A] := ⟨fun A' h=>by obtain rfl:= List.mem_singleton.mp h; exact p, List.pairwise_singleton _ _⟩
lemma back (i:Axis)(s:ℤ)(v:safeReflect M j δ n): Service M j w t τ η ξ J R δ q r (L.map (fun x=> x.shadow i s)):=by
 constructor; · intro A u; obtain ⟨a,h,rfl⟩:= List.mem_map.mp u; exact (p.guests a h).shadow i s v
 apply List.pairwise_map.mpr; exact p.border.imp (fun {a b} p=> (disjoint_image ((show Involutive _ from fling_there (n:=n) i s).injective)).2 p)
omit p
lemma back_refl (L:List (Cab n))(i:Axis)(s:ℤ): guest (L.map (fun x=>x.shadow i s))= reflMark i s (guest L):=by
 induction L with
 | nil=> exact funext (fun x=>(theta_one _).symm)
 | cons A L ih=>
    rw [List.map_cons]; change _ *guest _=reflMark i s (A.frame* guest L); rw [ih]; funext x; unfold reflMark; simp only [Pi.mul_apply,theta_mul]; rfl
lemma back_wall (L:List (Cab n))(i:Axis)(s:ℤ): Resort (L.map (fun x=>x.shadow i s))= hyphen i s (Resort L):=by
 induction L with| nil=> rfl| cons A L ih=> change _∪ Resort _= hyphen i s (A.broad∪ Resort L); rw [ih]; exact (image_union ..).symm
end Service
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern
#print axioms Service.permit
#print axioms Service.back_refl
#print axioms Service.back
#print axioms Service.guests_v
