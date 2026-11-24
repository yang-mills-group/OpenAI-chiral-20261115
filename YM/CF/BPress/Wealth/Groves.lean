import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Paths
import YM.Extra.ITERATION_NO_LOSS.Geometry
import YM.CF.BPress.Grid.Thin
/-!
Native stencil supports for gauge charges. Can read complete indicated Slot stencils, pairFoot(B=M_I+2), atom with inspected all; Grove connected. Need exactly these unreshaped arrays before mapping. Partly adapted path geometry lemmas from `Push.AbsoluteSums.Paths` (import exposes their cover-number versions).
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Wealth
open Function Filter Finset Lattice Wilson RG Grid Branch Push.AbsoluteSums
open scoped Topology ContDiff BigOperators Classical
variable {s : Side} {A : Gauge}
local notation "F" => Grid.field 4 s
open Push.AbsoluteSums.Paths Extra.Iteration.Shapes

lemma halo_bay (M:ℕ)(x : Site s) : halo M {x}=bay F x M:= by ext i; simp only [halo_spec,bay_mem]; simp -- tune
lemma halo_one (P: Support s)(b : ℕ) : halo b P = P.biUnion fun i=> bay F i b:= by ext i; simp only [halo_spec,mem_biUnion,bay_mem]; rfl
lemma halo_g (b:ℕ){K:Support s}(p:Grove F K) : Grove F (halo b K):=by
 have h(i : Site s) : i∈ bay F i b:= by rw [bay_mem, (Grid.field ..).reflex]; omega
 have ht : K∪ K.biUnion (fun x=>bay F x b)=halo b K:=by rw [←halo_one K]; exact union_eq_right.mpr (halo_subset ..)
 rw [←ht]; refine (many F _ p K (fun x=>bay F x b) (fun i _=>?_ ) (fun i hi=> ⟨i,hi,h i⟩)).1
 refine trunk_bay F ?_ i b; intro x y; obtain ⟨Q,g,c,u,v,w⟩:= Grid.thin x y le_rfl; exact orig_sub (rooted c x u y v) g
lemma halo_size (x : Site s)(b:ℕ) : (halo b {x}).card ≤ (2*b+1)^4:=by
 convert Corona.halo_size ({x}:Support s) b using 1; rw [card_singleton, one_mul, two_mul] -- tune
lemma walks_g (x : Site s)(w : Walk) : Grove F (native x w):=by
 induction w generalizing x with
 | nil=> rw [native, visits]; simp; apply Grove.single
 | cons a w ih=>
    rw [native, visits,List.toFinset_cons]; apply Grove.join (y:=x+a.vec) (ih ..) (by cases w <;> simp [native, visits]); change separation _ _ ≤ _; rw [separation_comm,separation,add_sub_cancel_left]; apply pdist_vec
lemma walks_first (x : Site s)(w:Walk): x∈ native x w:=by cases w <;> simp [native,visits]
lemma walks_n (x : Site s)(w: Walk): (native x w).card ≤ w.length+1:=by
 induction w generalizing x with|nil=>simp [native,visits]|cons a w ih=>rw [native,visits,List.toFinset_cons]; exact (card_insert_le ..).trans (Nat.add_le_add_right (ih _) _)
private lemma visits_cat {V : Type*} [AddCommGroup V] [One V] (x y : Four V) (w v : Walk) :
    y∈ visits x (w++v) ↔ y ∈ visits x w ∨ y∈ visits (stop x w) v:=by
 induction w generalizing x with
 | nil=> simp only [List.nil_append,visits,List.mem_singleton,stop]; refine ⟨Or.inr,?_⟩; rintro (rfl|v); cases v <;> simp [visits]; exact v
 | cons i w ih=> simp only [List.cons_append, visits,List.mem_cons, ih,stop]; rw [or_assoc]

def foot (x : Site s)(a: Slot) := a.stencil.image (fun p=> wrap s p+x)
lemma foot_native (x:Site s)(a : Slot) : foot x a=native x (a.walk ++ square a.plaq.val.1 a.plaq.val.2):=by
 let h:=a.walk++ square a.plaq.val.1 a.plaq.val.2; have he (w : Walk)(y:Cover) : (visits y w).map (fun i=>wrap s i+x)=visits (wrap s y+x) w:=by induction w generalizing y with|nil=>simp [visits]|cons i w ih=> simp [visits,ih,wrap_vec,add_right_comm]
 have hp: a.stencil=(visits (0:Cover) h).toFinset:=by ext i; simp [h,Slot.stencil,visits_cat,Slot.offset];
 have ht:(visits (0:Cover) h).map (fun i=>wrap s i+x)=visits x h:=by simpa using he h 0
 unfold foot native; change _=(visits x h).toFinset; rw [hp,←ht]; ext; simp
lemma foot_limit (x : Site s)(a : Slot) : x∈foot x a ∧ Grove F (foot x a) ∧ foot x a ⊆ halo a.length {x} ∧ (foot x a).card ≤ a.length+1:=by
 rw [foot_native]; refine ⟨walks_first ..,walks_g ..,fun i h=>?_ , (walks_n ..).trans_eq ?_⟩; swap; · rw [List.length_append]; rfl
 exact halo_spec.mpr ⟨x,mem_singleton_self x,(Paths.to_ball x _ h).trans_eq (List.length_append ..)⟩
lemma bundle_foot (x:Site s){k:ℕ}(l:Fin k → Slot) : bundle x l={x}∪univ.biUnion fun i=> foot x (l i):=by rw [singleton_union]; rfl
lemma bundle_limit (x:Site s){k:ℕ}(l : Fin k→ Slot) : x ∈ bundle x l ∧ Grove F (bundle x l) ∧ (bundle x l).card ≤ length l+k+1:=by
 rw [bundle_foot]; obtain ⟨h,t⟩:= many F _ (Grove.single x) univ (fun i=> foot x (l i)) (fun i _=> (foot_limit x (l i)).2.1) (fun i _=> ⟨x,mem_singleton_self _,(foot_limit x (l i)).1⟩); refine ⟨mem_union_left _ (mem_singleton_self _),h,t.trans ?_⟩; apply le_trans (add_le_add_right (sum_le_sum (fun i (_:i∈ (univ:Finset (Fin k)))=> (foot_limit x (l i)).2.2.2)) _); rw [sum_add_distrib,card_singleton]; simp [Paths.length,add_assoc,add_left_comm]; omega
lemma touched_limit (p : Face (Per s)): p.1∈touched p∧ Grove F (touched p) ∧ touched p ⊆ halo 2 {p.1}:= ⟨walks_first .., walks_g .., fun i v=> halo_spec.mpr ⟨p.1,mem_singleton_self _,Work.E01.sep_touched p i v⟩⟩ -- hull geometry tightened
lemma inspect_g {P: Support s}(p:Grove F P): Grove F (inspected P):=by
 unfold inspected; let S:=univ.filter fun i:Face (Per s)=> ¬ Disjoint P (touched i); have he:S.biUnion touched=Finset.univ.biUnion fun p:Face (Per s)=> if Disjoint P (touched p) then ∅ else touched p:=by
    ext i; simp only [mem_biUnion,mem_filter,mem_univ,true_and,exists_true_left,S]; refine exists_congr fun j=>?_ ; by_cases h:Disjoint P (touched j)<;> simp [h]
 rw [←he]; exact (many F _ p S touched (fun i _=> (touched_limit ..).2.1) (fun i h=> Finset.not_disjoint_iff.mp (mem_filter.mp h).2)).1
lemma atom_limit {k:ℕ} (o : Site s)(a : Atom A k) : let P:=inspected (a.footprint o); o∈P ∧ Grove F P ∧ P⊆ halo (a.length+8) {o} ∧ P.card ≤ (a.length+k+1)*17^4:=by
 intro P; obtain ⟨p,v,h⟩:= bundle_limit o a.leg; rw [←atom_foot o a] at v h p; let Q:=a.footprint o; have hp : P⊆halo 8 Q:=by intro i w; obtain ⟨j,l,t⟩:= inspect_dist Q w; exact halo_spec.mpr ⟨j,l,(separation_comm ..).le.trans t⟩
 refine ⟨mem_union_left _ p,inspect_g v,fun i t=>?_,(card_le_card hp).trans ((Corona.halo_size ..).trans (Nat.mul_le_mul_right _ h))⟩; obtain ⟨j,h,g⟩:=halo_spec.mp (hp t); rw [show Q=bundle o a.leg from atom_foot ..] at h; exact halo_spec.mpr ⟨o, mem_singleton_self _, (separation_triangle o j i).trans (Nat.add_le_add (where_slot o a.leg j h) g)⟩
open ConnectedActivityE6.Raw
lemma pair_limit {M:ℕ}(o:Face (Per s))(T : PathData A)(i:ℕ×ℕ): let l:= length (duplex T o.2 i); let P:=pairFoot (M+2) T o i; o.1 ∈ P ∧ Grove F P ∧ P⊆ halo (M+l+2) {o.1} ∧ P.card ≤ l+3+(2*M+5)^4:=by
 intro l P; obtain ⟨a,v,h⟩:=bundle_limit o.1 (duplex T o.2 i); let B:=halo (M+2) {o.1}; have hp:o.1∈ B:=halo_subset _ _ (mem_singleton_self _); refine ⟨mem_union_left _ hp, (halo_g (M+2) (Grove.single o.1)).unite v hp a,fun x hx=> ?_, (card_union_le ..).trans ?_⟩
 · apply halo_spec.mpr; refine ⟨o.1,mem_singleton_self _,?_⟩; rcases mem_union.mp hx with g|g; · obtain ⟨j,g,h⟩:=halo_spec.mp g; rw [mem_singleton.mp g] at h; omega
   refine (where_slot o.1 (duplex T o.2 i) x g).trans (show l≤ _ by omega)
 have he:= halo_size o.1 (M+2); rw [show 2*(M+2)+1=2*M+5 by omega] at he; refine (add_le_add he h).trans ?_; omega
end YM.CF.BPress.Wealth
