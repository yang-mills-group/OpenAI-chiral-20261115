import YM.CF.BPress.Grid.Cover
import YM.CF.BPress.Grid.Line
/-! Connect purchases on the micro lattice, at price per path length. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Grid
open Relation Function Finset Lattice Cube Branch
open scoped Topology BigOperators Classical
variable {d n : ℕ}{s : Side}{G : Gauge}
private lemma decrease (i j : Per s) (n:ℕ)(p:delta1 s i j≤ n+1): ∃ t, delta1 s i t≤ n ∧ delta1 s t j≤1:=by
  let a :ℤ:= (j-i).valMinAbs; let b:=SignType.sign a -- tune
  have ha: a*2∈ Set.Ioc (- (s.val:ℤ)) s.val:= ZMod.valMinAbs_mem_Ioc _; have hj: j=i+↑a:=by unfold a; rw [ZMod.coe_valMinAbs]; abel
  have hb: a.natAbs≤ n+1:=(d_sym j i).symm.le.trans p -- tune
  by_cases x: a.natAbs≤n; · exact ⟨j,(d_sym ..).le.trans x,by rw [d_id]; omega⟩
  obtain ⟨p,e⟩:=Set.mem_Ioc.mp ha
  rcases lt_or_ge a 0 with t|t
  · let k:=i+(↑(a+1):Per s); have hx:(k-i).valMinAbs=a+1:= (ZMod.valMinAbs_spec ..).mpr ⟨by unfold k; simp,by rw [Set.mem_Ioc]; omega⟩; refine ⟨k,?_,?_⟩
    · rw [d_sym,delta1,hx]; omega
    rw [show k=j+(↑(1:ℕ):Per s) from (by unfold k; rw [hj]; push_cast; rw [add_assoc])]; exact delta_nat ..
  let k:=i+(↑(a-1):Per s); have hx:(k-i).valMinAbs=a-1:= (ZMod.valMinAbs_spec ..).mpr ⟨by unfold k; simp,by rw [Set.mem_Ioc]; omega⟩; refine ⟨k,?_,?_⟩
  · rw [d_sym,delta1,hx]; omega
  nth_rw 1 [d_sym]; rw [show j=k+(↑(1:ℕ):Per s) from (by unfold k; rw [hj]; push_cast; abel)]; exact delta_nat ..
lemma decrease_bay (x y : Space d s) (p:delta x y ≤ n+1) :∃ z, delta x z≤n∧ delta z y≤1:= by
 choose z a b using fun i=> decrease (x i) (y i) n ((delta_at ..).trans p); exact ⟨z,delta_le.mpr a,delta_le.mpr b⟩
lemma thin (x y: Space d s)(p:delta x y ≤ n): ∃ S⊆ bay (field d s) x n, Grove (field d s) S∧x∈S ∧ y∈ S ∧ S.card≤ n+1:=by
  induction n generalizing y with
  | zero=>
    have he:= eq_of_delta x y (Nat.eq_zero_of_le_zero p); rw [←he]; exact ⟨{x},singleton_subset_iff.mpr (show _ from (bay_mem 0|>.mpr (delta_same x|>.le))),.single _,mem_singleton_self _,mem_singleton_self _,by simp⟩
  | succ n ih=>
    obtain ⟨z,v,g⟩:=decrease_bay x y p; obtain ⟨S,t,u,h,q,i⟩:= ih z v; exact ⟨insert y S, insert_subset ((bay_mem _).mpr p) (fun i hi=>(bay_mem _).mpr ((bay_mem _|>.mp (t hi)).trans (by omega))),Grove.join u q ((delta_comm ..).le.trans g),mem_insert_of_mem h,mem_insert_self ..,(card_insert_le ..).trans (by omega)⟩

lemma many {X I :Type} [Fintype X][DecidableEq X][DecidableEq I] (A:Branch.Field X) (S:Finset X)(h:Grove A S)(s:Finset I)(f:I→ Finset X)(t:∀ i∈s,Grove A (f i))(p:∀ i∈s,∃ x∈S,x∈ f i):
    Grove A (S ∪ s.biUnion f) ∧ (S∪ s.biUnion f).card ≤ S.card+∑ i∈s,(f i).card:=by
  refine ⟨?_,(card_union_le ..).trans (add_le_add_right card_biUnion_le _)⟩; induction s using Finset.induction_on with
  | empty=> simpa using h
  | insert i s g ih=>
    rw [biUnion_insert, union_left_comm] -- motive?
    obtain ⟨x,h,v⟩:= p i (mem_insert_self ..); exact (t i (mem_insert_self ..)).unite (ih (fun i z=>t _ (mem_insert_of_mem z)) (fun i z=>p _ (mem_insert_of_mem z))) v (mem_union_left _ h)

variable (x : Space d s)(i : Fin d)
def rail(k:ℕ) := (range (k+1)).image fun k=> hop x i k
lemma on_rail {u k:ℕ}(h:u≤k): hop x i u∈ rail x i k:= mem_image_of_mem _ (mem_range_succ_iff.mpr h)
lemma rail_g (k:ℕ) : Grove (field d s) (rail x i k) := by
 induction k with
 | zero=> rw [rail]; simp; exact Grove.single _
 | succ k ih=> rw [rail,range_add_one,image_insert]; apply Grove.join ih (on_rail x i le_rfl); rw [← hop_hop]; exact (delta_comm ..).le.trans (delta_hop ..)
def whole (r:ℕ):= {x}∪ (univ.biUnion fun i:Fin d=> rail x i r)
lemma paid_rail (r:ℕ):
    x∈whole x r ∧ Grove (field d s) (whole x r) ∧ (whole x r).card ≤ (r+1)*(d+1) ∧ whole x r ⊆ bay (field d s) x r:= by
 obtain ⟨h,t⟩:=many _ _ (Grove.single x) univ (fun i:Fin d=> rail x i r) (fun i _=> rail_g ..) (fun i _=> ⟨x,mem_singleton_self _,by simpa only [hop_zero] using on_rail x i (Nat.zero_le r)⟩); refine ⟨mem_union_left _ (mem_singleton_self _),h, t.trans ?_,?_⟩
 · have he : ∀ i, (rail x i r).card≤r+1:= fun i=> card_image_le.trans_eq (card_range _); have hp:=sum_le_sum (fun i (_: i∈ (univ:Finset (Fin d)))=> he i); simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hp; rw [card_singleton]; refine (add_le_add_right hp 1).trans ?_; nlinarith
 intro i p; apply (bay_mem _).mpr; rcases mem_union.mp p with q|q; rw [mem_singleton.mp q, (field ..).reflex]; omega; obtain ⟨j,_,g⟩:=mem_biUnion.mp q; obtain ⟨k,h,rfl⟩:=mem_image.mp g; exact (delta_hop ..).trans (mem_range_succ_iff.mp h)

def equalOn (U V : GaugeField G d s)(S: Finset (Space d s)) := ∀ (x: WalkEdge d s), x.1∈S → hop x.1 x.2 1 ∈ S → U x=V x
lemma equal_weaken {U V : GaugeField G d s}{S T:Finset (Space d s)} (p: equalOn U V S)(u : T⊆ S): equalOn U V T:= fun i a b=> p i (u a) (u b)
lemma equal_line {U V:GaugeField G d s}(u : ℕ)(p:equalOn U V (rail x i u)) : line U x i u=line V x i u:= by
 induction u with
 | zero=> rfl
 | succ u ih=>
   rw [line_succ,line_succ, ih _]; swap; · exact equal_weaken p (Finset.image_subset_image (f:=fun k=> hop x i k) (range_mono (Nat.le_succ _)))
   rw [p _ (on_rail x i (Nat.le_succ _)) ?_]; simp only [hop_hop]; exact on_rail x i le_rfl
end YM.CF.BPress.Grid
