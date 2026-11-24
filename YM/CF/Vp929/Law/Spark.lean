import YM.CF.Vp929.Law.Glory
set_option autoImplicit false
set_option maxHeartbeats 520000
noncomputable section
namespace YM.CF.VolumeCape
open Lattice Finset Function Metric Rooms March Filter
open scoped Topology Classical
namespace Delta
variable (C d:Side) {χ χ':Cover→ℕ}{x y:Cover} {B n:ℕ}(s:March)
local notation "H"=> (d.val*C.val)
local notation "T"=> (1000*H)
local notation "W" => ballot χ d C
local notation "P"=> ballot χ' d C
private lemma chart_court(i:Cover)(p:ℕ): s.follow (court i p)=court (s.slide i) p:=by
 apply March.eq_in; intro a; obtain ⟨a,rfl⟩:=s.equi.surjective a; change here (s.slide a)≤ _ ↔ here (s.slide a)≤ _; rw [←s.follows,s.stride_le,Delta.plot_here,s.follows,Delta.plot_here]; exact ⟨fun t=>s.range t,fun t=>by have h:=s⁻¹.range t; rw [s.left,s.left] at h; exact h⟩
private lemma toll_turn (x y:Rooms): toll C (s.follow x) (s.follow y) ↔ toll C x y:=by
 have e(s:March)(x y:Rooms)(t:toll C x y): toll C (s.follow x) (s.follow y):=by
    intro i a b h k; obtain ⟨i,rfl⟩:= s.step.perm.surjective i; obtain ⟨a,rfl⟩:=s.passport i a; obtain ⟨b,rfl⟩:=s.passport i b; rw [stride,s.swing_tips] at h k; have q:= t i a b h k; unfold March.push; split <;> omega
 exact ⟨fun v=>by simpa using e s⁻¹ _ _ v,e s x y⟩
variable (h:χ=χ'∘s.slide)
include h
private lemma survey(y:Cover)(x:Cover): watch χ' d C (s.slide y) (s.slide x) ↔ watch χ d C y x:=by
 have he:= Delta.sympathy χ s χ' h H x; have hx:Range T (s.slide y) (s.slide x) → Range T y x:= fun t=>by simpa only [s.left] using s⁻¹.range t
 exact and_congr he.symm (and_congr ⟨hx,fun v=>s.range v⟩ (by rw [h]; rfl))
lemma orbitB(x:Cover): ballot χ' d C (s.slide x)=ballot χ d C x:=by
 rw [ballot.eq_1,ballot.eq_1 χ d C]; congr 1; ext n; constructor
 · intro e y k; have q:= e (s.slide y) ((survey C d s h x y).2 k); rw [orbitB y,←chart_court,←chart_court] at q; exact (toll_turn C s ..).1 q
 intro e y k; obtain ⟨y,rfl⟩:=s.equi.surjective y; change watch _ _ _ _ (s.slide y) at k; let t:= (survey C d s h ..).1 k; have p:=e y t; change toll C (court (s.slide y) (lotto d C (ballot χ' d C (s.slide y)))) _; rw [orbitB y,←chart_court,←chart_court]; exact (toll_turn C s ..).2 p
termination_by χ x

 decreasing_by all_goals first|exact k.2.2|exact t.2.2
lemma wind_spin: turnClan s (windQ χ d C) (windQ χ' d C):=by
 let p:= survey C d s h; have e(i:Cover):s.follow (clusterQ χ d C i) = clusterQ χ' d C (s.slide i):=by unfold clusterQ; rw [chart_court,orbitB C d s h]
 intro a; constructor
 · rintro ⟨x,v,rfl⟩; exact ⟨s.slide x,(Delta.sympathy _ s _ h H x).1 v,(e x).symm⟩
 rintro ⟨x,v,w⟩; obtain ⟨x,rfl⟩:=s.equi.surjective x; refine ⟨x,(Delta.sympathy _ s _ h H x).2 v,s.fnQ.injective ?_ ⟩; change s.follow _=s.follow _; rw [e]; exact w
lemma paintCharge(a:Rooms): tintCode χ a=tintCode χ' (s.follow a):=by
 unfold tintCode; congr 1; ext i; rw [Set.Finite.mem_toFinset,Set.Finite.mem_toFinset]; constructor
 · rintro ⟨x,e,v⟩; exact ⟨s.slide x, (show here (s.slide x) ≤ s.follow a from s.follows x ▸ ((s.stride_le _ _).2 e)),(by rw [h] at v; exact v)⟩
 rintro ⟨x,e,v⟩; obtain ⟨x,rfl⟩:= s.equi.surjective x; change here (s.slide x) ≤ _ at e; rw [←s.follows,s.stride_le] at e; exact ⟨x,e,h ▸ v⟩
lemma turnMaster(t:Coloring χ B)(a:Rooms)(e:a.bounded B) : s.slide (Master χ a)=Master χ' (s.follow a):=by
 obtain ⟨z,v⟩:=s.equi.surjective (Master χ' (s.follow a)); change s.slide z=_ at v; have hz: here z ≤ a:= (s.stride_le _ _).1 ((follows ..).symm ▸ (v ▸ at_home _ _)); rw [pick t e hz]; exact v; let z':=Master χ a; have he: here (s.slide z') ≤ s.follow a:= follows .. ▸ ((s.stride_le _ _).2 (at_home _ _)); have de:= lowT χ' (s.follow a) (x:=s.slide z') he; rw [←v] at de; change χ z ≤ χ z'; rw [h]; exact de
end Delta
end YM.CF.VolumeCape
