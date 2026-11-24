import YM.CF.Vp929.Law.Motion
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 520000
noncomputable section
namespace YM.CF.VolumeCape
open Lattice Finset Function
open scoped Classical
namespace Rooms
variable {x y z:Cover} {v w B:Rooms}{i j:Axis}(s:March)
def span(x y:Cover) :Rooms:=fun i=> ⟨min (x i) (y i),max (x i) (y i),(min_le_left ..).trans (le_max_left ..)⟩
abbrev zone(p:Edge Cover):Rooms:=span p.1 (p.1+step p.2)
lemma spanFits : span x y ≤ B ↔ here x ≤ B ∧ here y ≤ B:=by
 constructor
 · intro h; constructor <;> intro i <;> obtain ⟨e,v⟩:= Wall.full (h i) <;> change _ ≤ min _ _ at e <;> change max _ _ ≤ _ at v <;> exact ⟨(by change _ ≤ _; dsimp [here,Wall.lone]; omega),(by dsimp [here,Wall.lone]; omega)⟩
 intro ⟨e,v⟩ i; obtain ⟨e,t⟩:=Wall.seen (e i); obtain ⟨p,k⟩:= Wall.seen (v i); exact ⟨le_min e p,max_le t k⟩
lemma spanT : (span x y).Tiny ↔ Range 1 x y:=by
 constructor <;> intro h i <;> obtain h:= h i
 · change max (x i) (y i) ≤ min _ _ + 1 at h; omega
 change max _ _ ≤ min _ _ + 1; omega
@[simp] lemma spanComm (x y:Cover): span x y=span y x:=by funext i; simp only [span]; apply Wall.ext <;> dsimp <;> omega
lemma span_fixed(x:Cover)(i:Axis): Tiny (span x (x+step i)):=spanT.mpr fun j=>by simp only [Pi.add_apply,step_apply]; split <;> omega
lemma spanEq : s.follow (span x y)=span (s.slide x) (s.slide y):=by funext j; obtain ⟨i,rfl⟩:=s.step.perm.surjective j; apply Wall.ext <;> rw [s.stride] <;> simp only [span,March.swing,March.drift, s.footstep] <;> split <;> dsimp [March.reverse] <;> omega
abbrev marks (x:Rooms):Set Cover:={y|here y ≤ x}
lemma finite (x:Rooms):x.marks.Finite:=(Set.finite_Icc x.foot x.headB).subset fun y v=> ⟨fun i=>(Wall.seen ((show here y ≤x from v) i)).1,fun i=>(Wall.seen ((show here y≤x from v) i)).2⟩
end Rooms
namespace Tour
open Rooms
variable {x y z:Cover} (v:Rooms)
def taxi(x y:Cover):ℕ:=∑ i:Axis,(x i-y i).natAbs
lemma route (p:here x ≤ v)(q:here y ≤ v)(u:x≠y):∃ z:Cover,here z ≤ v ∧(∃ i,z=x+step i∨x=z+step i) ∧ taxi x y= taxi z y+1:=by
 obtain ⟨i,h⟩:= Function.ne_iff.mp u; let a:= x i; let b:=y i; let c:ℤ:= if a < b then a+1 else a-1; have hv:a≠b:=h
 let z:=update x i c; have Z:z i=c:=update_self ..; have e :=Wall.seen (p i); have q':=Wall.seen (q i); change _ ≤ a∧a ≤ _ at e; change _ ≤ b ∧ b ≤ _ at q'
 refine ⟨z,?_, ?_,?_⟩
 · intro j; by_cases t:j=i; subst j; change Wall.lone (z i) ≤ _; rw [Z]; exact ⟨show _ ≤ c from by unfold c; split <;> omega, show c ≤ _ from by unfold c; split <;> omega⟩
   change Wall.lone (z j) ≤ _; rw [show z j=x j from update_of_ne t ..]; apply p j
 · refine ⟨i,?_⟩; by_cases t:a<b
   · left; funext j; by_cases p:j=i
     · subst j; simp [z,c,t,a]
     simp [z,p]
   right; funext j; by_cases p:j=i; subst j; simp [z,c,t,a]; simp [z,p]
 let H:(x i-y i).natAbs= (z i-y i).natAbs+1:=by rw [Z]; change (a-b).natAbs=(c-b).natAbs+1; unfold c; split <;> omega
 unfold taxi; rw [← Finset.add_sum_erase _ _ (mem_univ i),←Finset.add_sum_erase _ (fun j=>(z j-y j).natAbs) (mem_univ i)]; rw [H,Finset.sum_congr (rfl:univ.erase i=univ.erase i) (f:=fun j:Axis=>(z j-y j).natAbs) (g:=fun j=>(x j-y j).natAbs) (fun j p=>by rw [show z j=x j from update_of_ne (mem_erase.mp p).1 ..])]; omega
end Tour
end YM.CF.VolumeCape
