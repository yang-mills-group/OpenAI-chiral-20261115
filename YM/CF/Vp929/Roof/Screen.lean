import YM.CF.Vp929.Roof.Cane
import YM.CF.Skye.Man
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.VolumeCape
open Finset Function Mesh Lattice Rooms Atlas Delta Guide MeasureTheory Palace Mos Mesa Cube Lat
open scoped Topology Classical NNReal Matrix.Norms.Frobenius
namespace Cane
variable (C:Side)(K:ℕ→ℝ)(P:Record C)(t:Trust C P)(A:Realms)
local notation "R"=> Fringe C
abbrev shiftV(a:Cover):March:=⟨1,false,a⟩
lemma tslide(a b:Cover):(shiftV a).slide b=b+a:=by unfold shiftV March.slide; simp
lemma tturn(a:Cover):(shiftV a).turns A=translate a A:=by unfold March.turns shiftV; simp only [pull_one]; rfl
include t
lemma shift(a:Cover): Trust C (fun i=> P (i+a)):=fun i j u v=> add_right_cancel (t _ _ (Atlas.tell _ _ u _) v)
lemma matchShift(o:Cover): Cane.Q C K (fun i=> P (i+o)) (translate o A)=translate o (Cane.Q C K P A):=by
 rw [←tturn,← tturn]; apply matchTurn _ _ _ (shift C P t o) t ; intro a; rw [tslide,show Atlas.star (shiftV o)=1 from rfl, one_mul]
omit t
abbrev Channel(C):= Zone (Fringe C)→Mark (Bolt C)
abbrev click(o:Cover)(i:Zone R):=P (i.val+o)
def Documentary(c:Channel C):Prop:=∃ P:Record C, Trust C P∧ click C P 0=c
def display(c:Channel C)(A:Realms)(i:Axis): SU.E:= if h:Documentary C c then Cane.Q C K (Exists.choose h) A (0,i) else 1
include t
lemma scope_step(v:Cover)(i:Axis): Range 1 v (v+step i):=by intro j; by_cases h:j=i <;> simp [h]
lemma display0 (i:Axis)(c:Channel C)(h:c=click C P 0):display C K c A i=Cane.Q C K P A (0,i):=by
 let p:Documentary C c:=⟨P,t,h.symm⟩; unfold display; rw [dif_pos p]; refine inScope C p.choose P p.choose_spec.1 t 0 (fun i u=>?_) A A (fun _ _ _=>rfl) (0,i) (Range.refl _ _) (scope_step C P t 0 i)
 have k:= congrFun (p.choose_spec.2.trans h) (⟨i,u⟩:Zone R); simpa only [click,add_zero] using k
lemma display_cover (o:Cover)(i:Axis): display C K (click C P o) (translate o A) i = Cane.Q C K P A (o,i):=by
 rw [display0 _ _ _ (shift C P t o),matchShift C K P t]; simp only [translate,zero_add]; funext j; simp only [click,add_zero]
omit t
lemma runsM (c:Channel C)(i:Axis): Measurable (fun A=>display C K c A i):=by
 unfold display; by_cases h:Documentary C c; · simp_rw [dif_pos h]; exact (measurable_pi_apply _).comp (Cane.measurable C h.choose h.choose_spec.1 _)
 simp_rw [dif_neg h]; exact measurable_const
lemma scope0 (D:Realms)(c:Channel C)(h:Agrees (Scope R) A D)(i:Axis): display C K c A i=display C K c D i:=by
 unfold display; split_ifs with p; exact inScope C _ _ p.choose_spec.1 p.choose_spec.1 0 (fun _ _=>rfl) A D h (0,i) (Range.refl _ _) (scope_step C _ p.choose_spec.1 0 i); rfl
end Cane
end YM.CF.VolumeCape
