import YM.CF.DPress.FD.Cycle.Chime
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD.Cycle
open List Filter Set
open scoped Topology BigOperators ENNReal Classical
open Function
variable {I J:Type*}[Fintype I][DecidableEq I][Fintype J][DecidableEq J] (S:Equiv.Perm I) (W:Equiv.Perm J)(e:I≃J)(z:Semiconj e S W)
lemma twice (p:Coil I): (p.map e).map e.symm=p:=by
 induction p using Quotient.inductionOn' with| _ x=>simp only [_root_.Cycle.mk''_eq_coe, _root_.Cycle.map_coe,List.map_map, Equiv.symm_comp_self,List.map_id]
include z
lemma cone_h : (loops S).image (fun x:Coil I=> x.map e)= loops W:=by
 ext i; rw [Finset.mem_image]; constructor; · rintro ⟨u,t,rfl⟩; obtain ⟨i,t,rfl⟩:= Finset.mem_image.mp t; rw [← beamτ S W e z]; exact lands ..
 intro h; obtain ⟨j,h,rfl⟩:=Finset.mem_image.mp h; refine ⟨visit S (e.symm j),lands ..,?_⟩; rw [← beamτ S W e z,e.apply_symm_apply]
lemma symmetry (x:Skin J): mass S (x ∘ e)=mass W x:=by
 unfold mass ΔP; rw [←cone_h S W e z,Finset.prod_image (s:=loops S) (f:=fun i:Coil J=>coilW i x)]; swap; · intro i p j t w; exact (twice e i).symm.trans ((congrArg (_root_.Cycle.map e.symm) w).trans (twice e j))
 refine Finset.prod_congr rfl ?_; intro i p; obtain ⟨i,p,rfl⟩:=Finset.mem_image.mp p; rw [←beamτ S W e z,←coilW_C x _ (vote W _).symm,←coilW_C (x ∘ e) _ (vote S i).symm,lookτ S W e z]; congr 1; exact (List.map_map ..).symm
end YM.CF.DPress.FD.Cycle
