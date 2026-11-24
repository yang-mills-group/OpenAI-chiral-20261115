import SatinFixedContrastNovember4

import SatinThinReflector

/-! # II. All calendars: at ≥intrinsic width. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup.Balloon

open MacroGrid

private lemma beam_heats {X : Hilbert} {j : Axis} (p : OS.Semigroup X j)
    (v : X) (a b : ℝ) (f : 0 ≤ a) (w : a ≤ b) :
    p.E ((b-a).toNNReal) (p.E a.toNNReal v)= p.E b.toNNReal v := by
  have he : b.toNNReal=(b-a).toNNReal+a.toNNReal := by ext; simp [f,f.trans w, sub_nonneg.mpr w]
  rw [he,p.time]; rfl

section
variable (P : Spine) (j:Axis) (x : P.Spectrum0 3)
local notation "ξ" => P.advocate 3 x j
local notation "M" => timeMesh P.par
local notation "H" => P.ColorHil j ξ
local notation "ω" => P.colorZero j ξ
local notation "S" => P.physicalEnergy j ξ
local notation "E" => (S).E
local notation "Γ" => P.truck j ξ
local notation "G" => P.ManyF j ξ
local notation "Ω" => P.heaven j ξ
local notation "R" => P.seasons j ξ
local notation "V₀" => P.cartage j ξ
local notation "π'" => P.wealth j ξ
local notation "λ'" => (P.enter j ξ)


variable (A:P.Apron)(t:ℕ)
local notation "w" => A.realWidth P j
local notation "u" => P.meshPose t
local notation "T" => P.vtile t
abbrev beamRaw(e:ℝ):= E ((e-(w)).toNNReal) (A.engine P j ξ (P.colorZero j ξ))
abbrev beam(e:ℝ):= (R).E ((e-(w)).toNNReal) (flashY x A j)
abbrev beamGridRay (p:Cover) : P.ColorHil j ξ:= Γ (T p) (P.beamRaw j x A (u p j))
lemma beam_grid_pose_view(k:Cover)(b:(w) ≤ u k j)(p:A.s≤t):
    ∃ h:P.birthF j t (P.issuing t A k), P.viewF j ξ t h=P.beamGridRay j x A t k:= by
  let i:Fin 1:=0; let L:=[i]; let Q:= fun _:Fin 1=>A; let r:=fun _:Fin 1=>k
  have he : ∀ i∈L,(Q i).s≤t := fun i _=>p
  have ht:P.onBoard j t Q r L 0:= by
    refine ⟨(bell_le M t _ _).1 ?_,trivial⟩
    rw [P.begins j Q r t i p]; change bell M t 0 ≤ u k j - (w)
    rw [show bell M t 0=0 by simp [bell]]; linarith
  have hx: P.issuing t A k=P.shifts j (-(0:ℤ)) (P.fullScroll t Q r L):= by
    rw [neg_zero,P.shifts_zero]; change _=_*1; rw [mul_one]; rfl
  obtain ⟨f,g⟩:= P.vread j ξ t _ _ L 0 ht he
  have u':P.birthF j t (P.issuing t A k):=by rw [hx]; exact f
  refine ⟨u', (P.identical_F j ξ t _ _ hx).trans (g.trans ((P.transporting j ξ Q r t L 0 ht he).trans ?_))⟩
  let C:= P.charter j ξ (T k) (A.engine P j ξ)
  rw [show bell M t 0=0 by simp [bell]]
  change E (((u k j-(w))-0).toNNReal) (C ω)= _
  rw [sub_zero]; unfold beamGridRay beamRaw; unfold C; rw [P.raw_aperture,P.sixWard_truck_heat]
lemma beam_twice {z r:ℝ}(v:A.realWidth P j ≤ z)(k:z ≤ r) : P.beam j x A r =(R).E ((r-z).toNNReal) (P.beam j x A z):=by
 unfold beam; exact (beam_heats R (flashY x A j) (z-(w)) (r-(w)) (sub_nonneg.mpr v) (sub_le_sub_right k _)).symm.trans ( (by rw [sub_sub_sub_cancel_right])) -- os case
lemma raw_twice {z r:ℝ}(v:A.realWidth P j ≤ z)(k:z ≤ r) : P.beamRaw j x A r = E ((r-z).toNNReal) (P.beamRaw j x A z):=by
 unfold beamRaw; exact (beam_heats S _ (z-(w)) (r-(w)) (sub_nonneg.mpr v) (sub_le_sub_right k _)).symm.trans ((by rw [sub_sub_sub_cancel_right]))
lemma beam_bank (z:ℝ) : P.beam j x A z= (π') (P.beamRaw j x A z):= Eq.symm (P.bankHeat ..)
-- a priori
lemma beam_raw_le (z:ℝ) : ‖P.beam j x A z‖≤ ‖P.beamRaw j x A z‖:=by rw [P.beam_bank]; exact P.bank_cost ..
lemma beam_right_le {z r:ℝ}(v:A.realWidth P j ≤ z)(k:z ≤ r) : ‖P.beamRaw j x A r‖≤ ‖P.beamRaw j x A z‖:= by
 rw [P.raw_twice j x A v k]; exact le_trans (ContinuousLinearMap.le_opNorm ..) (mul_le_of_le_one_left (norm_nonneg _) ((S).shrinks _))
lemma beam_tide_norm (p:Cover) : ‖P.beamGridRay j x A t p‖= ‖P.beamRaw j x A ((u p) j)‖:= P.truck_norm ..
end

section birth
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)(t:ℕ)
lemma birthAddJ {a b:P.Test}(f:P.birthF j t a)(g:P.birthF j t b) : P.birthF j t (a+b):= by
 obtain ⟨f,rfl⟩:=f; obtain ⟨g,rfl⟩:=g
 exact ⟨⟨f.val+g.val,Subalgebra.add_mem (enclave P.calibration) f.property g.property⟩,rfl⟩
lemma birthScaleJ (z:ℂ) {a:P.Test}(f:P.birthF j t a): P.birthF j t (z • a):= by
 obtain ⟨f,rfl⟩:=f; exact ⟨⟨z • f.val,Subalgebra.smul_mem (enclave P.calibration) f.property z⟩,rfl⟩
lemma viewJ_plus {a b:P.Test}(f:P.birthF j t a)(g:P.birthF j t b):
    P.viewF j x t (P.birthAddJ j t f g)=P.viewF j x t f + P.viewF j x t g:= by
 let p:=P.birthAddJ j t f g
 have hg:=P.sixWard_view_sub j x t p g ((show P.birthF j t ((a+b)-b) by rwa [add_sub_cancel_right]))
 have he:P.viewF j x t f=P.viewF j x t p-P.viewF j x t g:= (P.identical_F j x t f _ (add_sub_cancel_right ..).symm).trans hg
 exact (eq_sub_iff_add_eq.mp he).symm
lemma viewJ_scale (z:ℂ) {a:P.Test}(f:P.birthF j t a):
    P.viewF j x t (P.birthScaleJ j t z f)=z • P.viewF j x t f := by
 let p:= P.birthScaleJ j t z f
 have hh (e:P.Test)(g:P.birthF j t e): inner ℂ (P.viewF j x t g) (P.viewF j x t p)=z*inner ℂ (P.viewF j x t g) (P.viewF j x t f):= ((P.released_gram j x t g p).trans (congrArg (P.singleState j t x) (mul_smul_comm ..))).trans ((map_smul (P.singleState j t x) z _).trans (congrArg (fun x:ℂ=>z*x) (P.released_gram j x t g f).symm))
 apply right_weight (P.ColorHil j x) _ _ (0:P.ColorHil j x); intro i v; simp only [List.mem_cons,List.not_mem_nil,or_false] at v; rcases v with v|v <;> subst i <;> exact hh _ _
lemma birthSumJ{ι:Type}[DecidableEq ι] (S:Finset ι)(f:ι→P.Test) (X:ι → P.ColorHil j x)
    (p:∀ i∈ S,∃ h:P.birthF j t (f i),P.viewF j x t h=X i):∃ h:P.birthF j t (∑ i∈ S,f i),P.viewF j x t h=∑ i∈ S,X i:= by
 induction S using Finset.induction_on with
 | empty=>
   rw [sum_empty,sum_empty]
   let g:= P.faceUnit j t
   have hx:= P.birthScaleJ j t 0 g
   have h:P.birthF j t 0:= by simpa only [zero_smul] using hx
   exact ⟨h, (P.identical_F j x t _ hx (zero_smul ..).symm).trans ((P.viewJ_scale j x t 0 g).trans (zero_smul ..))⟩
 | @insert a L h ih=>
   obtain ⟨i,x₀⟩:= ih (fun i z=> p i (mem_insert_of_mem z))
   obtain ⟨g,x'⟩:=p a (mem_insert_self ..)
   rw [sum_insert h,sum_insert h]
   exact ⟨P.birthAddJ j t g i,(P.viewJ_plus j x t g i).trans (congrArg₂ (· + ·) x' x₀)⟩
end birth
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.beam_grid_pose_view
