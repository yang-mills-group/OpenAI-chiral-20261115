import ExactRunning.Mode.Pivot
/-!
# The two joint thermodynamic-limit Hessians: supply data

`z_data` and `h_data` give finite resonances against the scenes assembled
from the joint films. Import also `railings` from Rack (same backgrounds).
-/

set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

open Exterior Wilson Precision
open Tree

set_option synthInstance.maxSize 1024
namespace BlockTie
variable {G : Gauge} {E I : Pylon G} {m : Side} {X : BlockTie E I}

open Pairing

variable (X) {r : ℝ} (h : 0 < r)

def zScene : Scene (Du G) :=
  (↑((1:ℝ)/2):ℂ) • tableau X.glows.film - tableau X.innerGhost.film -
  tableau (outerGhost G).film

def hScene : Scene (Du G) :=
  (↑((1:ℝ)/2):ℂ) • tableau X.pulse.film - tableau X.blow.film

def zCook (r : ℝ) (m : Side) : Box G m → ℝ :=
  fun z => X.zFlex r (outer G m z) (inner G m z)

def hCook (r : ℝ) (m : Side) : Box G m → ℝ :=
  fun z => X.hCost r (X.fg_bg m z) (co_bg G m z)

include h
lemma glows_ready : X.glows.Steady (ridge r) :=
  fun _ t l => (X.joint_glow t (shade_of_safe _ h t l)).unit
lemma innerReady : X.innerGhost.Steady (ridge r) :=
  fun _ t l => (X.innerGhost_glow t (shade_of_safe _ h t l)).unit
lemma outerReady (G : Gauge) : (outerGhost G).Steady (ridge r) :=
  fun _ t l => (outerGhost_glow G t (shade_of_safe _ h t l)).unit

lemma z_safe (m : Side) : X.ZSafe m r := by
  refine ⟨?_,h⟩
  have e := (X.glows_ready h).unit (X.hold_cut r m)
  simpa only [X.fg_bg_zero,co_bg_zero] using e

lemma z_scenes : (ridge r).Medium X.zScene :=
   (((X.glows_ready h).medium.smul _).sub (X.innerReady h).medium).sub (outerReady h G).medium

lemma z_data (m : Side) :
    Resonance (ridge r) ((ridge r).play m X.zScene) (X.zCook r m) := by
  have g := (X.glows_ready h).echo (X.hold_cut r m)
  have i := (X.innerReady h).echo (X.rolled_cut r m 0)
  have j := (outerReady h G).echo (m:=m) (.refl _)
  rw [zScene,Latitude.play_sub,Latitude.play_sub,Latitude.play_smul]
  exact ((g.weight (1/2)).sub i).sub j
omit h

lemma pulse_ready (r : ℝ) : X.pulse.Steady (ridge r) := fun _ t _ => X.freeAll _ t
lemma blow_ready (r : ℝ) : X.blow.Steady (ridge r) := fun _ t _ => (X.blow_glow t).unit

lemma h_safe (m : Side) (r : ℝ) : X.HSafe m r := by
  have e := (X.pulse_ready r).unit (X.barrel_cut r m)
  have f := (X.blow_ready r).unit (X.rolled_cut r m 0)
  simp only [X.fg_bg_zero,co_bg_zero] at e f
  exact ⟨e,f⟩

lemma h_scenes (r : ℝ) : (ridge r).Medium X.hScene :=
   ((X.pulse_ready r).medium.smul _).sub (X.blow_ready r).medium

lemma h_data (r : ℝ) (m : Side) :
    Resonance (ridge r) ((ridge r).play m X.hScene) (X.hCook r m) := by
  rw [hScene,Latitude.play_sub,Latitude.play_smul]
  exact (((X.pulse_ready r).echo (X.barrel_cut r m)).weight (1/2)).sub
    ((X.blow_ready r).echo (X.rolled_cut r m 0))

end BlockTie
end ExactRunning
