import VerifiedSatinSelectedSectors
/-!
Compare the two presentations on the *same* Glasshouse character and same axis.
Do not identify different axes' full Hilbert spaces. Scope: `the construction notes`.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6500
set_option maxHeartbeats 480000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Selected PhaseChoice PhaseChoice.SameCharacter PhaseChoice.Theory

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ} {E : ℕ → Family (tent Y H) → ℂ}
  (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
variable (j : Axis) (strict : Bool) (C : Arena Y H G.history.circuit j 0 strict)
variable (d : Axis) (D : Arena Y H G.history.circuit d 0 strict)
local notation "V₀" a:max b:max => groundRoom Y H V G.history a strict b
local notation "R" a:max b:max => displayAlgebra Y H V G.history G.clipped a strict b
local notation "𝔅" => driveAlgebra Y H V G.history G.clipped j strict C
local notation "T" => stationC Y H V G j strict C
variable (c : (displayAlgebra Y H V G.history G.clipped d strict D) →⋆ₐ[ℂ] ℂ)
local notation "rχ" => resident Y H V G d strict D c
local notation "χ" => displacement Y H V G.history G.clipped d strict D c j C

lemma same_station : stationC Y H V G j strict C = driveAlgebra Y H V G.history G.clipped j strict C := rfl

local notation "B₀" a:max b:max => Selected.adjust Y H V G.history G.clipped a strict b
local notation "Ψ" a:max b:max => adjustment Y H V G.history G.clipped a strict b
local notation "e" => earlyMap Y H V G j strict C d D

lemma same_aurora_map :
    Selected.adjust Y H V G.history G.clipped j strict C d D = connector Y H V G j strict C d D := by
  apply DFunLike.coe_injective
  apply (compressed_dense Y H V G.history G.clipped j strict C).equalizer ((B₀ j C) d D).continuous
    (connector Y H V G j strict C d D).continuous
  funext x
  dsimp only [Function.comp_apply]
  exact (adjusts Y H V G.history G.clipped j strict C d D x).trans
    (connector_disc Y H V G j strict C d D x).symm

lemma same_early_map (x : displayAlgebra Y H V G.history G.clipped j strict C) :
    adjustment Y H V G.history G.clipped j strict C d D x =
      (show R d D from (e).symm x) := by
  -- calculate on underlying operators, not in casts of StarSubalgebra
  apply Subtype.ext
  -- explicitly switch order of .conj
  change (((Ψ j C) d D x).val : _ →L[ℂ] _) = ((e).symm (show catalog Y H V G j strict C from x)).val
  have h := matches_map Y H V G j strict C d D ((e).symm x)
  have a : (e ((e).symm x)).val = x.val := congrArg (fun i : catalog Y H V G j strict C => i.val)
    ((e).apply_symm_apply x)
  have l : x.val = ((B₀ d D) j C).conjStarAlgEquiv ((e).symm x).val := by
    rw [same_aurora_map Y H V G d strict D j C]
    exact a.symm.trans h
  calc
    _ = ((B₀ j C) d D).conjStarAlgEquiv x.val := adjust_action Y H V G.history G.clipped j strict C d D x
    _ = ((B₀ d D) j C).conjStarAlgEquiv.symm x.val := by
      rw [LinearIsometryEquiv.symm_conjStarAlgEquiv, adjust_symm]
    _ = _ := ((B₀ d D) j C).conjStarAlgEquiv.symm_apply_eq.mpr l

lemma same_compression_mark (b : stationC Y H V G j strict C) :
    (PhaseChoice.bank Y H V G j strict C d D).mark b =
      (show catalog Y H V G d strict D from ((Ψ j C) d D (reduceToDisplay Y H V G.history G.clipped j strict C b))) := by
  rw [same_early_map]
  rfl

/-- This goes beyond `SameCharacter.sameReading`: full states of the two workers coincide
on the C* algebra of the unselected OS slabs and shifts on each assumed axis. -/
theorem same_state (b : stationC Y H V G j strict C) :
    fiberState Y H V G j strict C d D (resident Y H V G d strict D c) b =
      atCharacter Y H V G.history G.clipped j strict C
        (displacement Y H V G.history G.clipped d strict D c j C) b := by
  simp only [fiber_look,same_compression_mark]
  rfl

end YM.CF.Buffered.Afterglow.Tower.Reconstruction
