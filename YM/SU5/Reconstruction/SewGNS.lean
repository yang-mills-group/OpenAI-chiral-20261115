import VerifiedSatinSelectedSectors
import YM.SU5.Reconstruction.Sew
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
local notation "χ" => Selected.displacement Y H V G.history G.clipped d strict D c j C

local notation "L" => indoor Y H V G.history G.clipped j strict C χ
local notation "P" => procession Y H V G.history G.clipped j strict C χ
local notation "Ω" => doorstep Y H V G.history G.clipped j strict C χ
local notation "R₀" => arrive Y H V G.history G.clipped j strict C χ
local notation "L'" => fiberH Y H V G j strict C d D rχ
local notation "P'" => fiberOp Y H V G j strict C d D rχ
local notation "Ω'" => fiberVec Y H V G j strict C d D rχ
local notation "W" => engaged Y H V G j strict C d D rχ
local notation "eqT" => same_station Y H V G j strict C
/-- `same_station` is defeq. Give Lean an explicit equivalence to avoid defeq-search costs. -/
noncomputable def to_station : driveAlgebra Y H V G.history G.clipped j strict C ≃⋆ₐ[ℂ]
    stationC Y H V G j strict C := StarAlgEquiv.refl ℂ (stationC Y H V G j strict C)
local notation "u" => to_station Y H V G j strict C
lemma to_station_apply (b : 𝔅) : (u b).val=b.val := rfl

private theorem exists_matching :
    ∃ U : (indoor Y H V G.history G.clipped j strict C χ).space ≃ₗᵢ[ℂ] (L').space,
      ∀ b : driveAlgebra Y H V G.history G.clipped j strict C,
        U (R₀ b)= P' (u b) Ω' := by
  let f (b : T) := P' b Ω'
  have hf : DenseRange (fun b : 𝔅 => P' (u b) Ω') :=
    (fiber_sees Y H V G j strict C d D (resident Y H V G d strict D c)).mono
      (show Set.range f ⊆ Set.range (fun b : 𝔅 => f (u b)) from fun x h => by
        rcases h with ⟨b,rfl⟩
        exact ⟨(u).symm b,congrArg f ((u).apply_symm_apply _)⟩)
  apply Selected.gram_impl (A := L) (B := L')
    (arrive_dense Y H V G.history G.clipped j strict C χ) hf
  intro a b
  rw [arrive_pair, fiber_square]
  -- to_station and these products agree definitionally.
  -- normalize algebra instances
  exact Eq.symm (same_state Y H V G j strict C d D c (u (star a*b)))

noncomputable def matchGNS : (indoor Y H V G.history G.clipped j strict C χ).space ≃ₗᵢ[ℂ] (L').space :=
  (exists_matching Y H V G j strict C d D c).choose
local notation "U" => matchGNS Y H V G j strict C d D c

lemma matchGNS_stamp (b : driveAlgebra Y H V G.history G.clipped j strict C) :
    U (R₀ b) = P' (u b) Ω' := (exists_matching Y H V G j strict C d D c).choose_spec b

lemma matchGNS_vac : U Ω = Ω' := by
  have h := matchGNS_stamp Y H V G j strict C d D c 1
  rw [arrive_vac,map_one,map_one] at h
  exact h

lemma matchGNS_op (b : 𝔅) (x : indoor Y H V G.history G.clipped j strict C χ) :
    U (P b x) = P' (u b) (U x) := by
  have hf : Continuous (fun x : L => U (P b x)) := (U).continuous.comp (P b).continuous
  have hg : Continuous (fun x : L => P' (u b) (U x)) := (P' (u b)).continuous.comp (U).continuous
  refine congrFun ((arrive_dense Y H V G.history G.clipped j strict C χ).equalizer hf hg ?_) x
  funext a
  dsimp only [Function.comp_apply]
  rw [arrive_mul,matchGNS_stamp,matchGNS_stamp,map_mul,map_mul]
  rfl

lemma matchGNS_fields (s : ℕ) (x : Tower.Field Y H s j 0 strict) :
    U (Selected.bud Y H V s G.history G.clipped j strict C χ x) =
      (show (L').space from Acting.voice Y H V G j strict C W s x) := by
  obtain ⟨w,hw,a,rfl⟩ := artist_fits_slab Y H s j strict x
  rw [Selected.turns Y H V s G.history G.clipped j strict C χ a hw]
  exact (matchGNS_stamp Y H V G j strict C d D c _).trans
    ((Acting.notes Y H V G j strict C W s hw a).symm)

open MeshClock

lemma matchGNS_space (a : Trans j) (r : marks (timeMesh Λ)) (x : indoor Y H V G.history G.clipped j strict C χ) :
    U (((turnstile Y H V G.history G.clipped j strict C χ).crew a).play r x) =
      (show (L').space from Acting.lattice Y H V G j strict C W a r (U x)) :=
  matchGNS_op Y H V G j strict C d D c (shiftStamp Y H V G.history G.clipped j strict C a r) x

lemma matchGNS_time (t : ℝ≥0) (x : indoor Y H V G.history G.clipped j strict C χ) :
    U ((ride Y H V G.history G.clipped j strict C χ).E t x) =
      (show (L').space from Acting.clock Y H V G j strict C W t (U x)) :=
  matchGNS_op Y H V G j strict C d D c (Selected.coat Y H V G.history G.clipped j strict C t) x

end YM.CF.Buffered.Afterglow.Tower.Reconstruction
