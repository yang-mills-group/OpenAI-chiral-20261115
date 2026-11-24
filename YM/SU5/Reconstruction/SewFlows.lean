import VerifiedSatinSelectedSectors
import YM.SU5.Reconstruction.SewGNS
import YM.SU5.Reconstruction.AlongHeat
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
local notation "U" => matchGNS Y H V G j strict C d D c

open YM.SelectionAnalysis OS.Semigroup MeshClock

/-- For heat API; transverse directions dummy in this auxiliary record. -/
noncomputable abbrev pureHeat (X : Acting Y H V G j strict C) : OS.Semigroup X.space j where
  E := Acting.clock Y H V G j strict C X
  eZero := Acting.clock_zero ..
  time t v := Acting.clock_sum ..
  shrinks t := Acting.clock_law ..
  sym t := Acting.clock_symm ..
  «U» _ := ContinuousLinearMap.id ℂ _
  uZero := rfl
  space _ _ := rfl
  unitary _ _ := rfl
  independent _ _ := rfl
  continuousE := Acting.price_every Y H V G j strict C X
  continuousU _ := continuous_const

local notation "S" => ride Y H V G.history G.clipped j strict C χ

lemma matchGNS_interior (x : indoor Y H V G.history G.clipped j strict C χ) {z : ℂ} (hz : 0 < z.im) :
    U ((S).F (-Complex.I*z) x) =
    (show (L').space from Acting.halfSpaceFunction Y H V G j strict C W z (U x)) :=
  OS.Semigroup.intertwines_F S (pureHeat Y H V G j strict C W)
    (U).toLinearIsometry.toContinuousLinearMap (matchGNS_time Y H V G j strict C d D c) x (Selected.air_positive hz)

lemma matchGNS_edge (x : indoor Y H V G.history G.clipped j strict C χ) (t : ℝ) :
    U ((S).edge t x) =
    (show (L').space from Acting.unitaryTime Y H V G j strict C W t (U x)) :=
  OS.Semigroup.intertwines_edge S (pureHeat Y H V G j strict C W)
    (U).toLinearIsometry.toContinuousLinearMap (matchGNS_time Y H V G j strict C d D c) x t

section rank
lemma of_victory (p : Victory Y H V G.history G.clipped strict j C χ) :
    (PhaseChoice.bank Y H V G j strict C d D).FixedPhase rχ := by
  change ∀ w : L', (∀ u ∈ approach Y H V G j strict C, P' u w=w) → ∃ c₀:ℂ,w=c₀ • Ω'
  intro w hw
  obtain ⟨x,rfl⟩ := (U).surjective w
  have time_fixed (t : ℝ≥0) : (S).E t x=x := by
    apply (U).injective
    exact (matchGNS_time Y H V G j strict C d D c _ _).trans
      (hw (heatOp Y H V G j strict C t) (Or.inl ⟨_,rfl⟩))
  have space_fixed (a : Trans j) (r : marks (timeMesh Λ)) : ((turnstile Y H V G.history G.clipped j strict C χ).crew a).play r x=x := by
    apply (U).injective
    exact (matchGNS_space Y H V G j strict C d D c _ _ _).trans
      (hw (shiftOp Y H V G j strict C a r) (Or.inr ⟨(a,r),rfl⟩))
  obtain ⟨z,hz⟩ := one_real Y H V G.history G.clipped j strict C χ p (x:=x) ⟨(lamp_fixed S x).mpr time_fixed,space_fixed⟩
  exact ⟨z,(congrArg U hz.symm).trans ((map_smul U _ _).trans (congrArg (z • ·) (matchGNS_vac Y H V G j strict C d D c)))⟩

variable (T : ∀ j:Axis, Arena Y H G.history.circuit j 0 false)
variable (c' : (displayAlgebra Y H V G.history G.clipped d false (T d)) →⋆ₐ[ℂ] ℂ)
local notation "x" => resident Y H V G d false (T d) c'
lemma extreme_receipt (p : ∀ j : Axis, Victory Y H V G.history G.clipped false j (T j)
    (Selected.displacement Y H V G.history G.clipped d false (T d) c' j (T j))) :
    ExtremeReceipt Y H V G d T x := by
  have h (j) := of_victory Y H V G j false (T j) d (T d) c' (p j)
  refine ⟨h,fun a w hs ht => Transaction.show_fixed _ _ (h a) _ ?_,fun a => Transaction.show_norm _ _,
    fun a _ _ c d h₁ h₂ p q t => Transaction.cannot_split _ x (h a) p q c d h₁ h₂ t,
    fun a y t => Transaction.show_queue (PhaseChoice.bank Y H V G a false (T a) d (T d)) x y t⟩
  intro b hb
  rcases hb with ⟨s,rfl⟩|⟨⟨u,v⟩,rfl⟩
  · exact ht _
  exact hs ..
end rank

end YM.CF.Buffered.Afterglow.Tower.Reconstruction
