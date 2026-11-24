import VerifiedSatinSelectedSectors
import YM.SU5.Reconstruction.TwoCells
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6500
set_option maxHeartbeats 440000
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
open Tapestry Tapestry.Altitude Tapestry.Exhibition
open Set
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H

open _root_.YM.CF.Pannier.Chancel
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ} {E : ℕ → Family (tent Y H) → ℂ}
  (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H) {L : Rack Λ l} {B : Clay Λ l}
  (D : Exhibition Y H i k I E L B)
variable (j d : Axis) (T : ∀ j : Axis, Arena Y H G.history.circuit j 0 false)
local notation "χ₀" => Dome (tent Y H)
local notation "Ĉ" => euclideanHalf Λ l (tent Y H) j
variable (c : (displayAlgebra Y H V G.history G.clipped d false (T d)) →⋆ₐ[ℂ] ℂ)
local notation "χ" => Selected.displacement Y H V G.history G.clipped d false (T d) c j (T j)
local notation "rχ" => resident Y H V G d false (T d) c
local notation "ρ" => indoor Y H V G.history G.clipped j false (T j) χ
local notation "P" => procession Y H V G.history G.clipped j false (T j) χ
local notation "Ω" => doorstep Y H V G.history G.clipped j false (T j) χ
local notation "Ψ" => matchGNS Y H V G j false (T j) d (T d) c
local notation "𝒱" s:max x:max => Selected.arriving Y H V s G.history G.clipped j false (T j) χ x
local notation "Θ" => onDrawing Y H V G D d T rχ
local notation "Mx" => evaluate Y H V G d T rχ
local notation "Ex" s:max => Selected.response Y H V s G.history G.clipped j false (T j) χ
variable (S : Finset Cover)
variable (s q t : ℕ) (o : Cover) (z : SU.Slot) (f : Selected.Marks (tent Y H) true)
local notation "C₀" s:max => insertAt Y H s
local notation "σ" n:max => silhouette Λ l n
variable (p a : Cover) (δ : ℝ)
local notation "U" => leftCell j K p S
local notation "U'" => rightCell K a S
local notation "f₊" => relocateWorld Y H true a f
local notation "fₘ" => Selected.mirrorInMarks Y H j true (relocateWorld Y H true p f)
local notation "u₊" => insertAt Y H s f₊
local notation "uₘ" => insertAt Y H s fₘ
local notation "u" => uₘ*u₊
local notation "μ" n:max => vistaFinish Y H (s+n) D
local notation "χₙ" n:max F:max => stream Y H G.refine s n F
open SelectionAnalysis OS.Semigroup
local notation "Γ" => saunters Y H V G.history G.clipped j false (T j) χ
local notation "S₀" => peninsula Y H V G.history G.clipped j false (T j) χ
local notation "W" F:max => land Y H V s G.history G.clipped j false (T j) χ F
local notation "inH" x:max => Selected.arriving Y H V s G.history G.clipped j false (T j) χ x

def DocketPrice : Prop :=
    Exceeds Y H V s G.history G.clipped j (T j) χ δ f z S o q t p a ∧
    (
    ----- one actual gauge–matter interaction test in the stated RemoteSplit sense
    Disjoint (silhouette Λ l s U) (silhouette Λ l s U') ∧
    (∀ i:Axis,∀ x∈ silhouette Λ l s U, ∀ y∈ silhouette Λ l s U', x i+δ≤ y i) ∧
    (¬ Selected.RemoteSplit j K p a S (booty o t q) (Window.family z) (Mx s)) ∧
    uₘ∈ circum Λ l K false (silhouette Λ l s U) (Set.Iic s) ∧
    u₊∈ circum Λ l K false (silhouette Λ l s U') (Set.Iic s) ∧
    u∈ circum Λ l K false (silhouette Λ l s (U∪ U')) (Set.Iic s) ∧
    1/32 ≤ ‖Θ (u)‖
    ) ∧
    (∃ x y : Tower.Field Y H s j 0 true,
      let g := Selected.admit Y H s j x; let m := Selected.admit Y H s j y
      x.val=(relocateWorld Y H true p f).val ∧ y.val=(f₊).val ∧
      Θ u = inner ℂ (inH g) (inH m) ∧
      Θ u = inner ℂ (W g) (W m) ∧
      (∀ᶠ v : RSpace in 𝓝 0, 1/33 ≤ ‖inner ℂ (W g) ((S₀).E (v j).toNNReal ((S₀).U (diameter v) (W m)))‖)
    ) ∧
    ∀ n:ℕ,
    (((μ n) u).val=(χₙ n (fₘ).val)*(χₙ n (f₊).val) ∧ Θ u=Mx (s+n) ((μ n) u).val) ∧
      InTest K true (volumeAround Λ l n U) false (χₙ n (fₘ).val) ∧
      InTest K true (volumeAround Λ l n U') false (χₙ n (f₊).val)
lemma acquires
    (h : ThresholdInteraction Y H V s G.history G.clipped j (T j) S χ f z o q t)
    (w : Exceeds Y H V s G.history G.clipped j (T j) χ δ f z S o q t p a) : DocketPrice Y H V G D j d T c S s q t o z f p a δ := by
  exact ⟨w,partner_cost Y H V G D j d T c S s q t o z f p a δ h w,
    interaction_vectors Y H V G D j d T c S s q t o z f p a δ w,
    fun n=> further_partners Y H V G D j d T c S s q t o z f p a δ h w n⟩
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.acquires
