import ReviewGradedBoundsSatinGraded
import ReviewGradedBoundsSatinCharts

/-! Refinement and real-position chart laws on one selected Satin course.
The chart comparison retains its strict ordering or overlap hypotheses. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 470000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Tapestry Tapestry.Altitude PhaseChoice
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
open Tower.Selected Set MeshClock Tapestry.Exhibition
open SelectionAnalysis Vacancy.Average
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  {L:Rack Λ l}{B:Clay Λ l}{T:ℕ→ℕ→Tariff}{t:ℕ→Tariff}(D:Fashion Y H i k I E L B T t)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
local notation "Dₚ" => D.toExhibition
local notation "V" => D.univ_
local notation "Q" => G.history
local notation "Qt" => G.clipped
local notation "χ" => Dome (tent Y H)
local notation "O" => Altitude.Cloud (Dome (tent Y H))
local notation "P₀" s:max => vistaFinish Y H s (Dₚ)

section here
variable (C : ∀ i: Axis, Tower.Arena Y H G.history.circuit i 0 false)
variable (c: (displayAlgebra Y H D.univ_ G.history G.clipped 0 false (C 0)) →⋆ₐ[ℂ] ℂ)

open One SelectionAnalysis.Regularizing

def WorldChartLaws : Prop :=
  ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (U : σ → Set RSpace) (fields : ∀ i, Pol Y H (U i))
    (P : List σ) (p : P.Nodup) (v : σ → RSpace),
    (∀ {S : Type} (l' : Filter S) (n : S → FrameRef) (y : S → σ → placement Λ),
      Tendsto n l' zoom → Tendsto (fun i k => physPos Λ (y i k)) l' (𝓝 v) → Formed U P v →
      Tendsto (fun i => Average.center (fun z : Dress (timeMesh Λ) σ (n i) =>
        poseValue Y H D G C c U fields P (plotted (timeMesh Λ) (n i) (y i) z)))
        l' (𝓝 (responseAtlas Y H D G C c U fields P v))) ∧
    ∀ {s t : ℕ} {a b : Axis} (F : Board Y H D s a U fields) (J : Board Y H D t b U fields)
      (Z : List σ), P.Perm Z → OfferedOn Y H D P F v → OfferedOn Y H D Z J v →
      crossBill Y H D G C c F P v = crossBill Y H D G C c J Z v

theorem worldCharts_on : WorldChartLaws Y H D G C c := by
  intro σ _ _ U fields P hp v
  constructor
  · intro S filter n y zooms positions aperture
    exact at_world Y H D G C c U fields P hp v filter n zooms y positions aperture
  · intro s t a b F J Z perm admitF admitJ
    exact any_world Y H D G C c F P v hp admitF perm J admitJ

def GradedRefinementLaws : Prop :=
  ∃ (subseq : ℕ → ℕ) (M : One.Collection Λ l),
    One.Twined Y H (i := i) (k := k) (n := G.rows) (m := G.columns) M subseq ∧
    (∀ (s t : ℕ) (b : Bool) (a : Axis) (z : ℤ) (f : Family (tent Y H)),
      f ∈ One.gradeFlank (tent Y H) b a z →
      One.beamB Y H M b s t f ∈ One.gradeFlank (tent Y H) b a ((Λ.R.L.val : ℤ)^t*z)) ∧
    (∀ (s t : ℕ) (b e : Bool) (S T : Finset Cover) (f g : Family (tent Y H)),
      InTest (tent Y H) true S b f → InTest (tent Y H) true T e g → Detached Λ l S T →
      One.beamB Y H M (b.xor e) s t (f*g) = One.beamB Y H M b s t f * One.beamB Y H M e s t g) ∧
    ∀ (s : ℕ) (b : Bool) (S : Finset Cover) (f g : Family (tent Y H)) (P : Cover → SU.E),
      InTest (tent Y H) true S b f → InTest (tent Y H) true S b g → Circular S (parentGauge Λ P) f g →
      Circular (wingspan Λ l S) P (One.stripe Y H M b s f) (One.stripe Y H M b s g)

include D in
theorem gradedRefinement_on : GradedRefinementLaws (i := i) (k := k) Y H G := by
  obtain ⟨q,hq,M,hm⟩ := One.attains Y H D.univ_ G.history
  let grant : One.Twined Y H (i := i) (k := k) (n := G.rows) (m := G.columns) M q := ⟨hq,hm⟩
  refine ⟨q,M,grant,?_,?_,?_⟩
  · intro s t b a z f hf
    exact One.beamWing Y H D.univ_ s G.history grant hf t
  · intro s t b e S T f g hf hg sep
    exact One.beamMult Y H D.univ_ s G.history grant hf hg sep t
  · intro s b S f g P hf hg relation
    exact One.stripeH Y H D.univ_ s G.history grant b P hf hg relation

#print axioms worldCharts_on
#print axioms gradedRefinement_on
end here
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
