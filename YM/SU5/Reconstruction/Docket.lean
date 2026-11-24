import VerifiedSatinSelectedSectors
import YM.SU5.Reconstruction.LimitingTests
import YM.SU5.Reconstruction.TwoCells
import YM.SU5.Reconstruction.StampActs
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

/-!
# CP-A Docket receipts. See `ElectionEuclidean` for actual joint witness. The record in
that theorem deliberately keeps previous budgets and identifications. Do not erase claims
requiring this very history/reading. NO claim of merging the *Lorentz frames* or full
reconstruction. This specializes merited estimates for the same physical domain, not all
intermediate comparison statements (e.g. `census_converges` remains separately on a Panel).
-/
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ} {E : ℕ → Family (tent Y H) → ℂ}
  (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H) {L : Rack Λ l} {B : Clay Λ l}
  {τh : ℕ→ℕ→Tariff} {τl : ℕ→Tariff} (D : Fashion Y H i k I E L B τh τl)
variable (T : ∀ j : Axis, Arena Y H G.history.circuit j 0 false)
local notation "ν" => Dome (tent Y H)
local notation "e" => D.toExhibition
local notation "cY" => Y
local notation "hY" => H
local notation "r₀" => i ∘ G.rows
local notation "v₀" => k ∘ G.columns
local notation "M" r:max => Y.uv (v₀ r)
local notation "P" r:max => (Y.voyage (r₀ r))
local notation "Ξ" r:max => partitionZ (((P r).X (M r)).gram (M r)) Λ.U ((P r).CapeT (M r))
local notation "Y₀" r:max => Journey.side Y (r₀ r) (M r)
local notation "μ" r:max => Wilson.prior SU.group (More (Y₀ r))
local notation "f₀" r:max x:max => numeratorTop Y H (r₀ r) (v₀ r) x
-- independent of component
structure CutInterpret : Prop where
  converge (x : Cloud (Dome (tent Y H))) (p : x∈ FiniteGaugeDataPoly K) :
    Tendsto (fun n:ℕ=> taking Y H (r₀ n) (v₀ n) x) atTop (𝓝 (vistaTake Y H e x))
  support (s : ℕ) (U : Set RSpace) (wide : Bool) (x : Cloud ν)
    (p : x∈jetty Λ l K wide (handstamp U) (Set.Iic s)) (d : Bornology.IsBounded U) :
    ∃ S : BillOfWork, x∈fountainHeads K S s ∧ (∀ i, silhouette Λ l i (S i) ⊆ U) ∧
    ∀ᶠ r : ℕ in atTop, Ferry Y s (r₀ r) (v₀ r) ∧ Tapestry.Pay Y s (r₀ r) (v₀ r) ∧
      (∀ n : ℕ, s≤n → let B:=frameBudget S Λ l n;
        FullDistances B (side Y (r₀ r) n) ∧ silhouette Λ l n B ⊆ U ∧
        (n ≤ M r → AtSupport false (Satin.region B (Journey.side Y (r₀ r) n)) (attire (breathing Y H n (r₀ r) (v₀ r) x)))) ∧
      AtSupport false (Satin.region (frameBudget S Λ l (M r)) (Y₀ r)) (toMark (observableTop Y H (r₀ r) (v₀ r) x)) ∧
      (x∈localEuclidean Λ l K wide U → covariant (toMark (observableTop Y H (r₀ r) (v₀ r) x))) ∧
      (∀ A : Pane (Y₀ r), ∃ z : FC (Single (Y₀ r)), Reed.Plain z ∧
        observableTop Y H (r₀ r) (v₀ r) x A=(Reed.think (Tset (Y₀ r))).eval z) ∧
      Ξ r≠0 ∧ Ξ r = (∫ v,(f₀ r 1) v ∂ (μ r)) ∧ Integrable (f₀ r x) (μ r) ∧
      taking Y H (r₀ r) (v₀ r) x=(∫ v,(f₀ r x) v ∂ (μ r)) / (Ξ r)
  native_separated (A B : Set RSpace) (p : Disjoint A B) (a : Bornology.IsBounded A) (b : Bornology.IsBounded B) :
    ∀ᶠ i : ℕ in atTop, ∀ (n k : ℕ), Tapestry.Pay Y n i k → ∀ (x y : Cloud (Dome (tent Y H))),
      x∈ jetty Λ l (tent Y H) true (handstamp A) (Set.Iic n) → y∈ jetty Λ l (tent Y H) true (handstamp B) (Set.Iic n) →
        breathing Y H n i k (x*y)= breathing Y H n i k x*breathing Y H n i k y

include V in
lemma interpret_cuts : CutInterpret Y H G D := by
  refine ⟨fun _=>convergence Y H G D, fun _ _ _ _ p d=> bare_path Y H V G p d, fun A B p a b=>?_⟩
  exact (independent_insertion Y H A B p a b).mono fun n p i k t=> p i k t true true

open _root_.YM.CF.Pannier.Chancel
open SelectionAnalysis
variable (j : Axis)
variable (c : displayAlgebra Y H V G.history G.clipped 0 false (T 0) →⋆ₐ[ℂ] ℂ)
local notation "χ" j:max => Selected.displacement Y H V G.history G.clipped 0 false (T 0) c j (T j)
local notation "rχ" => resident Y H V G 0 false (T 0) c
local notation "Θ" => onDrawing Y H V G e 0 T rχ
local notation "Eχ" => evaluate Y H V G 0 T rχ
local notation "L₀" j:max => indoor Y H V G.history G.clipped j false (T j) (χ j)
local notation "X" j:max => engaged Y H V G j false (T j) 0 (T 0) rχ
local notation "ψ" j:max => matchGNS Y H V G j false (T j) 0 (T 0) c
local notation "Ĉ" j:max => euclideanHalf Λ l (tent Y H) j
local notation "Ψ" j:max => scan Y H V G e j 0 T c
structure Dictionary : Prop where
  vacuum : ExtremeReceipt Y H V G 0 T rχ
  reads (j:Axis) : DenseRange (scan Y H V G e j 0 T c)
  reflection (j:Axis)(x y:Ĉ j) : inner ℂ ((Ψ j) x) ((Ψ j) y)= Θ (Sunlight.oppose Λ j (PhaseChoice.atZero Λ) K x.val*y.val)
  workerVacuum (j:Axis): (ψ j) (doorstep Y H V G.history G.clipped j false (T j) (χ j))= (show (fiberH Y H V G j false (T j) 0 (T 0) rχ).space from (X j).ground)
  same_flow (j:Axis)(x:L₀ j)(t:ℝ) :
    (ψ j) ((ride Y H V G.history G.clipped j false (T j) (χ j)).edge t x) =
    (show (fiberH Y H V G j false (T j) 0 (T 0) rχ).space from Acting.unitaryTime Y H V G j false (T j) (X j) t ((ψ j) x))
lemma interpreted (p : ∀ j:Axis, Victory Y H V G.history G.clipped false j (T j) (χ j)) : Dictionary Y H V G D T c := by
  exact ⟨extreme_receipt Y H V G 0 T c p, fun j=> scan_dense Y H V G e j 0 T c, fun j=>scan_inner Y H V G e j 0 T c, fun j=>matchGNS_vac Y H V G j false (T j) 0 (T 0) c, fun j x t=> matchGNS_edge ..⟩

end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.interpret_cuts
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.interpreted
