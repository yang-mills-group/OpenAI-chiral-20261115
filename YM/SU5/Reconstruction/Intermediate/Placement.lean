import YM.SU5.Reconstruction.PolarArchives.Morning
import YM.SU5.Reconstruction.Brazier.Gaps
/-! $Seam region physically meaning: choose REAL permission; validate even both footprints & no wrapping BOTH along cuts alltogether. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Tilted
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G
open WindRose
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (j:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped j false (C j) →⋆ₐ[ℂ] ℂ)
local notation "Mirror" i:max=> flipMark i (tent Y H)
open Stormwatch ConePrice Germ SelectionAnalysis CrossedFrame
open YM.ConePrice.Storm
local notation "µ" => Domain Y H G false Set.univ
local notation "Gt" => marks (timeMesh Λ)
open Fock Lat Laurent Wilson Cube Finset Branch Scree RG Spire Vale Pastry Peaks Dial Phase Lifted Skye Tapestry.Exhibition Tapestry.Altitude Tenant Rush Tulip
open PolarArchives Brazier
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker -- may clobber K.Gauge representation norms
attribute [local instance] opCStarAlgebra
variable (m t s:ℕ)
local notation "𝗠" i:max j:max=> Journey.side Y i j
local notation "🎨" i:max=> (Y.voyage m).CapeT i
variable (P:Ramp) (r:ℝ≥0)
local notation "Θ" f:max=> Tilted.Ramp.bill P f
variable (U V₀ : Finset Cover)
abbrev period : ℝ := gaugeMesh Λ s * ((More (𝗠 m s)).val:ℝ)
-- any test here physically clearly positive, fits between periodic seams. Implement on both +/- footprints.
noncomputable def Fits (W:Set RSpace)(A:Finset Cover) : Prop:= PhaseChoice.SupportedPhysically Λ l s A W ∧ ∀ x∈bufferedHull Λ l s A,|landN P x|+(r:ℝ) < period Y m s/2
structure CanInspect (f : Mark (Journey.side Y m s)) : Prop where
  siteF : AtSupport false (Satin.region U (Journey.side Y m s)) f
  siteT : AtSupport false (Satin.region V₀ (Journey.side Y m s)) (Tilted.Ramp.bill P f)
  right : Fits Y m s P r (Acres P r) U
  left : Fits Y m s P r (P.s.act '' Acres P r) V₀
  unwrap : PhaseChoice.FullDistances (V₀∪U) (Journey.side Y m s)
  parted : Detached Λ l V₀ U
lemma CanInspect.gap {U V₀}{f}(p:CanInspect Y m s P r U V₀ f) : ∀ x∈Satin.region V₀ (𝗠 m s),∀ y∈ Satin.region U (𝗠 m s),2*(Advance.nearZero (aliasLaw Λ)+distanceLaw l) < separation x y := Tarmac.contrast p.unwrap p.parted
local notation "Bu" z:max=> volumeAround Λ l z U
local notation "Bv" z:max=> volumeAround Λ l z V₀
include H in
lemma prices_upper (A:Finset Cover) (W:Set RSpace) (p:PhaseChoice.SupportedPhysically Λ l s A W) : ∀ᶠ m in atTop, ∀ d:ℕ, Fits Y m (s+d) P r W (volumeAround Λ l d A):= by
 obtain ⟨c,e⟩ := ((compact_hull Λ l s A).image (show Continuous fun x:RSpace=> |landN P x|+(r:ℝ) from ((continuous_abs.comp (landNp P)).add continuous_const))).bddAbove
 have g:Tendsto (fun m=> ((𝗠 m s).val:ℝ)) atTop atTop:= tendsto_natCast_atTop_atTop.comp (SlabMark.goes Y H s)
 filter_upwards [g.eventually_gt_atTop (c/gaugeMesh Λ s)] with m q d
 refine ⟨p.persists d,fun x hx=>?_⟩
 have hs: |landN P x|+(r:ℝ) ≤ c := e (Set.mem_image_of_mem _ (hull_persists Λ l s A d hx))
 have ht := (div_lt_iff₀ (gaugeMesh_pos Λ s)).1 q
 apply lt_of_le_of_lt hs; unfold period; rw [period_width]
 change c < gaugeMesh Λ s * (((𝗠 m s).val*2:ℕ):ℝ) / 2; rw [Nat.cast_mul,Nat.cast_ofNat]; linarith
include H in
lemma funded_region (p:PhaseChoice.SupportedPhysically Λ l s U (Acres P r))(q:PhaseChoice.SupportedPhysically Λ l s V₀ (P.s.act '' Acres P r)) : ∀ᶠ m in atTop, ∀ d:ℕ, Fits Y m (s+d) P r (Acres P r) (Bu d) ∧ Fits Y m (s+d) P r (P.s.act '' Acres P r) (Bv d) ∧ PhaseChoice.FullDistances (Bv d∪ Bu d) (Journey.side Y m (s+d)) ∧ Detached Λ l (Bv d) (Bu d):= by
 filter_upwards [prices_upper Y H s P r U _ p,prices_upper Y H s P r V₀ _ q, unwrapped Y H s (V₀∪U)] with m a b c d
 have hp:= unpaired P r; have hz:= PhaseChoice.separatedPhys q p (Disjoint.preimage _ hp)
 exact ⟨a d,b d,Tarmac.dist_mono_here (Finset.union_subset (Tarmac.origin_mono Finset.subset_union_left d) (Tarmac.origin_mono Finset.subset_union_right d)) (c d),Around_detaches Λ l hz d⟩
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened
