import YM.SatinExist.Lazul
import YM.SatinExist.ColdSpring
import YM.SU5.Macro.Spot
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
namespace Spine
variable (P : Spine)
local notation "K" => P.calibration
local notation "Λ" => P.par
local notation "ι" => P.width
local notation "Y" => P.run
local notation "H" => P.large
local notation "ℒ" => P.law
local notation "π"=> P.history
local notation "Λ₁"=> Λ.R.L
open Afterglow.Hierarchy Hierarchy
open Chrono Hills
variable {C:Call P.par P.width}{W:Wicket P.par P.width}(R:Rolled P.run P.large P.period P.cutoff W C)
variable (j: Axis) (s : ℕ)
local notation "M₀"=> P.room j
open SalonG
variable (A' : ∀ j:Axis, Repertory P.run P.large P.law R j)
variable (x:P.Spectrum0 3)(f:Charm.W P.calibration)
local notation "U₁"=> A' j
local notation "W₀"=> route Y H s j ℒ R U₁
local notation "Ⅺ"=> (P.otherSpectrum 3 j x)
local notation "ρ"=> P.chi j Ⅺ
local notation "fβ" Q:max=> P.azureNativeInclusion Q
local notation "G"=> P.azureReadingOnSelectedVacuum x s
local notation "Φ" => P.azureReadingOnSelectedVacuum x
open Steam Eight.Bonbon Tapestry.Altitude
open Six.OneCup
local notation "φ" s:max=> P.singleState 3 s x
local notation "Ψ" s:max=> P.comparisonS x s
private lemma singleMK : Six.MatterWard K (φ s):= (P.singles_pure_ward s x).2
private noncomputable def reElect (F:Dome K)(u:F∈enclave (K)): Charm.W K:= ⟨F.val,F.property,(enclave_spec K).mp u⟩
noncomputable def sliver : Charm.W K →ₗ[ℂ] Charm.W K where
  toFun z:= P.reElect (slice K (φ s) (P.azureNativeInclusion z)) (slicing_enclave (P.singleMK s x) _ ((enclave_spec K).mpr z.property.2))
  map_add' a b:= Subtype.ext (congrArg (fun z:P.Test=>z.val) (show slice K (φ s) (fβ (a+b)) = slice K (φ s) (fβ a)+slice K (φ s) (fβ b) by rw [map_add,map_add]))
  map_smul' z a:= Subtype.ext (congrArg (fun z:P.Test=>z.val) (show slice K (φ s) (fβ (z • a)) = z • slice K (φ s) (fβ a) by rw [map_smul,map_smul]))
lemma slivers_of (d:Charm.W K)(D:Six.PureGauge K (fβ d)): P.sliver s x (d*f)=d* P.sliver s x f:= by
  apply Subtype.ext
  exact congrArg (fun z:P.Test=>z.val) (show slice K (φ s) (fβ (d*f))= fβ d * slice K (φ s) (fβ f) by rw [map_mul]; exact slicerLink (φ s) _ _ D)
lemma comp_slivers (X:Dome K→ₗ[ℂ]ℂ)(v: Six.Comparison K (φ s) X): X (fβ f)=(Φ s) (P.sliver s x f):= slicing v _
lemma sliver_loc (S:Finset Cover)(v:Charm.Locator K f S): Charm.Locator K (P.sliver s x f) S:= (Tapestry.locates K S true).mp (cuts_local (φ s) S (fβ f) ((Tapestry.locates K S true).mpr v))
open Tower.Selection.Home
private lemma re_gauged (S:Finset Cover)(m:Side)(r:Hosp S (P.calibration.c m))(z:Monochrome.Bay K S):
    (φ s) (Monochrome.reGauge K S m r z).val=(φ s) z.val:=by
  simp_rw [P.single_state]
  apply congrArg _; apply Subtype.ext
  have hZ:= Monochrome.settles S m Y H ℒ P.projection 3 (P.room 3) s r z
  have hz:= congrArg Subtype.val hZ; exact hz
include A'
private lemma estimates_single {g:ℝ}(p:0≤g)(q:∀ᶠ s in atTop, Club Y g s)(S:Finset Cover)(m:Side)(r:Hosp S (P.calibration.c m))(z:Monochrome.Bay K S): ∃ C:ℝ,0 ≤ C ∧ ∀ᶠ s:ℕ in atTop,∀ x:P.Spectrum0 3,‖P.singleState 3 s x z.val‖ ≤ C:=by
 let T:= Monochrome.reGauge K S m r z
 let F:= P.reElect T.val (Monochrome.neutral K S m r z)
 have h: Charm.Locator K F S:= (Tapestry.locates K S true).mp T.property
 let B:= duration S *‖Charm.reading K S F h‖
 have ht:= width_read h
 have hb:0≤ B:=(norm_nonneg _).trans (ht m (1,1))
 let t:=wageZ Λ H Y S g
 refine ⟨B*t,mul_nonneg hb (Real.exp_pos _).le,?_⟩; filter_upwards [q] with s q x; rw [← P.re_gauged s x S m r]; exact income Y H ℒ R A' S s q _ hb p (P.elected_sphere R A' x) F h ht -- possible placeholders
lemma sliver_cost {g:ℝ}(p:0≤g)(q:∀ᶠ s:ℕ in atTop, Club Y g s)(S:Finset Cover): ∃ t:ℝ, 0≤t ∧ ∀ᶠ s:ℕ in atTop,∀ (x:P.Spectrum0 3)(F:Charm.W K) (c:ℝ), Charm.Locator K F S → Width K F c → Width K (P.sliver s x F) (t*c):=by
 obtain ⟨m,r⟩:= (separates K S).exists
 choose C h L using fun i:Evens S=>P.estimates_single R A' p q S m ⟨r⟩ ⟨toastPoint K S i,toastAt ..⟩
 refine ⟨_,show 0≤∑ i,C i from Finset.sum_nonneg (fun i _=> h i),?_⟩; filter_upwards [Filter.eventually_all.mpr L] with s F x U c V v
 intro n Vv; change ‖(slice K (P.singleState 3 s x) (fβ U)).val n Vv‖≤ _
 exact toast_limit (P.singleState 3 s x) S m ⟨r⟩ (fβ U) ((Tapestry.locates K S true).mpr V) c C (v m)  (fun i=> F i x) _ _
#print axioms sliver_cost
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
