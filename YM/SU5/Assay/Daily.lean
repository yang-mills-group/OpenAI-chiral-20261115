import YM.SU5.Assay.Approach
import YM.SU5.Selected.Parish
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
variable {P:Spine}{j:Axis}{s v w:ℕ}{f g:P.Test}
local notation "Λ"=> P.par
local notation "Y"=> P.run
local notation "K"=> P.calibration
local notation "H"=> P.large
local notation "b"=> ruler (Λ).block
local notation "V"=> P.law
local notation "L"=> (Λ).R.L.val
local notation "π"=> P.history
local notation "Qt"=> P.projection.clipped
local notation "C₀"=> P.room j
local notation "σ"=> P.shifts j

local notation "μ"=> P.meanBox
local notation "ν"=> P.euclOp
local notation "T"=> P.shiftOp
local notation "Ν"=> whenly (timeMesh (Λ))
local notation "Ω"=> P.floorVec
local notation "S"=> enclave K
open Set Metric
variable (P)
/-- Toolkit paid at unit price or less. Same assumption also for tools *not*
 gauge invariant. Time frame relative coordinates. -/
def onShelf (Z:Finset Cover):Set P.Test:={f|f∈bay K Z true ∧ pay f.val 1}
/-- Allowed supplies for composing bias spectators. -/
def inRoom (Z:Finset Cover):Set P.Test:={f|f∈bay K Z true ∧ f∈S∧∀m,Continuous (f.val m)}
variable(j s w)(Z:Finset Cover)(R:P.Register)(q:Between P.calibration j 0 (ruler P.par.block*w) Z)(p:0<w)
local notation "Q"=> μ j s w
include q p in
lemma from_bay {f:P.Test}(u:f∈bay K Z true):P.BEntry j w f:=⟨p,Z,u,q⟩
include q p R in
lemma compact_shelf:IsCompact (closure (Q '' P.onShelf Z)):=by
 let F:=P.localBox j s w p Z q
 obtain ⟨B,h,d⟩:=(show IsCompactOperator F.toLinearMap from P.compact_boxes j s w p Z q R).image_closedBall_subset_compact 1
 refine h.of_isClosed_subset isClosed_closure (closure_minimal ?_ h.isClosed)
 rintro _ ⟨f,⟨u,y⟩,rfl⟩
 obtain ⟨x,e⟩:= rendered Z K u
 refine d ⟨x,?_,?_⟩
 · rw [mem_closedBall_zero_iff]; apply PhaseChoice.sample_price Y H; rw [e];exact y
 · exact (meanBox_card s (P.openingCard j s w Z q x) p (Subtype.ext e)).symm
include q p in
lemma daily_near : (Q '' P.onShelf Z)⊆ closure (Q '' P.inRoom Z):=by
 rintro _ ⟨f,⟨u,y⟩,rfl⟩
 let h:=P.from_bay j w Z q p u
 obtain ⟨x,e,g⟩:=PhaseChoice.renovate Y H V P.projection j C₀ Z s w q p (h.card s) u
 rw [meanBox_eq s h]
 have t:= tendsto_subtype_rng.mp g
 change Tendsto (fun i=> P.Box j s w p (x i)) atTop (𝓝 (P.Box j s w p (h.card s))) at t
 refine isClosed_closure.mem_of_tendsto t (Eventually.of_forall fun i=>subset_closure ?_)
 exact ⟨P.entryTest j s (x i),⟨(e i).1,(enclave_spec K).mpr (e i).2.1,(e i).2.2⟩, meanBox_card s (x i) p rfl⟩

include q p R in
lemma reserve_daily(x:P.Spectrum0 j)(n:ℕ){δ:ℝ}(v:0<δ):
 ∃(F:Finset P.Test),(∀i∈F,i∈P.inRoom Z)∧∃ a f,P.Placard j w n F a f ∧ let z:= μ j s a f (Ω j)
  ‖z‖<2 ∧ ‖P.rinse j s w n z‖=1 ∧∀i∈P.onShelf Z, ‖P.framed j s w n i z - P.singleState j s x i‖<δ:=
 P.approach_earns j s w n _ _ (fun _ h=>P.from_bay j w Z q p h.1) (fun _ h=>P.from_bay j w Z q p h.1)
   (P.compact_shelf j s w Z R q p) (P.daily_near j s w Z q p) x R v
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
