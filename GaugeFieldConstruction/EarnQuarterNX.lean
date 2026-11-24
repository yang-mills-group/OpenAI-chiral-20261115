import GaugeFieldConstruction.BuckAuthorNX
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 130000
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
namespace Spine
open Aria Set OS.Semigroup Ballad Six Glaze
open Papal FrameP Fock.Flux Gleam BProof.PricePort Gleam.Guide Gleam.clocks
open Lead Designs
-- actual Legend.T criterion ADDS no change in right hand ph pairing. path Mat.Coordinates in Gauge._
open XGarden XGarden.MastTin XGarden.Shield
open Scree.Ing.Ivey.ShoreQ
open AnalyticBridge VerifiedReset Taxi Push.Uniform Tap
open TableF TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
variable {n:Side}{N:ℕ}(A:BeaconNX N)(P:BudgetPoint)
lemma EraWordLifeNX {o:Skye.Seat n}{d:ℕ} (h:A.1.patio.image (wrap (More n))⊆ CanoeNX o d)(t:SU.Slot× SU.Slot): DomainP (CanoeNX o d) (wordLegNX A n t.1 t.2):=by
 change node (wrap n A.1.birth)∈_ ∧ node (wrap n A.1.death)∈_
 rw[node_of,node_of]; exact ⟨h (mem_image_of_mem _ (porchBorn _)), h (mem_image_of_mem _ (porchGone _))⟩
lemma EarnQueenNX (h:ℝ): ∃ f:ℝ,0≤f∧∀ (n:Side)(P:BudgetPoint)(o:Skye.Seat n)(d:ℕ),P.order≤6 → A.1.patio.image (wrap (More n))⊆ CanoeNX o d → DonauNX d P o h (BookBirthNX A n) f:=by
 obtain ⟨w,t⟩:= accountPinNX A
 let V:= ∑ i:SU.Slot × SU.Slot,h^2*w i
 refine ⟨max V 0,le_max_right ..,fun n P o d v u=>?_⟩
 apply CanoeNX_up o _ (le_max_left ..)
 have ht: DonauNX d P o h (PureFNX A n) V:=by rw[alignsΦNX]; exact CanoeNX_sum _ univ _ _ (fun i _=>moorKulNX o _ (EraWordLifeNX A u i) _ (t n P o _ v u i)) -- tune args
 apply CanoeNX_up o (CanoeNX_scale o ht (WindLifeNX A n)); rw [feeLifeNX,one_mul]
#print axioms bookGritNX
#print axioms EarnQueenNX
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
