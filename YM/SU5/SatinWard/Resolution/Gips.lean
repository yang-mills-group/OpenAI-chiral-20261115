import YM.SU5.SatinWard.Resolution.HaloLens
import YM.SU5.Assay.Issuing
-- adapt TollBelt (Glaze incompatible)
import YM.SU5.Assay.EngineAxle
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "K"=> P.calibration
local notation "H"=> P.ColorHil j x
local notation "B"=> P.ManyF j x
local notation "X"=> (P.ColorHil j x).Op
local notation "Y"=> (P.ManyF j x).Op
local notation "Lag"=>ℝ→ℝ→(P.ManyF j x).Op
local notation "S"=> P.seasons j x
local notation "U"=> P.physicalEnergy j x
local notation "ω"=> (P.seasons j x).wax
local notation "W"=> P.cartage j x
local notation "θ"=> P.tableau j x
local notation "E"=> P.enter j x
local notation "R"=> P.wealth j x
local notation "Vac"=> P.colorZero j x
local notation "Ω"=> P.heaven j x
/-! Measure across a belt seam at this very height. Also controls all lags outward, even
 immediately at joint enrollment. -/
variable (D:P.Apron){a b c d:ℝ}
local notation "τ"=>P.tock
local notation "β"=>P.rawBase j x
local notation "ρ"=> P.charter j x
local notation "𝔤"=>P.Grips j x
local notation "δ"=>D.realWidth P j
lemma grasp_fixed (p:δ≤a)(q:δ≤b):𝔤 D.s (-a) b D.F (β D a b):=by
 let s:=D.s; let w:=D.u j
 have h₁:τ s (-(w:ℤ))= -δ:=by rw [←zero_sub (w:ℤ), P.tock_sub,P.tock_zero,zero_sub];rfl
 have h₂:τ s (-(w:ℤ)+((w+w:ℕ):ℤ))=δ:=by rw [Nat.cast_add,←add_assoc,neg_add_cancel,zero_add];rfl
 let g:=D.admit j
 refine Sill.grips (m:=-(w:ℤ)) (w:=w+w)
   ⟨by erw [h₁]; exact neg_le_neg p,by erw [h₂];exact q,⟨by rw [neg_neg];exact g,D.realM⟩,?_⟩
 erw [h₁,h₂,costing,neg_neg]
 rw [show -δ- -a=a-δ by abel,P.rawBase_engineAxle];rfl
lemma nap_place (y:Cover): P.issuing D.s D y=P.chartAll y D.F:=by unfold issuing Apron.full;rw [Nat.sub_self];rfl
lemma grasp_place (y:Cover)(p:δ≤τ D.s (y j)-a)(q:δ≤b-τ D.s (y j)):
 𝔤 D.s a b (P.chartAll y D.F) (ρ (P.vtile D.s y) (β D (τ D.s (y j)-a) (b-τ D.s (y j)))):=by
 let t:=P.issuing_grips j x D.s D y le_rfl p q
 rw [nap_place,P.raze_align] at t
 exact t

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
