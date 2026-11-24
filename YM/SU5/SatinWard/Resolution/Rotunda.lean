import YM.SU5.SatinWard.Resolution.IslandU
import YM.SU5.Assay.CharterCost
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 100000
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
namespace Rotunda
open MeshClock MeshClock.Carousel
local notation "Ξ"=>P.VMark
local notation "SØ"=> timeMesh P.par
local notation "B₀"=> P.ManyF j x
local notation "Φ"=> P.physicalEnergy j x
local notation "R"=> P.seasons j x
local notation "Γ"=> P.charter j x
local notation "Ω"=>P.laysM
variable (A T: (P.ColorHil j x).Op)
noncomputable abbrev charterL :P.VMark→ (P.ColorHil j x).Op:= fun u=> Γ u A
local notation "Η" A:max=> charterL P j x A
def Earned (A:X):Prop:=UniformContinuous (charterL P j x A)
local notation "HR"=> Earned P j x
noncomputable def royal : Vantage→ (P.ColorHil j x).Op:= sphereEm (timeMesh P.par) (charterL P j x A)
local notation "ℛ"=> royal P j x
variable {A T}(u:Earned P j x A)(w:Earned P j x T)
local notation "γ"=> liftP (timeMesh P.par) Axis
include u
lemma extending : UniformContinuous (ℛ A) := uniformContinuous_uniformly_extend (liftp_iso _).isUniformInducing (liftp_dense _) u
lemma transport (z:P.VMark): royal P j x A (P.laysM z)=Γ z A:= (liftp_visible (timeMesh P.par)).extend_eq (show Continuous (Η A) from UniformContinuous.continuous u) _
lemma fromGone : royal P j x A 0=A:= by rw [← P.lays_zero,transport _ _ _ u, P.charter_zero]
lemma pay (V:Vantage) : ‖ℛ A V‖=‖A‖:=by
 apply congrFun ((liftp_dense (I:=Axis) (SØ)).equalizer (g:=fun v=>‖ℛ A v‖) (h:=fun _=> ‖A‖) (extending P j x u|>.continuous.norm) continuous_const (funext fun i=>?_)) V -- expected eliminator .mp. inspect
 exact congrArg norm (transport P j x u i) |>.trans (P.charter_cost j x i A)
variable {Y₀:Type*}{f:Y₀→P.VMark}{l:Filter Y₀}
lemma shore {y:Vantage}(p:Tendsto (P.laysM ∘ f) l (𝓝 y)) : Tendsto (fun i=>Γ (f i) A) l (𝓝 (ℛ A y)):= Tendsto.congr' (Eventually.of_forall fun i=>transport P j x u (f i)) ((Continuous.tendsto (extending P j x u|>.continuous) y).comp p) -- function inference defeq.Log
local notation "L"=> P.reprise j x
local notation "Κ"=> P.locate j x
lemma in_window (V:Vantage): L (royal P j x A V)= Κ V (L A):=by
 obtain ⟨g,pg⟩:=P.vantage_approach V -- import? locate uses. can get seq from closure.
 let X':=L A; let h:=P.locate_limit j x pg (BSOT.stay (l:=atTop) X'); let A':= BSOT.fromNorm (shore P j x u pg); let F:= P.reprise_bsot j x A'; exact F.unique (h.congr' (Eventually.of_forall fun n=> (P.reprise_charter j x (g n) A).symm))
include w
lemma receives (V:Vantage) : ‖ℛ A V- ℛ T V‖= ‖A-T‖:=by obtain ⟨f,h⟩:=P.vantage_approach V; apply tendsto_nhds_unique (((shore P j x u h).sub (shore P j x w h)).norm); apply Tendsto.congr' ?_ tendsto_const_nhds; exact Eventually.of_forall fun i=>(P.charter_dist j x (f i) A T).symm
-- after dark X.Owner can let reconstruction collar.s.grit. Support accountant.Need next op purchase.Brit.So.
#print axioms in_window
omit w u
end Rotunda
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
