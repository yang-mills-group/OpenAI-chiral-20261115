import YM.SU5.Assay.Locate
import YM.SU5.Six.PressSmear
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
open MacroGrid
/-!
 Full quadrature helper (generalization of that in FineRays).
-/
variable (F:SampleDose)(t:ℕ)
local notation "δ"=>P.macroStep t
local notation "Q"=>P.usedGrid t F
local notation "Φ"=>P.activation t F
local notation "Z"=>P.meshPose t
lemma activation_real (i:Cover):star (Φ i)=Φ i:= by rw [activation,Complex.star_def,Complex.conj_ofReal]
lemma activation_norm (i:Cover):‖Φ i‖=δ^4*‖F.val (Z i)‖:=by
 rw [activation,Complex.norm_real,norm_mul,Real.norm_of_nonneg (pow_nonneg (P.macroStep_pos t).le 4)]
abbrev gridMass :=∑i∈Q, ‖Φ i‖
lemma gridMass_limit : Tendsto (fun i=>P.gridMass F i) atTop (𝓝 (∫x,‖F.val x‖)):=by
 let g(y:Vantage):=‖F.val y‖
 refine (rSum_limit P.macroStep P.macroStep_zero g F.smooth.continuous.norm P.macroStep_pos
   (show HasCompactSupport F.val from F.budget).norm).congr (fun t=>?_)
 let y(i:Cover):=g (P.meshPose t i)
 have v:∀i,i∉P.usedGrid t F→y i=0:=by
   intro i h
   rw [P.usedPose] at h
   unfold y g; rw [image_eq_zero_of_notMem_tsupport h,norm_zero]
 have hp:=room_price _ (P.macroStep_pos t) y _ v
 refine hp.2.trans ?_
 rw [Finset.smul_sum,gridMass]; refine Finset.sum_congr rfl fun i _=>?_
 rw [activation_norm];rfl
lemma gridMass_cap :∀ᶠt in atTop,P.gridMass F t≤ (∫x,‖F.val x‖)+1:= (P.gridMass_limit F).eventually (ge_mem_nhds (lt_add_one _))
lemma activates (L:Hilbert)(f:Vantage→L)(u:Cover → L.Op):
 poseApprox L (fun z:Vantage=>(F.val z:ℂ) • f z) u (δ) =∑i∈Q,Φ i • u i (f (Z i)):=by
 let g:=fun i:Cover=> u i ((F.val (Z i):ℂ) • f (Z i));
 have he(i:Cover)(x:i∉Q): g i=0:= by
    have hu : F.val (Z i)=0:=by by_contra p; exact x ((P.usedPose t F i).2 (subset_closure p))
    unfold g; rw [hu,Complex.ofReal_zero,zero_smul,map_zero]
 refine (room_price δ (P.macroStep_pos t) g Q he).2.trans ?_
 rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro i h; change ((δ)^Fintype.card Axis:ℝ) • _=_; unfold g; rw [map_smul,show Fintype.card Axis=4 by rfl, ← Complex.coe_smul (δ^4), smul_smul]; push_cast [activation]; rfl
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
