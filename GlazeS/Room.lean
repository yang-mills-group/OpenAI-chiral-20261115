import GlazeS.CastLight
import SatinFacet
import Crape.Halo
import Crape.Adjust
import Crape.Supple
import Crape.TimeLine
import Nankin.Bern
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
namespace PledgeT
open Calico
set_option maxRecDepth 6000
set_option maxHeartbeats 700000
open Aria Casting Set
open scoped Pointwise
namespace MiterT
open MacroGrid
variable (P:Spine) (t:ℕ)(F:SampleDose)
local notation "U"=>P.meshPose t
local notation "θ"=>P.macroStep t
local notation "Q"=> P.usedGrid t F
local notation "α" k:max => P.activation t F k
private lemma intoGrid (X:Hilbert)(f:Vantage→X)(T:Cover → X.Op):
 poseApprox X (fun z:Vantage=>(F.val z:ℂ) • f z) T (θ) =∑ i∈ Q, α i • T i (f (U i)):=by
 let g:=fun i:Cover=> T i ((F.val (U i):ℂ) • f (U i));
 have he(i:Cover)(x:i∉Q): g i=0:= by
    have hu : F.val (U i)=0:=by by_contra p; exact x ((P.usedPose t F i).2 (subset_closure p))
    unfold g; rw [hu,Complex.ofReal_zero,zero_smul,map_zero]
 refine (room_price θ (P.macroStep_pos t) g Q he).2.trans ?_
 rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro i h; change ((θ)^Fintype.card Axis:ℝ) • _=_; unfold g; rw [map_smul,show Fintype.card Axis=4 by rfl, ← Complex.coe_smul (θ^4), smul_smul]; push_cast [activation]; rfl
-- obsolete domains removed.
variable (x:P.Spectrum0 3)(J:P.Ellis 3 x)
local notation "ξ"=>P.advocate 3 x 3
local notation "H0"=>P.ColorHil 3 ξ
local notation "H"=>P.ManyF 3 ξ
local notation "S" => P.physicalEnergy 3 ξ
-- P.contraction along t.R grid. limit
noncomputable def scoop(P:Spine)(x:P.Spectrum0 3)(g:P.ColorHil 3 (P.otherSpectrum 3 3 x))(F:SampleDose)(p:Vantage):P.ManyF 3 (P.otherSpectrum 3 3 x):=
 P.cartage 3 _ p (P.wealth 3 _ ((F.val p:ℂ) • (P.physicalEnergy 3 _).E ((p 3).toNNReal) g))
include J
lemma verge (g:P.ColorHil 3 (P.otherSpectrum 3 3 x)): Tendsto (fun t=>∑ i∈P.usedGrid t F,P.activation t F i • P.truck 3 (P.otherSpectrum 3 3 x) (P.vtile t i) ((P.physicalEnergy 3 (P.otherSpectrum 3 3 x)).E ((P.meshPose t i 3).toNNReal) g)) atTop (𝓝 (P.enter 3 (P.otherSpectrum 3 3 x) (∫ p:Vantage, scoop P x g F p))) :=by
 let f(p:Vantage):= (S).E ((p 3).toNNReal) g
 let a(p:Vantage):= (F.val p:ℂ) • f p
 have h: HasCompactSupport a:= F.budget.mono (fun x v p=> v (show a x=0 by unfold a; rw [show F.val x=0 from p,Complex.ofReal_zero,zero_smul]))
 have hg:Continuous a:= (Complex.continuous_ofReal.comp F.smooth.continuous).smul (((S).continuousE g).comp (continuous_real_toNNReal.comp (continuous_apply 3))) -- S macro parentheses
 exact (P.macroRiemann x 3 J a h hg).congr fun t=> intoGrid P t F H0 f _
#print axioms verge
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
