import NeedleW.Floor
import Aloft.Resolve
import NeedleW.Line
import Aloft.Spoon
import Aloft.BudgetA
import Aloft.Ride
import Aloft.Conceit
import Aloft.ZL
import Aloft.Canon
import Ridgetop.Origin
import Risa.Warehouse
import Preen.Chey
-- pilot price exactly zero, all. 
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 360000
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
open Aria Casting Set
open scoped Pointwise
namespace MiterT
open _root_.YM.Gleam.Luster.Risa CF.BProof AnalyticBridge.VerifiedReset
open Py.Rate.LocalLimit Py Py.Dyad Papal _root_.YM.CF.Pannier.Chancel Cliplet Precision
variable (P:Spine) 
namespace Aloft
open Py.Dyad Keeping Py.Rate.Pitching.Focus
open _root_.YM.Preen
local notation "j0"=> (3:Axis)
variable (M:Morn P.par.K)(α:ℝ)(F:ℕ)(C D:ℕ→ℕ→ℝ)(x:P.Spectrum0 3)(p:∀ s,F ≤ s→ Accordance P M F s (C s) (D s))(u:RobeRoad P F C D x)(v:Jones P M α F C D x)
local notation "ξ"=>P.otherSpectrum 3 3 x
local notation "Ω"=>P.heaven 3 ξ
local notation "Ψ"=> P.seasons 3 ξ
local notation "H"=>P.ManyF 3 ξ
local notation "ζ"=>P.wealth 3 ξ
local notation "A₀"=>paster (Ω)
local notation "U"=>P.cartage 3 ξ
namespace Anchovy
open _root_.NeedleW
variable (J:P.Ellis 3 x)
private def finask(d k:ℕ){Lμ:ℕ→(H).space→ℝ}(a:ℝ):Prop:= ∃ w:Cover, ∃ e:Enrolled P d k w, ∃ z:(H).space, (∃ g:Vantage, U g z=amber P x 0 (hikeV d+k) w e.clock.1)∧ (Lμ (hikeV d+k) z ≤ a)
set_option maxHeartbeats 650000 in
private lemma juice(d k:ℕ)(o:Cover){f:ℕ→(H).space→ℝ}{a:ℝ}(hp:(P.calibration.ℓ:ℤ)+22 ≤ nodeC o 3 ∧ nodeC o 3 ≤ (P.par.R.L.val:ℤ)^k*reachQ P (hikeV d))(q:f (hikeV d+k) (amber P x 0 (hikeV d+k) o hp.1) ≤ a): finask P x d k (Lμ:=f) a:= enroll (shifted P (hikeV d+k) x o hp.1) q
where enroll (θ: ∃ y:Cover, ∃ h:nodeC y 3=nodeC o 3, (∀i:Axis,i≠3→0 ≤nodeC y i ∧ nodeC y i ≤ (ruler P.par.block)) ∧ ∃ g:Vantage,amber P x 0 (hikeV d+k) y (hp.1.trans_eq h.symm)=U g (amber P x 0 (hikeV d+k) o hp.1))(q:f (hikeV d+k) (amber P x 0 (hikeV d+k) o hp.1) ≤ a):finask P x d k (Lμ:=f) a:=by
        obtain ⟨y,e,g,z,r⟩:=θ
        have hE:Enrolled P d k y:= ⟨g,e.symm ▸ hp⟩
        exact ⟨y,hE,amber P x 0 (hikeV d+k) o hp.1,⟨z,r.symm⟩,q⟩
variable (G:ℕ→ (P.ManyF 3 (P.otherSpectrum 3 3 x)).space)(g:∀ i,F ≤ i→PeriodS P F C D x i (G i))
local notation "z" j:max=>A₀ (G j)
-- avoid z identifiers in finask uses
include p v g
set_option maxHeartbeats 570000 in
lemma boundLine: ∀ᶠ d:ℕ in atTop,∀ m:ℕ,∃ w:Cover,∃ e:Enrolled P d m w, ∃ k:H,
 (∃ u':Vantage,U u' k=amber P x 0 (hikeV d+m) w e.clock.1) ∧ ‖clean (z (hikeV d)) k‖ ≤ thresholdU P M α d m:=by
 let k(d):=z (hikeV d)
 filter_upwards [windows P M α F C D x p v G g] with d he m
 let o:=fell P F d m
 have hx:‖(scaffold P x (k d)) (sparrow P F ξ _ _)‖ ≤ thresholdU P M α d m:=he m
 exact juice P x d m o (f:=fun _ t=>‖clean (k d) t‖) (toad ..) hx -- amber definally?
#check @windows
#print axioms boundLine
end Anchovy
end Aloft
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
