import ZecaEggshell
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
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "ℓ"=> P.calibration.ℓ
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s f r v i k:ℕ}
local notation "Λ"=> P.par
/-! # Buy height and travel together. Keep both actual calibration and rank resolution schedule. -/
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)
open Aria Casting MacroGrid
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)

local notation "z'"=> Yoke.witnessZ
local notation "κ"=>P.sidesPerTick
local notation "κz"=> (P.sidesPerTick:ℤ)

variable (x : P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "M"=> P.ColorHil 3 (ξ)
local notation "G"=> P.ManyF 3 (ξ)
local notation "Ω"=> P.colorZero 3 ξ
local notation "Γ"=>P.cartage 3 ξ
local notation "Η"=>P.seasons 3 ξ
local notation "π"=>P.wealth 3 ξ
local notation "Πγ"=>P.enter 3 ξ
local notation "ω"=> P.heaven 3 ξ
open Regis.Circuit -- Aster





open _root_.YM.ZecaSky


variable (p:Plume_LocalFieldBounds)
  (F:P.Nib 3 (P.advocate 3 x 3))
  (c:ℕ→ℂ)
  {seq:ℕ→ℕ}

def ontoRoof:Prop:=(P.roof:ℝ)+1≤p.tar
-- reversed tilt
def zecaStern(f r:ℕ):=P.kestrelRig x F c p r (P.mWarp f r p)
#check zecaStern
variable (t:P.ontoRoof p)
include t

lemma stern_fit (d:P.granPos f r [] 3≤P.jetS r):
 P.rosePad 3 (P.pointEra r) ≤ P.mWarp f r p:=
   calc
    _ ≤ P.macroStep (P.pointEra r) * _ := P.rose_wider _
    _ = P.jetS r * (P.roof:ℝ) :=by rw [P.jetS_base,mul_assoc]
    _ ≤ _ :=by
     unfold mWarp
     linarith only [d,mul_le_mul_of_nonneg_left (show (P.roof:ℝ)+1≤p.tar from t) (P.jetS_pos r).le]

lemma stern_hot (d:P.granPos f r [] 3≤P.jetS r):
 0<P.mWarp f r p:=by
 have j:0 < (P.roof:ℝ) :=by unfold roof; positivity
 unfold ontoRoof at t
 have hj:=mul_lt_mul_of_pos_left (show (1:ℝ)<p.tar by linarith only [j,t]) (P.jetS_pos r)
 unfold mWarp
 linarith only [hj,d]
#check norm_star
#check star_smul

lemma stern_nick {error:ℕ→ℝ}(n:P.Nick f x F c error)
 (e0:Tendsto error atTop (𝓝 0))(s':Tendsto seq atTop atTop):
 Neighbor (P.zecaStern x p (P.twinNib 3 ξ F) (star c) f ∘ seq)
    (fun i=>P.mPlover x f (seq i) p) :=by
 have e:=(e0.comp s').mul_const ‖ω‖
 rw [zero_mul] at e
 refine squeeze_zero' (Eventually.of_forall (fun _=>norm_nonneg _)) ?_ e
 filter_upwards [s'.eventually n,s'.eventually (P.at_half (f:=f))] with i b d
 let r:=seq i
 let a:=P.mWarp f r p
 have h:=P.stern_fit p t d
 specialize b _ _ h h
 let Y:=P.crop 3 x f r [] a a
 let Z:=(P.plumeK r:ℂ) 
 let D:= c r • F a a - Z • Y
 have u:‖(star (c r)) • (star (F a a)) - Z • (star Y)‖ ≤ error r:=by
   have y:= (norm_star D).trans_le b
   unfold D Z at y
   rw [star_sub, star_smul,star_smul, RCLike.star_def, Complex.conj_ofReal] at y
   exact y
 refine le_trans ?_ (mul_le_mul_of_nonneg_right u (norm_nonneg ω))
 simp only [Function.comp_apply,zecaStern,kestrelRig,kestrelSeed,mPlover,← map_sub,P.cart_norm]
 exact ContinuousLinearMap.le_opNorm ((star (c r)) • (star (F a a)) - Z • (star Y)) _
#print axioms stern_nick
