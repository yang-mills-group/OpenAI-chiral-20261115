import ZecaNimbus
import ZecaHallow
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
local notation "W"=> P.calibration
local notation "ℓ"=> P.calibration.ℓ
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
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

/- G3 application. Negative b-displacement d on the exact mesh. -/
def towardLeft (b:Axis) (d:ℝ):Vantage:=fun j => if j=b then -d else 0
def rain (b:Axis)(hb:b≠3)(p:Plume_LocalFieldBounds)(d:Skiff5):Plume_LocalFieldBounds where
 k:=p.k+d.k
 num:=fun j=> (p.num j)*5^d.k - (if j=b then (d.num :ℤ)*5^p.k else 0)
 u:=by rw [if_neg (Ne.symm hb),sub_zero]
       exact mul_pos p.u (by positivity)
lemma rain_pose (b:Axis)(hb:b≠3)(p:Plume_LocalFieldBounds)(d:Skiff5):
 (rain b hb p d).pose=p.pose+towardLeft b d.d:=by
 funext j
 simp only [Plume_LocalFieldBounds.pose,Pi.add_apply,rain,Skiff5.d,towardLeft]
 split <;> push_cast <;> rw [pow_add] <;> field_simp <;> ring

variable {b:Axis} (hb:b≠3){a c:ℝ}
local notation "O"=> Option (brig a c)
local notation "Δ" => ZecaSky.pitch (beam5 a c)
-- need explicit a c

def falling (hb:b≠3) (p:Plume_LocalFieldBounds): O → Plume_LocalFieldBounds
 | none => p
 | some k => rain b hb p k.val
lemma falling_pose(p:Plume_LocalFieldBounds) (k:O):
 (falling hb p k).pose=p.pose + towardLeft b (Δ k):=by
 cases k with
 | some k => exact rain_pose b hb p k.val
 | none =>
    funext; change p.pose _ = p.pose _ + towardLeft b 0 _
    simp [towardLeft]
lemma falling_tar(p:Plume_LocalFieldBounds)(k:O):
 (falling hb p k).tar=p.tar:=by
 rw [Plume_LocalFieldBounds.tar,falling_pose, Pi.add_apply,towardLeft,if_neg (Ne.symm hb),add_zero]
lemma rotary_matches (p:Plume_LocalFieldBounds) (k l:O):
 tendril (falling hb p k) (falling hb p l)= rotary b p.tar (Δ k-Δ l):=by
 unfold tendril
 rw [falling_pose, falling_pose]
 unfold rotary
 -- tune ext on lambda
 congr 1
 funext j
 simp only [Plume_LocalFieldBounds.tar,Pi.add_apply,towardLeft]
 by_cases d:j=3
 · subst j
   simp only [if_neg hb.symm,ite_true]
   ring
 · rw [if_neg d]
   split <;> ring
#check @rotary_matches


variable {F:P.Nib 3 (P.advocate 3 x 3)}{sc:ℕ→ℂ}{seq:ℕ→ℕ}
lemma skiffG (m:P.Mach x F sc seq) (p:Plume_LocalFieldBounds) (d:P.aboveRoof p):
 Accord Yoke.witnessZ SU.group b p.tar (beam5 a c)
   (fun n (k:O)=>P.kestrel x F sc (falling hb p k) (seq n)):=by
 intro i j
 have h(k:O):P.aboveRoof (falling hb p k):=by unfold aboveRoof;rw [falling_tar];exact d
 rw [← rotary_matches hb]
 exact m _ _ (h i) (h j)
abbrev singer (f:ℕ)(p:Plume_LocalFieldBounds) (r:ℕ):M:=P.fly x f r (P.spacedPitch r p)
lemma skiffM (W₀:5∣P.par.R.L.val) (T:P.Nepenthe seq x) (p:Plume_LocalFieldBounds):
 Accord Yoke.witnessZ SU.group b p.tar (beam5 a c)
   (fun n (k:O)=>P.singer x f (falling hb p k) (seq n)):=by
 intro i j
 rw [← rotary_matches hb]
 simpa only [finch,singer,add_zero,lyric] using P.freed_gram (f:=f) x (falling hb p i)
    (falling hb p j) 0 0 W₀ T

lemma G_copy (p:Plume_LocalFieldBounds)(k:O):
 P.kestrel x F sc (falling hb p k) r =
   Γ (P.jetS r • towardLeft b (Δ k)) (P.kestrel x F sc p r):=by
 unfold kestrel kestrelRig warpPose
 rw [falling_tar,falling_pose,smul_add,add_comm (P.jetS r • p.pose),P.cart_paves]
 rfl
#print axioms skiffM
