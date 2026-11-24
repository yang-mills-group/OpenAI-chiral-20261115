import ZecaCorvid
import ZecaKite
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




-- C transfer assuming allowance plus close. 
section
variable (F:P.Nib 3 (P.advocate 3 x 3)) (c:ℕ→ℂ)
def kestrelSeed (r:ℕ)(t:ℝ):G:= c r • F t t ω
def kestrelRig (p:Plume_LocalFieldBounds) (r:ℕ)(t:ℝ) := Γ (P.warpPose r p)
    (P.kestrelSeed x F c r t)
def kestrelTilt (p:Plume_LocalFieldBounds)(f r:ℕ) := P.kestrelRig x F c p r (P.warpf f r p)
def kestrel (p:Plume_LocalFieldBounds)(r:ℕ) := P.kestrelRig x F c p r (P.jetS r*p.tar)

variable (h:P.Bottle 3 (P.advocate 3 x 3) F)
include h
local notation "seed"=>P.kestrelSeed x F c
lemma kestrel_scale(t u:ℝ)(t0:0<t)(p:t≤u):
 seed r u=(Η).E ((u-t).toNNReal) (seed r t):=by
 let t':=(u-t).toNNReal
 have ht:P.buff 3 ξ (u-t) (u-t) (F t t) ω= (Η).E ((u-t).toNNReal) (F t t ω):=by
    show (Η).E _ (F t t ((Η).E _ ω))=_
    rw [P.heaven_hot]
 unfold kestrelSeed; rw [h.prop t0 t0 p p,map_smul,ht]

lemma kestrel_speed(t u v a:ℝ)(t0:0<t)(x0:0<a)
 (ea:t+a≤u)(ka:t+a≤v):
 ‖seed r u-seed r v‖≤ (2 / a*|u-v|)*‖seed r t‖:=by
 have e:= SatinJets.Stellar.flight_steeper Η x0 (le_sub_iff_add_le'.mpr ka) (le_sub_iff_add_le'.mpr ea)
 rw [sub_sub_sub_cancel_right] at e
 rw [P.kestrel_scale (r:=r) x F c h t u t0 ((le_add_of_nonneg_right x0.le).trans ea),
     P.kestrel_scale (r:=r) x F c h t v t0 ((le_add_of_nonneg_right x0.le).trans ka)]
 exact (ContinuousLinearMap.le_opNorm
       ((Η).E ((u-t).toNNReal)-(Η).E ((v-t).toNNReal))
       _).trans (mul_le_mul_of_nonneg_right e (norm_nonneg _))

omit h
-- fee ~ 1/K for comparing time pitches
abbrev curlCost(f r:ℕ):ℝ:= 2/P.jetS r * P.granPos f r [] 3
lemma curl_go: Tendsto (P.curlCost f) atTop (𝓝 0):=by
 have hv:Tendsto (fun r=> 2*P.echoFoot/(P.plannedK r:ℝ)) atTop (𝓝 (0:ℝ)):=
   tendsto_const_nhds.div_atTop P.planned_grows
 refine squeeze_zero (fun r=>mul_nonneg
    (div_nonneg (by norm_num) (P.jetS_pos r |>.le)) P.fly_time_stem) (fun r=>?_) hv
 have e:= (le_abs_self _).trans (P.granPos_tiny (f:=f) (v:=r) 3 [])
 have ha: 0 < P.jetS r:= P.jetS_pos r
 refine (mul_le_mul_of_nonneg_left e (show 0≤2/P.jetS r by positivity)).trans_eq ?_
 have s':0<P.macroStep r:=P.macroStep_pos r
 unfold jetS
 have e':0 < (P.plannedK r:ℝ):=Nat.cast_pos.mpr (P.pointK_pos ..)
 field_simp

lemma at_half: ∀ᶠ r:ℕ in atTop, P.granPos f r [] 3≤P.jetS r:= by
 filter_upwards [(P.curl_go (f:=f)).eventually (ge_mem_nhds (show (0:ℝ)<2 by norm_num))] with r p
 have h:=P.jetS_pos r
 rw [curlCost,div_mul_eq_mul_div,div_le_iff₀ h] at p
 linarith only [p]

variable (p a:Plume_LocalFieldBounds) (d:a.tar+2≤p.tar)
include d h
lemma fast_tilt:
 ∀ᶠ r:ℕ in atTop,
 ‖P.kestrel x F c p r - P.kestrelTilt x F c p f r‖≤
 P.curlCost f r * ‖P.kestrelTilt x F c a f r‖:=by
 filter_upwards [P.at_half (f:=f)] with r e
 let t:=P.warpf f r a
 let v:=P.warpf f r p
 let w:=P.jetS r*p.tar
 let δ:=P.jetS r
 have htw:t+δ≤w:=by
   have ht:=mul_le_mul_of_nonneg_left d (P.jetS_pos r).le
   unfold t δ w warpf
   linarith only [e,ht]
 have hd:w-v= -(P.granPos f r [] 3):=by unfold w v warpf; ring
 have h':=P.kestrel_speed (r:=r) x F c h t w v δ (P.warpPos_hot a) (P.jetS_pos r)
      htw (htw.trans (show w≤v from le_add_of_nonneg_right P.fly_time_stem))
 rw [hd,abs_neg,abs_of_nonneg P.fly_time_stem] at h'
 unfold kestrelTilt kestrel kestrelRig
 rw [← map_sub,P.cart_norm,P.cart_norm]
 exact h'

variable {seq:ℕ→ℕ}
lemma detilted (e:Tendsto seq atTop atTop)
 {B:ℝ}(b:∀ᶠ i:ℕ in atTop, ‖P.kestrelTilt x F c a f (seq i)‖≤B):
 Tendsto (fun i=> ‖P.kestrel x F c p (seq i) - P.kestrelTilt x F c p f (seq i)‖)
 atTop (𝓝 0):=by
 have h':=((P.curl_go (f:=f)).comp e).mul_const B
 rw [zero_mul] at h'
 apply squeeze_zero' (Eventually.of_forall (fun _=>norm_nonneg _)) _ h'
 filter_upwards [e.eventually (P.fast_tilt (f:=f) x F c h p a d),b] with i t hb
 exact t.trans (mul_le_mul_of_nonneg_left hb
    (mul_nonneg (div_nonneg (by norm_num) (P.jetS_pos _).le) P.fly_time_stem))
end
