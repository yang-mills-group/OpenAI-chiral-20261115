import ZecaGannet
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


variable (F:P.Nib 3 (P.advocate 3 x 3))
  (c:ℕ→ℂ) (seq:ℕ→ℕ)
local notation "F'"=>P.twinNib 3 ξ F
lemma skip_anti
  (h:P.Bottle 3 (P.advocate 3 x 3) F){t u:ℝ}(p:0<t)(d:t≤u):
 P.skipping x F u ≤ P.skipping x F t:=by
 have k:=P.kestrel_scale (r:=1) x F 1 h t u p d
 unfold skipping
 simp only [kestrelSeed, Pi.one_apply,one_smul] at k
 rw [k]
 exact Hierarchy.Seld.stayPay _ _ _

def teeter (t:ℝ):= P.skipping x F t + P.skipping x (P.twinNib 3 ξ F) t

lemma totter (l:P.MyJet x F)
  (h:P.Bottle 3 (P.advocate 3 x 3) F)
  (j:P.Bottle 3 (P.advocate 3 x 3) (P.twinNib 3 (P.advocate 3 x 3) F)):
 Gait (P.teeter x F) :=by
 obtain ⟨B,m,b,w⟩:=h.pay
 refine ⟨fun t p=> add_pos_of_pos_of_nonneg (norm_pos_iff.mpr (l t t p p)) (norm_nonneg _),
   fun p q=>add_le_add (P.skip_anti x F h p q) (P.skip_anti x _ j p q),
   B*(‖ω‖+‖ω‖+1),m,by positivity,fun t u y=>?_⟩

 refine (add_le_add (ContinuousLinearMap.le_opNorm (F t t) ω)
     (ContinuousLinearMap.le_opNorm (star (F t t)) ω)).trans ?_
 rw [norm_star,← mul_add, mul_div_right_comm]
 exact mul_le_mul (w t u y) (le_add_of_nonneg_right zero_le_one)
    (by positivity) (by positivity)
#print axioms totter

lemma sesqui (q:P.Mach x F c seq)
  (z:P.Mach x (P.twinNib 3 (P.advocate 3 x 3) F) (star c) seq)
 {a:ℕ}{D:ℝ}(b:0<D)
 (e:∀i t,0<t→
    P.teeter x F (P.jetS (seq i)*t) ≤
     P.teeter x F (P.jetS (seq i)*P.startW.tar) * D*spur a t):
 P.Ebb x F c seq ∧ P.Ebb x (P.twinNib 3 (P.advocate 3 x 3) F) (star c) seq:=by
 obtain ⟨A,v,w⟩:=P.gram_paid x F c seq q
 obtain ⟨B,r,u⟩:=P.gram_paid x F' (star c) seq z
 have h(i):‖c (seq i)‖ * P.teeter x F (P.jetS (seq i)*P.startW.tar)≤A+B:=by
    unfold teeter
    rw [mul_add,← norm_star (c (seq i))]
    have w':=w i
    rw [← norm_star (c (seq i))] at w'
    exact add_le_add w' (u i)

 have g(i)(t:ℝ)(p:0<t):‖c (seq i)‖ * P.teeter x F (P.jetS (seq i)*t)≤
   (A+B)*D*spur a t:= by
    refine le_trans (mul_le_mul_of_nonneg_left (e i t p) (norm_nonneg (c (seq i)))) ?_
    rw [← mul_assoc, ← mul_assoc]
    have h0:0≤ spur a t:=by unfold YM.ZecaSky.spur;positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (h i) b.le) h0
 have y:0<(A+B)*D:=mul_pos (add_pos v r) b
 constructor
 · refine ⟨a,(A+B)*D,y,fun i t p=>le_trans ?_ (g i t p)⟩
   unfold kestrelSeed
   rw [norm_smul]
   exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg _)) (norm_nonneg _)
 · refine ⟨a,(A+B)*D,y,fun i t p=>le_trans ?_ (g i t p)⟩
   unfold kestrelSeed
   rw [norm_smul,Pi.star_apply,norm_star]
   exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg _)) (norm_nonneg _)
#print axioms sesqui
