import ZecaWrack
import ZecaNimbus
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


def startW : Plume_LocalFieldBounds :=
   ⟨0,fun _ => (P.roof:ℤ)+10,by change (0:ℤ) < (P.roof:ℤ)+10; positivity⟩
lemma goW:P.aboveRoof P.startW:=by
 unfold aboveRoof Plume_LocalFieldBounds.tar Plume_LocalFieldBounds.pose startW
 push_cast
 linarith

section
variable (F:P.Nib 3 (P.advocate 3 x 3))
 (c:ℕ→ℂ) (seq:ℕ→ℕ)

def skipping(t:ℝ):= ‖F t t ω‖
lemma skip_gait
  (l:P.MyJet x F)
  (h:P.Bottle 3 (P.advocate 3 x 3) F):
 Gait (P.skipping x F):=by
 obtain ⟨D,m,b,q⟩:=h.pay
 refine ⟨fun t p=> norm_pos_iff.mpr (l t t p p), ?_,
    D*(1+‖ω‖), m, by positivity,?_⟩
 · intro t u e d
   have k:=P.kestrel_scale (r:=1) x F 1 h t u e d
   unfold skipping
   simp only [kestrelSeed, Pi.one_apply,one_smul] at k
   rw [k]
   exact Hierarchy.Seld.stayPay _ _ _
 · intro t u w
   refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
   have v:=q t u w
   rw [mul_div_right_comm]
   exact mul_le_mul v (by linarith) (norm_nonneg _) (by positivity)

lemma gram_paid (T: P.Mach x F c seq) :
   ∃M₀:ℝ, 0<M₀ ∧ ∀i,‖c (seq i)‖*P.skipping x F (P.jetS (seq i)*P.startW.tar)≤ M₀:=by
 let e(i):=‖P.kestrel x F c P.startW (seq i)‖
 obtain ⟨B,t⟩:= fam_gramBound (T _ _ P.goW P.goW)
 obtain ⟨I,h⟩:=eventually_atTop.mp t
 have e0(i):0≤e i:= norm_nonneg _
 let b:=∑i ∈ Finset.range I,e i
 refine ⟨|B|+b+1,add_pos_of_nonneg_of_pos (add_nonneg (abs_nonneg _)
      (Finset.sum_nonneg (fun i _=>e0 i))) zero_lt_one,fun i=>?_⟩
 have bp:0≤b:= Finset.sum_nonneg (fun i _=>e0 i)
 have ht:e i ≤ |B|+b+1:=by
    rcases le_or_gt I i with q|q
    · exact (h _ q).trans (by linarith only [le_abs_self B,bp])
    refine le_trans (Finset.single_le_sum (f:=e) (fun i _=>e0 i) (Finset.mem_range.mpr q)) ?_
    change b≤|B|+b+1 -- small
    linarith [abs_nonneg B]
 unfold e kestrel kestrelRig kestrelSeed at ht
 rw [P.cart_norm,norm_smul] at ht
 exact ht

def Ebb :Prop:=
 ∃ (d:ℕ)(K:ℝ),0<K ∧ ∀ i t,0<t → 
    ‖P.kestrelSeed x F c (seq i) (P.jetS (seq i)*t)‖ ≤ K*spur d t

lemma ebb (q:P.Mach x F c seq)
 {a:ℕ}{D:ℝ}(b:0<D)
 (e:∀i t,0<t→
    P.skipping x F (P.jetS (seq i)*t) ≤
     P.skipping x F (P.jetS (seq i)*P.startW.tar) * D*spur a t):
 P.Ebb x F c seq:=by
 obtain ⟨M₀,v,w⟩:=P.gram_paid x F c seq q
 refine ⟨a,M₀*D,mul_pos v b,fun i t u=>?_⟩
 unfold kestrelSeed
 rw [norm_smul]
 refine le_trans (mul_le_mul_of_nonneg_left (e i t u) (norm_nonneg (c (seq i)))) ?_
 rw [← mul_assoc, ← mul_assoc]
 have h0:0≤ spur a t:=by unfold YM.ZecaSky.spur;positivity -- ≤s
 exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (w i) b.le) h0
#print axioms ebb
