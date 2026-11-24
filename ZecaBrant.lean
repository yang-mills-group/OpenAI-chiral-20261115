import ZecaBitters
import ZecaMilkweed
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


structure Umber(seq:ℕ→ℕ) :Prop where
 sky:Tendsto seq atTop atTop
 poses:∀ f a b p q,Tendsto (fun i=>P.carbbendMiss f a b p q 0 0 (seq i) x) atTop (𝓝 0)

variable (f)(r)(a b:Bool)
def canary(a:Bool):P.Apron:= if a then (P.basePlay x f r).kiss P 3 else P.basePlay x f r
-- f and r notation order? #check.
#check P.canary
local notation "D"=>P.canary (r:=r) (f:=f) x
lemma canary_s : (D a).s=r:=by unfold canary;split <;>rfl
lemma canary_w :
 (D a).realWidth P 3=(P.basePlay x f r).realWidth P 3:=by unfold canary;split<;>rfl
lemma canary_F: (D a).F=P.centeredQ x r (P.thyme a r f):=by
 unfold canary thyme
 by_cases h:a=true
 · rw [if_pos h, if_pos h]
   exact P.reflect_center ..
 rw [if_neg h,if_neg h]
 rfl
lemma canary_issue(u:Cover):
 P.issuing r (D a) u=P.centeredQ x r (P.thyme a r f+κ • u):=by
 have e:=P.issuing_here (D a) u
 rw [canary_s, canary_F,P.chart_center] at e
 exact e
def grackle(a:Bool)(u:Cover) : M:=
 (P.plumeK r:ℂ) • P.beamGridRay 3 x (D a) r u
local notation "E"=> P.grackle (f:=f) (r:=r) x
local notation "Jk"=>P.plumeK r
#check canary_issue

lemma grackle_gram(u v:Cover)
 (hu:(P.basePlay x f r).realWidth P 3≤ P.meshPose r u 3)(hv:(P.basePlay x f r).realWidth P 3 ≤ P.meshPose r v 3):
 inner ℂ (E a u) (E b v) =
 (Jk:ℂ)*((Jk:ℂ)*((P.tallWorth r:ℂ)^2*
 P.pulseQ 3 z' r (P.thyme b r f+ κ • v)
      (opposeQ 3 (P.thyme a r f+κ • u)) x)):=by
 obtain ⟨d,w⟩:=P.beam_grid_pose_view 3 x (D a) r u
   (le_trans (canary_w P (f:=f) (r:=r) x a).le hu) ((canary_s P (f:=f) (r:=r) x a).le)
 obtain ⟨e,z⟩:=P.beam_grid_pose_view 3 x (D b) r v
   (le_trans (canary_w P (f:=f) (r:=r) x b).le hv) ((canary_s P (f:=f) (r:=r) x b).le)
 unfold grackle
 rw [inner_smul_left,inner_smul_right,Complex.conj_ofReal,←w,←z,P.released_gram,
   P.single_agrees,canary_issue,canary_issue,P.reflect_center,P.lens_price]
private lemma carbonateX {a t r:ℝ}(h:1/2≤a)(d:0<t)(X Y:ℂ):
 let k:=r^4/(t*a^2)
 ‖(k:ℂ)*((k:ℂ)*((t:ℂ)^2*X)) - Y‖≤ 16* ‖(r:ℂ)^8*X - (a:ℂ)^4 * Y‖:=by
 dsimp only
 have ha:0<a:=by linarith
 have ha4:0<a^4:=by positivity
 let b:ℝ:= (a^4)⁻¹
 have hb:0<b:=by unfold b; positivity
 have hu:b≤16:=by
   unfold b; rw [inv_le_iff_one_le_mul₀ ha4]
   linarith only [pow_le_pow_left₀ (show 0≤ (1/2:ℝ) by norm_num) h 4]
 have he:
    (↑(r^4/(t*a^2)):ℂ) * ((↑(r^4/(t*a^2)):ℂ) * ((t:ℂ)^2 * X)) - Y=
       (b:ℂ)* ((r:ℂ)^8*X-(a:ℂ)^4*Y):=by
   have hd:(a:ℂ)≠0:=by exact_mod_cast ha.ne'
   have he:(t:ℂ)≠0:=by exact_mod_cast d.ne'
   unfold b; push_cast; field_simp
 rw [he,norm_mul,Complex.norm_real,Real.norm_of_nonneg hb.le]
 gcongr


variable {r} (p:Plume_LocalFieldBounds)(W₀:5∣P.par.R.L.val)
def pod (a:Bool)(r:ℕ):=P.grackle f r x a (P.spacedPitch r p+0)
include W₀
lemma brant_d : ∀ᶠ r:ℕ in atTop,
  ‖inner ℂ (P.pod f x p a r) (P.pod f x p b r)-lyric p p‖≤16*P.carbbendMiss f a b p p 0 0 r x:=by
 filter_upwards [P.freed (f:=f) x p 0 W₀,P.reward_positive] with r h t
 unfold pod
 rw [P.grackle_gram f r x a b _ _ h.le h.le]
 exact carbonateX (P.petal_floor r) t.1 _ _
variable {seq:ℕ→ℕ}(e:P.Umber x seq)
include e
lemma brant_go :
 Tendsto (fun i=>inner ℂ (P.pod f x p a (seq i)) (P.pod f x p b (seq i))) atTop (𝓝 (lyric p p)):=by
 have h:=(e.poses f a b p p).const_mul 16
 rw [mul_zero] at h
 refine Metric.tendsto_nhds.mpr fun t d=>?_
 filter_upwards [h.eventually (gt_mem_nhds d),e.sky.eventually (P.brant_d f x a b p W₀)]
      with i v h
 rw [dist_eq_norm]; exact h.trans_lt v
#print axioms brant_go
#check @pod
#check @grackle
