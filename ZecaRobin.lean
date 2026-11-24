import ZecaNepenthe
import SatinThinMill
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

/-- first. ℓ†, price. -/

abbrev petalsK(r:ℕ):= Aster P.run P.period P.cutoff r
def plumeK(r:ℕ):ℝ:= (P.jetR r)^4/(P.tallWorth r*P.petalsK r^2)

-- price. 3 convention.
def fly (f r:ℕ) (u:Cover) : M:=
 (P.plumeK r:ℂ) • P.beamGridRay 3 x (P.basePlay x f r) r u
local notation "B"=>P.basePlay x f r
local notation "Jk"=>P.plumeK r

lemma petal_floor(r:ℕ): (1/2:ℝ) ≤ P.petalsK r:= (astral P.run P.period P.cutoff r).1.1
lemma plume_pos:∀ᶠ r:ℕ in atTop,0<P.plumeK r:=by
 filter_upwards [P.reward_positive] with r hp
 exact div_pos (pow_pos (P.jetR_pos r) _) (mul_pos hp.1
    (pow_pos (show (0:ℝ)<_ from lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) (P.petal_floor r)) _))

open Next.Free Regis.Head.Brecht
private lemma reflected_chord(u v:Cover)
 (hu:(B).realWidth P 3≤ P.meshPose r u 3)(hv:(B).realWidth P 3 ≤ P.meshPose r v 3):
 inner ℂ (P.fly x f r u) (P.fly x f r v) =
 (Jk:ℂ)*((Jk:ℂ)*((P.tallWorth r:ℂ)^2*
 P.pulseQ 3 z' r ((P.granule (P.megaK f r))+ κ • v)
      (opposeQ 3 (P.granule (P.megaK f r)+κ • u)) x)):=by
 have h(m:Cover) : P.issuing r B m=P.centeredQ x r (P.granule (P.megaK f r)+κ • m):=
     (P.issuing_here ..).trans (P.chart_center ..)
 obtain ⟨d,w⟩:=P.beam_grid_pose_view 3 x B r u hu le_rfl
 obtain ⟨e,z⟩:=P.beam_grid_pose_view 3 x B r v hv le_rfl
 unfold fly; rw [inner_smul_left,inner_smul_right,Complex.conj_ofReal,←w,←z,P.released_gram,
   P.single_agrees,h u,h v,P.reflect_center,P.lens_price]
def lyric(p q:Plume_LocalFieldBounds):ℂ:=spectrumℓ z' SU.group (tendril p q)

private lemma fly_scalar {a t r:ℝ}(h:1/2≤a)(d:0<t)(X Y:ℂ):
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

abbrev finch (f:ℕ)(p:Plume_LocalFieldBounds)(a:Cover)(r:ℕ):M:=P.fly x f r (P.spacedPitch r p+a)

variable (p q:Plume_LocalFieldBounds)(a b:Cover)(W₀:5∣P.par.R.L.val)

include W₀
lemma freed : ∀ᶠ r:ℕ in atTop, (P.basePlay x f r).realWidth P 3 < P.meshPose r (P.spacedPitch r p+a) 3:=by
 have h:=Filter.Tendsto.const_mul_atTop p.hot P.planned_grows
 filter_upwards [P.spaced_prepare W₀ p,h.eventually_gt_atTop ((P.roomy:ℝ)-a 3)] with r q v
 rw [P.play_width,P.pose_w]; apply mul_lt_mul_of_pos_right _ (P.macroStep_pos _)
 rw [Pi.add_apply,Int.cast_add,q]
 exact sub_lt_iff_lt_add.mp v

lemma freed_cost : ∀ᶠ r:ℕ in atTop,
  ‖inner ℂ (P.finch x f p a r) (P.finch x f q b r)-lyric p q‖≤16*P.bendMiss f p q a b r x:=by
 filter_upwards [P.freed (f:=f) x p a W₀, P.freed (f:=f) x q b W₀,
    P.reward_positive] with r h d t
 unfold finch
 rw [P.reflected_chord x _ _ h.le d.le]
 exact fly_scalar (P.petal_floor r) t.1 _ _
variable {seq:ℕ→ℕ}(T:P.Nepenthe seq x)
include T
lemma freed_gram : Tendsto (fun i=> inner ℂ (P.finch x f p a (seq i)) (P.finch x f q b (seq i))) atTop (𝓝 (lyric p q)):=by
 have h:=(T.poses f p q a b).const_mul 16
 rw [mul_zero] at h
 refine Metric.tendsto_nhds.mpr fun e d=>?_
 filter_upwards [h.eventually (gt_mem_nhds d),T.sky.eventually (P.freed_cost (f:=f) x p q a b W₀)]
      with i v h
 rw [dist_eq_norm]; exact h.trans_lt v
