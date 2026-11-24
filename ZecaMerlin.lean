import ZecaHarrier
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


-- We show recognition on ANY charged spot. 
def hawthorn (f r:ℕ) (p:Plume_LocalFieldBounds): P.Test:=
 (P.plumeK r:ℂ) • P.issuing r (P.basePlay x f r) (P.spacedPitch r p)
open PhaseChoice
/-- on THIS character, strict=false. actual actor in the ordinary j=3 Hilbert.
 Every issued support pays the full footprints in Q_− / strict positive halfspace. -/
structure Ledge (r:ℕ) (F:P.Test) (U:Set Vantage) (v:M) : Prop where
 stamp : ∃ h:P.birthF 3 r F,P.viewF 3 (P.advocate 3 x 3) r h = v
 corner : ∃ S, F ∈ bay P.calibration S true ∧ F ∈ enclave P.calibration ∧
                 SupportedPhysically Λ P.width r S U

local notation "B"=>P.basePlay x f r
variable (f)(p:Plume_LocalFieldBounds)(W₀:5∣P.par.R.L.val)
include W₀
/-- Any room which q sits in at unit radius roomy/K from p in UV. 
Only need sign constraints here. -/
lemma stamp_here :
 ∀ᶠ r:ℕ in atTop,∃ h:P.birthF 3 r (P.hawthorn x f r p),
    P.viewF 3 ξ r h=P.singer x f p r:=by
 filter_upwards [P.freed (f:=f) x p 0 W₀] with r h
 rw [add_zero] at h
 obtain ⟨a,g⟩:=P.beam_grid_pose_view 3 x (P.basePlay x f r) r _ h.le le_rfl
 unfold hawthorn
 refine ⟨P.birthScaleJ 3 r _ a,?_⟩
 rw [P.viewJ_scale _ _ _ _ a,g]
 rfl
omit W₀
lemma hawthorn_ledge
 {U:Set Vantage}
 (h:∃ d:P.birthF 3 r (P.hawthorn x f r p),P.viewF 3 ξ r d=P.singer x f p r)
 (u:P.Aperture (B) (P.meshPose r (P.spacedPitch r p)) ⊆ U):
 P.Ledge x r (P.hawthorn x f r p) U (P.singer x f p r):=by
 exact ⟨h,_,Subalgebra.smul_mem _ (P.issuing_support r (P.spacedPitch r p) (P.basePlay x f r)) _,
          Subalgebra.smul_mem _ (P.issuing_color r (P.spacedPitch r p) (P.basePlay x f r)) _,by
          intro i hi v hv
          let w:Vantage:=fun j=>v j/2
          have a : (2:ℝ) • w=v:=by funext y; change 2*(v y/2)=v y; ring
          exact u (P.inside_now r (P.spacedPitch r p) (P.basePlay x f r) le_rfl (show w∈P.pinFoot r
             (P.plotSet r (P.basePlay x f r) (P.spacedPitch r p)) from ⟨i,hi,a.symm ▸ hv⟩))⟩


abbrev sunstep:Set Vantage:= {y|0<y 3}
abbrev moonstep (b:Axis):Set Vantage:={y|0<y 3 ∧ y b <0}

include W₀

lemma hawth_sun :
 ∀ᶠ r:ℕ in atTop, P.Aperture (P.basePlay x f r) (P.meshPose r (P.spacedPitch r p)) ⊆ sunstep:=by
 filter_upwards [P.freed (f:=f) x p 0 W₀] with r v y h
 rw [add_zero] at v
 have q: -((P.basePlay x f r).realWidth P 3) ≤ y 3-P.meshPose r (P.spacedPitch r p) 3:= (abs_le.mp (h _)).1
 show 0<y 3; linarith only [v,q]
lemma hawth_moon {b:Axis} (t: p.pose b <0):
 ∀ᶠ r:ℕ in atTop, P.Aperture (P.basePlay x f r) (P.meshPose r (P.spacedPitch r p)) ⊆ moonstep b:=by
 have q:=Filter.Tendsto.const_mul_atTop (neg_pos.mpr t) P.planned_grows
 -- q works ? RHS ℝ...
 filter_upwards [P.hawth_sun f x p W₀,P.spaced_prepare W₀ p,
     q.eventually_gt_atTop (P.roomy:ℝ)] with r a v d y h
 have k:= (abs_le.mp (h b)).2
 rw [P.play_width,pose_w,v] at k
 refine ⟨a h,?_⟩
 linarith only [k,mul_lt_mul_of_pos_right d (P.macroStep_pos r)]

lemma occupies {b:Axis} :
 ∀ᶠ r:ℕ in atTop,
    P.Ledge x r (P.hawthorn x f r p) sunstep (P.singer x f p r) ∧
    (p.pose b<0 → P.Ledge x r (P.hawthorn x f r p) (moonstep b) (P.singer x f p r)):=by
 have h:∀ᶠ r:ℕ in atTop,p.pose b<0 →
    P.Aperture (P.basePlay x f r) (P.meshPose r (P.spacedPitch r p)) ⊆ moonstep b:=by
      by_cases z:p.pose b<0
      · exact (P.hawth_moon f x p W₀ z).mono fun _ t _=>t
      exact Eventually.of_forall fun _ h=>(z h).elim
 filter_upwards [h,P.hawth_sun f x p W₀,P.stamp_here f x p W₀] with r i j t
 exact ⟨P.hawthorn_ledge f x p t j,fun e=>P.hawthorn_ledge f x p t (i e)⟩
#print axioms occupies
