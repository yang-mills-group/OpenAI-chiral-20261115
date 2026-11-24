import ZecaRobin
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




-- exact H ↔ G pair costs through strict Plenum. mixed x – advocates.
local notation "B"=>P.basePlay x f r
local notation "d"j:max=>Apron.realWidth P B j
local notation "Y"=>P.meshPose r
local notation "θ" => opposeR 3
section
variable (y z:Cover)
 (p:(P.basePlay x f r).realWidth P 3 < P.meshPose r y 3)(q:(P.basePlay x f r).realWidth P 3 < P.meshPose r z 3)
 (Q₀:∀ j, opposeR 3 (P.meshPose r y) j+(P.basePlay x f r).realWidth P j<P.meshPose r z j-(P.basePlay x f r).realWidth P j)

local notation "T"H:max=> P.beamGridRay 3 x B r H
local notation "U"v:max=> P.thinRay x B (P.base_birth x f r) (Y v)

include p
private lemma priced_beak :
 π (T y)= U y:=by
 let Z:=P.thinGridRay x r B (P.base_birth x f r) y
 have hx:π Z= U y:=by
   unfold Z thinGridRay thinRay; rw [P.commit_move]
   apply congrArg (Γ _); exact P.bankHeat ..
 obtain ⟨u,h⟩:=P.beam_grid_pose_view 3 x B r y p.le le_rfl
 obtain ⟨u',h'⟩:=P.thin_grid_pose_view x r B (P.base_birth x f r) y p le_rfl
 have e:T y=Z:=h.symm.trans h'
 rw [e,hx]

include q Q₀
lemma feather_grid (J:P.Ellis 3 x):
 inner ℂ (π (T y)) (π (T z))=inner ℂ (T y) (T z):=by
 obtain ⟨u,h⟩:=P.beam_grid_pose_view 3 x B r y p.le le_rfl
 obtain ⟨w,t⟩:=P.beam_grid_pose_view 3 x B r z q.le le_rfl
 have he:inner ℂ (T y) (T z)=P.singleState 3 r x (P.issuing r ((B).kiss P 3) (opposeQ 3 y)*P.issuing r B z):=by
    rw [←h,←t,P.released_gram,P.single_agrees,P.issue_reflect]
 rw [he,P.priced_beak x y p,P.priced_beak x z q]
 let L:=[false,true]
 let A:=usher ((B).kiss P 3) B
 let a:=usher (opposeQ 3 y) z
 let D:=usher (θ (Y y)) (Y z)
 have hx:P.gridSpot r ∘ a=D:=by funext i; cases i with |false=>exact P.tile_reflect r y 3|true=>rfl
 have hT(t:Axis):P.Turnstile t A L D:= List.pairwise_pair.mpr (Q₀ t)
 have hu:P.Plenum A L D:=⟨fun t=> ⟨_,List.Perm.refl _,hT t⟩⟩
 have g:=P.spot_full x A L a J r (fun b _=>by cases b <;> exact le_refl r)
   (hx.symm ▸ hT 3) (hx.symm ▸ hu)
 have ht:θ (Y y) 3+(d 3)<0:=by rw [show θ (Y y) 3 = -Y y 3 from if_pos rfl]; linarith only [p]
 have hb:P.commonWell 3 x A D L=inner ℂ (U y) (U z):=by
    have e:=P.thin_pair_well_price x B (P.base_birth x f r)
        B (P.base_birth x f r) (θ (Y y)) (Y z) ht q J
    rw [show θ (θ (Y y))= Y y from reflectPose_twice ..] at e
    exact e
 rw [hx,hb,show P.fullScroll r A a L=P.issuing r ((B).kiss P 3) (opposeQ 3 y)*P.issuing r B z from by
        change _*(_* (1:P.Test))=_; rw [mul_one]; rfl] at g
 exact g.symm
end
variable (p:Plume_LocalFieldBounds)(W₀:5∣P.par.R.L.val)
include W₀
lemma copy_spacing : ∀ᶠ r:ℕ in atTop,∀ j:Axis,
 θ (P.meshPose r (P.spacedPitch r p+0)) j +P.roomy*P.macroStep r<
 P.meshPose r (P.spacedPitch r p+(fun _=>(P.charmF:ℤ))) j-P.roomy*P.macroStep r:=by
 -- chooses positive time too
 let a:Cover:= fun _=> (P.charmF:ℤ)
 have h:=Filter.Tendsto.const_mul_atTop p.hot P.planned_grows
 filter_upwards [P.spaced_prepare W₀ p,h.eventually_ge_atTop 0] with r v w k
 let Y' := P.spacedPitch r p
 let m := P.macroStep r
 let z :ℝ:=P.roomy
 rw [pose_w,Pi.add_apply,add_zero Y',Int.cast_add]
 have hx: (↑(a k):ℝ)=z+z+1:=by change (↑(↑P.charmF:ℤ):ℝ)=_; rw [Int.cast_natCast,charmF,Nat.cast_succ,Nat.cast_add]
 rw [hx]
 let r₀:ℝ:=Y' k
 have hm:0 < m:=P.macroStep_pos r
 have hv:P.meshPose r Y' k=r₀*m:=rfl
 have hj:θ (P.meshPose r Y') k ≤ r₀*m:=by
    unfold opposeR mirrorΩ
    by_cases t:k=3
    · subst k
      have h0:0≤r₀:=w.trans_eq (v 3).symm
      rw [if_pos rfl,hv]; exact neg_le_self (mul_nonneg h0 hm.le)
    rw [if_neg t,hv]
 change _ + z*m < (r₀+_)*m-z*m
 linarith only [hj,hm]

variable (J:P.Ellis 3 x)
include J
lemma freed_clone : ∀ᶠ r:ℕ in atTop,
 inner ℂ (π (P.finch x f p 0 r)) (π (P.finch x f p (fun _=> (P.charmF:ℤ)) r))=
 inner ℂ (P.finch x f p 0 r) (P.finch x f p (fun _=> (P.charmF:ℤ)) r):=by
 let a:Cover:= fun _=>P.charmF
 filter_upwards [P.freed (f:=f) x p 0 W₀,P.freed (f:=f) x p a W₀, P.copy_spacing p W₀] with r h q j
 unfold finch fly
 rw [map_smul,map_smul,inner_smul_left,inner_smul_right,inner_smul_left,inner_smul_right,
       P.feather_grid x _ _ h q (by intro k; rw [P.play_width]; exact j k) J]
#print axioms Spine.freed_clone
