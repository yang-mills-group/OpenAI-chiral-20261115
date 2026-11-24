import Lucent.Coffer
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

open Spine Preparation.Yoke Lucent EmberWind
variable (P:Spine)
local notation "Ξ" => household (P.calibration)
local notation "φ" => P.groundZero 3
local notation "Kₚ" => P.calibration

open Ballad Arity Story
namespace Carillon
variable {a:ℝ}(e:0<a)

def behindM(L:ℕ)(M:ℕ)(x:Cover) (A:Finset Cover):Prop:=
     ∀ y∈ A,∀ i, |y i - M*x i| + (L:ℤ) ≤ (4:ℤ)*M
local notation "sheetB"=> basket P e
abbrev μcost (P:Spine)(a:ℝ)(s:ℕ):= pour (Arity.mosaic P.par a s)
local notation "H+" => μcost P a
structure Shelled(P:Spine){a:ℝ}(e:0<a)(k s:ℕ):Prop where
    heart : ∀i, behindM k (μcost P a s) (Story.points i) ((basket P e).extent s i)
    live : k+20 < μcost P a s

lemma stamps:∀ s,(sheetB |>.R s:ℝ)=μcost P a s:=fun _=>rfl

lemma shell_buys(k:ℕ): ∀ᶠ s in atTop, Shelled P e k s:=by
 have v:= (fit P.par e).gauge.eventually_gt_atTop (k+20:ℕ)
 filter_upwards [v] with s t
 have h: k+20 < μcost P a s:= by exact_mod_cast (show ((k+20:ℕ):ℝ)<μcost P a s from t)
 refine ⟨?_,h⟩
 intro i y z j; let D:=Story.points i
 let m:= μcost P a s
 have e:y∈skyDeck (nodeC (lime D (Arity.mosaic P.par a s))) (m+4+8):=z
 have g:(nodeC (lime D (Arity.mosaic P.par a s))) j= ↑m*D j +1:=by
   unfold nodeC lime; rw [smul_smul]
   change (μcost P a s • D j)+_ = _
   rw [nsmul_eq_mul]; rfl
 rw [pav_v] at e; specialize e j; rw [g] at e
 change |y j - ↑m*D j|+ (k:ℤ)≤ (4:ℤ)*m
 change _ < m at h
 rw [← le_sub_iff_add_le,abs_le]; omega
