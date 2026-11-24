import ZecaBenzene
import ZecaProng
import ZecaCeviche
import ZecaMirin
import ZecaSpindrift
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



open Hierarchy.Seld.Zeca
open Hierarchy.Seld (parabola)
open OS.Semigroup
open Boundary

local notation "Δr"=> P.jetS
variable (F:P.Nib 3 (P.advocate 3 x 3)) (sc:ℕ→ℂ)(seq:ℕ→ℕ)(d:Vantage)


variable (D:Hierarchy.Seld.Zeca.Moment (P.ManyF 3 (P.advocate 3 x 3)))

def Cider (r:ℕ)(t:ℝ) : G:=
 sc r • parabola Η D.n (duration t.toNNReal) (D.op ω)

def Calvados : ℕ→ℂ→ℂ:=fun i=>
 let r:=seq i
 oceanRun Η (P.Cider x sc D r) (poseSp 3 (Δr r • d)) (Δr r)
def Mimosa (T:ℝ)(W:ℝ→ℂ) :=fun i:ℕ=> 
 sandpiperI (P.Calvados x sc seq d D i) T W

variable (q:P.Truth 3 (P.advocate 3 x 3) F D)
include q

lemma cider_true(r:ℕ){t:ℝ}(p:0<t) :
 P.kestrelSeed x F sc r t=P.Cider x sc D r t:=by
 unfold kestrelSeed
 have y:=Real.toNNReal_pos.mpr p
 have j:=q.translation _ _ y y
 rw [Real.coe_toNNReal _ p.le] at j
 rw [j]
 exact congrArg (fun v:G=>sc r • v) (coinVac Η (P.nv 3 ξ) D (P.prepaid 3 ξ) _ _ y)

lemma cider_hot(i:ℕ)(T:ℝ)(W:ℝ→ℂ){y:ℝ}(p:0<y):
 shellI (P.Orange x F sc seq d i) T W y=
 shellI (P.Calvados x sc seq d D i) T W y:=by
 unfold shellI Orange Calvados
 apply integral_congr_ae
 refine Eventually.of_forall fun a=>?_
 simp only [oceanRun,tide_re,P.cider_true x F sc D q (seq i)
    (half_pos (mul_pos (P.jetS_pos _) p))]


variable (T:ℝ)(W:ℕ→ℝ→ℂ)

structure Breakwater(Q:ℕ→ℂ→ℂ)(T:ℝ)(W:ℕ→ℝ→ℂ)(d:Vantage):Prop where
 wick(i:ℕ):
   Tendsto (shellI (Q i) T (W 0)) (𝓝[>] 0) (𝓝 (sandpiperI (Q i) T (W 0)))
 spacelike:
   Tendsto (fun i=>sandpiperI (Q i) T (W 0)) atTop
      (𝓝 (shellI (Colada d) T (W 0) 0))

lemma amaro
 (p:P.Bottle 3 (P.advocate 3 x 3) F)(u:P.Mach x F sc seq)
 (v:P.Ebb x F sc seq)
 (e:d 3=0)(h:Pentadose d)
 (a:0<T)(b:T<heartscale d)
 (w:Temporal T W) :
 Breakwater (P.Calvados x sc seq d D) T W d :=by
 let Q:=P.Calvados x sc seq d D
 let A:=P.Orange x F sc seq d
 have g:P.Orange x F sc seq d=A:=rfl
 have s:=P.oranges_hot x F sc seq d p v
 have t:=P.oranges_splash x F sc seq d e h u
 have y(i:ℕ):
  Tendsto (shellI (Q i) T (W 0)) (𝓝[>] 0) (𝓝 (sandpiperI (A i) T (W 0))):=by
   refine (enters_jetty s a w i).congr' ?_
   filter_upwards [eventually_mem_nhdsWithin] with p k
   exact P.cider_hot x F sc seq d D q i T (W 0) k
 have r (i:ℕ) :sandpiperI (Q i) T (W 0)=sandpiperI (A i) T (W 0):=
    (y i).limUnder_eq
 refine ⟨fun i=>?_,?_⟩
 · rw [r];exact y i
 · change Tendsto (fun i=>sandpiperI (Q i) T (W 0)) _ _
   simp_rw [r]
   exact current_boundary s t a (salud_mix z' SU.group _ b) w
#print axioms amaro

omit q
lemma Pentadose.negative {d:Vantage} (a:Pentadose d):Pentadose (-d):=by
 obtain ⟨k,v,f⟩:=a
 exact ⟨k,-v,fun i=>by simp [f,neg_div]⟩

lemma cordialDiff
 (T:ℝ)(W:ℕ→ℝ→ℂ)(d:Vantage)(p:0<T){Q A:ℕ→ℂ→ℂ}
 (h:Breakwater Q T W d)
 (a:Breakwater A T (Tow W) (-d)):
 Tendsto (fun i=>sandpiperI (Q i) T (W 0) - sandpiperI (A i) T (Tow W 0))
    atTop (𝓝 0):=by
 have e:shellI (Colada (-d)) T (Tow W 0) 0=shellI (Colada d) T (W 0) 0:=
   salud_reverse z' SU.group _ p _
 have v:=h.spacelike.sub a.spacelike
 rwa [e,sub_self] at v

include q
theorem amaro_reverse
 (p:P.Bottle 3 (P.advocate 3 x 3) F)(u:P.Mach x F sc seq)
 (v:P.Ebb x F sc seq)
 (e:d 3=0)(h:Pentadose d)
 (a:0<T)(b:T<heartscale d)
 (w:Temporal T W) :
 Tendsto (fun i=> P.Mimosa x sc seq d D T (W 0) i -
    P.Mimosa x sc seq (-d) D T (Tow W 0) i) atTop (𝓝 0):=by
 exact cordialDiff T W d a (P.amaro x F sc seq d D q T W p u v e h a b w)
    (P.amaro x F sc seq (-d) D q T (Tow W) p u v
        (by simp [e]) h.negative a
        (show T < ‖-(WithLp.toLp 2 d:Gaia)‖ by rw [norm_neg];exact b)
        w.tow)
#print axioms amaro_reverse
