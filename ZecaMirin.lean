import ZecaWasabi
import ZecaIbis
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

def sidelock(δ E q:ℝ) (d:Vantage) :=
 Off δ E (heartscale d*q) (WithLp.toLp 2 d)
local notation "Δr"=> P.jetS
local notation "Q₃"=> (P.seasons 3 ξ).ℚmeasure

lemma tap_g(d:Vantage) (r:ℕ) (q E:ℝ)(p:d 3=0) (a:0<q):
 Bask (heartscale d) q E (P.commRun x d r) (P.commRise x r)
  (fun v=>‖(Q₃).region (sidelock (P.jetS r) E q d) v‖):=by
 have i:=Off_bask (E:=E) (d:=WithLp.toLp 2 d) Η (P.jetS_pos r).le
     (show 0≤heartscale d*q from mul_nonneg (norm_nonneg _) a.le)
 unfold commRun;rw [P.cart_m]
 have e:(poseSp 3 ((Δr r) • d)).val = (Δr r) • WithLp.toLp 2 d:=by
    let z:=poseSp 3 ((Δr r) • d)
    ext j;by_cases y:j=3
    · subst j
      rw [show (poseSp ..).val 3=0 from z.property]
      simp [p]
    change z.val j=(Δr r)*d j
    exact transverse_eyes 3 (fun i:Trans 3=>((Δr r)•d) i.val) ⟨j,y⟩
 rw [e];exact i

variable (F:P.Nib 3 (P.advocate 3 x 3)) (sc:ℕ→ℂ)
    (Z:Hierarchy.Seld.Zeca.Moment (P.ManyF 3 (P.advocate 3 x 3)))

lemma pelicanFull(r:ℕ)(p:Vantage) (a:0<p 3)
 (e:P.Truth 3 (P.advocate 3 x 3) F Z):
   P.pelican x F sc p r=
   (Η).U (poseSp 3 (Δr r • p))
      (sc r • parabola Η Z.n (duration (P.jetS r*p 3).toNNReal) (Z.op ω)):=by
 unfold pelican; rw [P.uses_cart]
 refine congrArg ((Η).U (poseSp 3 _)) ?_
 unfold kestrelSeed
 have u:=mul_pos (P.jetS_pos r) a
 have y:=Real.toNNReal_pos.mpr u
 have j:=e.translation _ _ y y
 rw [Real.coe_toNNReal _ u.le] at j
 rw [j]
 exact congrArg (fun v:G=>sc r • v) (coinVac Η (P.nv 3 ξ) Z (P.prepaid 3 ξ) _ _ y)
#check Test4

theorem mirin (seq:ℕ→ℕ)(p d:Vantage)
 (t:0<p 3)(e:d 3=0)
 (w:P.RV x F sc seq p d)
 (o:P.Truth 3 (P.advocate 3 x 3) F Z)
 {E q η:ℝ}(a:0≤E)(l:E<q)(u:0<η):
   ∀ᶠ i:ℕ in atTop, ∀f:Test4,
    ‖(Q₃).region (sidelock (P.jetS (seq i)) E q d)
      (sc (seq i) • (Z.field Η f (P.nv 3 ξ)).val)‖≤ η * ∫y,‖f y‖ :=by
 filter_upwards [w E q a l (η * Real.exp (-(p 3*E))) (by positivity)] with i g f
 refine wasabi Η (P.nv 3 ξ) Z (P.prepaid 3 ξ) (P.nova 3 ξ)
    f (P.jetS_pos _) t (y:=poseSp 3 (P.jetS (seq i) • p)) ?_
 erw [←P.pelicanFull x F sc Z (seq i) p t o]
 exact (g _ (P.tap_g x d _ q E e (a.trans_lt l))).le
#print axioms Spine.mirin
