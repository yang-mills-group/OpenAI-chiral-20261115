import YM.SU5.MacroSix.TestDensity
import YM.SU5.MacroSix.ElectedQuadrature

/-! # The macroscopic response, limit proof

Here the pose variables are *independent*, not a shared vector translate. A simple
sufficient condition is a real separating wall between all time (3rd-axis) supports,
including both body widths. Gracefully handles lack of spatial clearance, no point-wise
price postulate in this condition.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2600
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Aria
open _root_.YM.MacroSix (independently SmoothDensity total finiteTest weightKernel compact_weight)

namespace Spine
variable (P : Spine) (s n t : ℕ) (Z Z' : Window.Family) (f g : Vantage → ℝ) (c : ℝ)
  (x : P.Spectrum0 3)
local notation "β" => P.otherSpectrum 3 3 x
local notation "S" => P.seasons 3 β
local notation "G" => P.ManyF 3 β
local notation "S'" => P.physicalEnergy 3 β
local notation "H" => P.ColorHil 3 β
local notation "T" => (S).E
local notation "T'" => (S').E
local notation "κ" => P.enter 3 β
local notation "U" => P.cartage 3 β
local notation "U'" => P.truck 3 β
local notation "τ" r:max => Real.toNNReal r
local notation "W" => ((P.sixWidth s n 3):ℝ)
local notation "D" i:max => P.sixBody s n i
local notation "B" i:max => (P.sixBody s n i).kiss P 3
local notation "V" i:max => P.darkField s n i x
local notation "Δ" i:max => P.openField s n i x

structure OnFrame : Prop where
  before : ∀ y ∈ tsupport f, y 3 + (P.sixWidth s n 3:ℝ) < c
  after : ∀ z ∈ tsupport g, c < z 3 - (P.sixWidth s n 3:ℝ)

def timeWeight (y : Vantage) (r : Bool) : ℝ≥0 := Real.toNNReal
  (if r then y 3-c else c-y 3)

lemma timeWeight_cont (r : Bool) : Continuous (fun y ↦ timeWeight c y r) := by
  cases r <;>
    first | exact continuous_real_toNNReal.comp ((continuous_apply _).sub continuous_const) |
      exact continuous_real_toNNReal.comp (continuous_const.sub (continuous_apply _))

def frameLight (r : Bool) (y : Vantage) : G := U y (T (timeWeight c y r) (V Z))
def originLight (r : Bool) (y : Vantage) : H := T' (timeWeight c y r) (Δ Z)
def darkSmear (r : Bool) : G := total G volume (fun y ↦ (f y:ℂ) • P.frameLight s n Z c x r y)
def nativeLight (r : Bool) (y : Cover) : H := U' (P.vtile t y) (P.originLight s n Z c x r (P.pose t y))

def weighLight (r : Bool) : H := finiteTest (f ∘ P.pose t) ((P.meshSize t)^4)
  (P.nativeLight s n t Z c x r)

lemma frameLight_cont (r : Bool) : Continuous (P.frameLight s n Z c x r) :=
  P.caravan 3 β _ _ continuous_id (((S).continuousE (V Z)).comp (timeWeight_cont c r))

lemma originLight_cont (r : Bool) : Continuous (P.originLight s n Z c x r) :=
  ((S').continuousE (Δ Z)).comp (timeWeight_cont c r)

lemma light_weight_eq (r : Bool) (y : Vantage) :
    U y (P.wealth 3 β ((f y:ℂ) • P.originLight s n Z c x r y)) =
      (f y:ℂ) • P.frameLight s n Z c x r y := by
  let q := timeWeight c y r
  let d := T q
  let m := P.wealth 3 β
  have he : m (P.originLight s n Z c x r y)=d (V Z) :=
    (P.bankHeat 3 β q (Δ Z)).trans (congrArg d (P.darkField_selected s n Z x))
  let l := U y
  let a : ℂ := f y
  exact (congrArg l ((map_smul m a _).trans (congrArg (fun b : G ↦ a • b) he))).trans
    (map_smul l a (d (V Z)))

lemma nativeLight_weight_eq (r : Bool) :
    P.vectorSum x (fun y ↦ (f y:ℂ) • P.originLight s n Z c x r y) t = P.weighLight s n t Z f c x r := by
  let d (y : Cover) := P.nativeLight s n t Z c x r y
  let X := ((P.meshSize t:ℝ)^4:ℝ)
  have he (y : Cover) : U' (P.vtile t y) ((f (P.pose t y):ℂ) • P.originLight s n Z c x r (P.pose t y)) =
      (f (P.pose t y):ℂ) • d y := map_smul (U' (P.vtile t y)) _ _
  unfold vectorSum
  simp_rw [he]; exact congrArg (fun z : ℂ ↦ z • ∑ᶠ k, (f (P.pose t k):ℂ) • d k) (Complex.ofReal_pow ..).symm

lemma frameLight_limit (p : Continuous f) (u : HasCompactSupport f) (r : Bool) (J : P.Ellis 3 x) :
    Tendsto (fun t : ℕ ↦ P.weighLight s n t Z f c x r) atTop
      (𝓝 (κ (P.darkSmear s n Z f c x r))) := by
  let D' (y : Vantage) := (f y:ℂ) • P.originLight s n Z c x r y
  have hp := (Complex.continuous_ofReal.comp p).smul (P.originLight_cont s n Z c x r)
  let F' (y : Vantage) := U y (P.wealth 3 β (D' y))
  have ht : Tendsto (fun i : ℕ ↦ P.vectorSum x D' i) atTop (𝓝 (κ (total G volume F'))) :=
    P.vectorLimit x J D' hp (compact_weight _ u _)
  have he : F' = (fun y ↦ (f y:ℂ) • P.frameLight s n Z c x r y) :=
    funext (P.light_weight_eq s n Z f c x r)
  have he' : κ (total G volume F') = κ (P.darkSmear s n Z f c x r) :=
    congrArg (fun F' ↦ κ (total G volume F')) he
  let y (t : ℕ) := P.weighLight s n t Z f c x r
  have hv : Tendsto y atTop (𝓝 (κ (total G volume F'))) := ht.congr
    fun i ↦ P.nativeLight_weight_eq s n i Z f c x r
  -- avoid tactic matching deep dependent local notation
  exact Eq.mp (congrArg (fun z : H ↦ Tendsto y atTop (𝓝 z)) he') hv

/-- Macroscopic kernel answer. This uses the *actual commonWell* and below is proved to be
the finer and finer signed-state reading with our smearing prescription. First body opposed
(mark, not just matrix transpose); pose y unreflected in this notation. -/
def measureField : Matrix Window.Family Window.Family ℂ :=
  Matrix.of fun Z Z' ↦ independently (fun y z ↦ P.fieldKernel s n x y z Z Z') f g

/-- At height t, advance and smear, Eq `(As)` with the same mesh granule normalization. -/
def smearField (A : P.Apron) : P.Test :=
  finiteTest (f ∘ P.pose t) ((P.meshSize t)^4) (P.fieldAt t A)

/-- The actual measurement at height t using independent products.
At qualifying locations (both ask supports) including all later refinements. -/
def measureAt : Matrix Window.Family Window.Family ℂ := Matrix.of fun Z Z' ↦
  P.singleState 3 t x (P.smearField t f ((P.sixBody s n Z).kiss P 3) *
    P.smearField t g (P.sixBody s n Z'))

local notation "K" y:max z:max => P.fieldKernel s n x y z

-- Time frame enforces strict order including closures of supports. (Footprints charged
-- to positive radius on *both* fields.)
lemma OnFrame.factors {P : Spine} {s n f g c} (e : P.OnFrame s n f g c) {y z}
    (h : y ∈ tsupport f) (q : z ∈ tsupport g) :
    P.fieldOrder s n 3 y z ∧ y 3 ≤ c ∧ c ≤ z 3 := by
  have hp := e.before _ h
  have hh := e.after _ q
  have hw : 0 ≤ ((P.sixWidth s n 3):ℝ) := (P.sixWidth s n 3).property
  exact ⟨hp.trans hh,by linarith,by linarith⟩

lemma measureField_integral (p : Continuous f) (q : HasCompactSupport f)
    (p' : Continuous g) (q' : HasCompactSupport g)
    (J : P.Ellis 3 x) (e : P.OnFrame s n f g c) :
    Integrable (weightKernel (fun y z ↦ (K y z) Z Z') f g) ∧
      P.measureField s n f g x Z Z'= inner ℂ (P.darkSmear s n Z f c x false)
        (P.darkSmear s n Z' g c x true) := by
  let F := P.frameLight s n Z c x false
  let F' := P.frameLight s n Z' c x true
  let k (y z : Vantage) := (K y z) Z Z'
  have hk (y : Vantage) (h : y ∈ Function.support f) (z : Vantage) (q : z ∈ Function.support g) :
      k y z=inner ℂ (F y) (F' z) :=
    let a := e.factors (subset_tsupport _ h) (subset_tsupport _ q)
    P.fieldKernel_factors s n Z Z' x J y z a.1 c a.2.1 a.2.2
  exact MacroSix.weighted_pair G (fun y ↦ (f y:ℂ) • F y) (fun y ↦ (g y:ℂ) • F' y) k f g
    (fun y ↦ MacroSix.weights G k f g F F' hk y.1 y.2)
    ((Complex.continuous_ofReal.comp p).smul (P.frameLight_cont s n Z c x false))
    (compact_weight f q F)
    ((Complex.continuous_ofReal.comp p').smul (P.frameLight_cont s n Z' c x true))
    (compact_weight g q' F')

lemma weigh_equals (h : HasCompactSupport f) (q : HasCompactSupport g) (hs : s ≤ t)
    (e : P.OnFrame s n f g c) :
    P.measureAt s n t f g x Z Z' = inner ℂ (P.weighLight s n t Z f c x false)
      (P.weighLight s n t Z' g c x true) := by
  let p := P.pose t
  let a := P.nativeLight s n t Z c x false
  let b := P.nativeLight s n t Z' c x true
  let Y := P.fieldAt t (B Z)
  let W' := P.fieldAt t (D Z')
  have he (i : Cover) (u : i ∈ Function.support (f ∘ p)) (j : Cover)
      (w : j ∈ Function.support (g ∘ p)) :
      P.singleState 3 t x (Y i * W' j)=inner ℂ (a i) (b j) :=
    let v := e.factors (subset_tsupport f (show f (p i) ≠ 0 from u))
      (subset_tsupport g (show g (p j) ≠ 0 from w))
    P.nativeKernel_factors s n t Z Z' x hs i j v.1 c v.2.1 v.2.2
  exact MacroSix.finiteTest_compare H (f ∘ p) (g ∘ p) _ Y W' (P.singleState 3 t x)
    (P.gridCosts_finite t ℝ f h) (P.gridCosts_finite t ℝ g q) a b he

/-- Macro-order conclusion needed for both of the six-clan tests. Works at fixed `s n`
even without ordering in spatial projections! -/
theorem measure_tends (p : Continuous f) (q : HasCompactSupport f)
    (p' : Continuous g) (q' : HasCompactSupport g)
    (J : P.Ellis 3 x) (e : P.OnFrame s n f g c) :
    Tendsto (fun t ↦ P.measureAt s n t f g x Z Z') atTop (𝓝 (P.measureField s n f g x Z Z')) := by
  let y := P.darkSmear s n Z f c x false
  let z := P.darkSmear s n Z' g c x true
  let A (i : ℕ) := P.measureAt s n i f g x Z Z'
  have he : Tendsto A atTop (𝓝 (inner ℂ (κ y) (κ z))) :=
    ((P.frameLight_limit s n Z f c x p q false J).inner
      (P.frameLight_limit s n Z' g c x p' q' true J)).congr'
      ((eventually_ge_atTop s).mono fun i h ↦ (P.weigh_equals s n i Z Z' f g c x q q' h e).symm)
  have hh := ((κ).inner_map_map y z).trans
    (P.measureField_integral s n Z Z' f g c x p q p' q' J e).2.symm
  exact Eq.mp (congrArg (fun z ↦ Tendsto A atTop (𝓝 z)) hh) he

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.measure_tends
