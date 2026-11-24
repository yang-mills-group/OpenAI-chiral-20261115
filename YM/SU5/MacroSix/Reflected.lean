import YM.SU5.MacroSix.Receipt
import YM.SU5.MacroSix.Zoom
import YM.SU5.Voyager.Canyon
import YM.SU5.MacroSix.OctantPay

/-!
# t:trans6 (i) strict macroscopic Gram grant

Measured on the same normalized signed state. Compare even after projecting onto
`V_i`. Part (ii) will need no spectral projection on the final (not Gram) measurements.
The argument is for *any* positive-size admissible starting ball in the indicated
momentum cone/octant, indeed any open set satisfying those hypotheses. No bounded
frequency assumption on the full measure! Weakening `t:trans6`'s window hypotheses.
No lower bound uniform in i at this macroscopic smearing step (that's different from
`sixGrant` on the zoom).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2200
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Aria
open _root_.YM.MacroSix _root_.YM.MacroSix.ClockTest Spectral Caino Spectral.Orbit.Prairie
open Set

namespace Spine
variable (P : Spine) (s n : ℕ) (Z : Window.Family) (f : Full → ℝ)
    (u : ClockTest.Space → ℝ) (g : ℝ → ℝ) (x : P.Spectrum0 3)
local notation "β" => P.otherSpectrum 3 3 x
local notation "S" => P.seasons 3 β
local notation "G" => P.ManyF 3 β
local notation "T" => P.travelTime s n
local notation "wTh" => ((P.sixWidth s n 3):ℝ)
local notation "Q" => (S).ℚmeasure
local notation "ρ" => P.dew s n
local notation "η" => f ∘ mirrorΩ 3
local notation "original" i:max => P.birthCloud x i s n
local notation "K" i:max => P.darkSmear s n i f 0 x true

lemma clocks_reflected (p : ∀ x ∈ tsupport f, wTh < x 3) : P.OnFrame s n (η) f 0 := by
  refine ⟨fun y h ↦ ?_, fun y h ↦ sub_pos.mpr (p y h)⟩
  rw [throughMirror] at h; have hp : wTh < -(y 3) := by
    have hx := p _ h; exact lt_of_lt_of_eq hx (show mirrorΩ 3 y 3=-(y 3) from if_pos rfl)
  linarith

def TimeFare : Prop := ∀ x ∈ tsupport g, (P.sixWidth s n 3:ℝ) < x

lemma calendarFrame (h : P.TimeFare s n g) : P.OnFrame s n (ClockTest.joined u g ∘ mirrorΩ 3) (ClockTest.joined u g) 0 :=
  P.clocks_reflected s n _ (fun x v ↦ h (ClockTest.clock x) (joined_support u g x v).1)

/-- No assumption on spectral support of the smearing; exact integral vector with
unprojected-in-spectrum base state. Verified zero-*time*-energy removal. -/
lemma pulseDark_reach : K Z = reachVector S T f (original Z) := by
  have he (x : Full) : transverse 3 (fun j ↦ x j.val)= bankOf x := by
    apply Subtype.ext
    refine Mink.ext_by ?_ (by
      change YM.time (transverse 3 _).val=YM.time (bankOf x).val
      exact Eq.trans ((transverse 3 _).property) (bankOf x).property.symm)
    change YM.spatial _ = YM.spatial (bankOf x).val
    rw [show YM.spatial (bankOf x).val = WithLp.toLp 2 (ClockTest.trans x) from spatial_position ..]
    ext i
    exact transverse_eyes (3:Axis) (fun j ↦ x j.val) (⟨i.castSucc, Fin.castSucc_ne_last _⟩:Trans (3:Axis))
  let r := T
  let y := original Z
  let F := P.frameLight s n Z 0 x true
  have hT (v : Vantage) : timeWeight 0 v true=(ClockTest.clock v).toNNReal := by
    unfold timeWeight; rw [if_pos rfl,sub_zero]; rfl
  have hw (z : Full) : P.cartage 3 β z=(S).U (bankOf z) :=
    (P.uses_cart 3 β z).trans (congrArg (S).U (he z))
  have hq (z : Full) : (f z:ℂ) • F z=travelVector S r f y z := by
    exact congrArg₂ (fun (k : (G).Op) (t : ℝ≥0) ↦ (f z:ℂ) • k ((S).E t (P.darkField s n Z x))) (hw z) (hT z)
  exact congrArg (total G volume) (funext hq)

lemma reflected_dark_eq : P.darkSmear s n Z (η) 0 x false = K Z := by
  let R := mirrorΩ 3 (A:=ℝ)
  let G' := P.frameLight s n Z 0 x
  let A (i : Vantage) := (f i:ℂ) • G' true i
  let B (i : Vantage) := (f (R i):ℂ) • G' false i
  have h (i : Vantage) : timeWeight 0 (R i) true=timeWeight 0 i false := by
    unfold timeWeight; simp [R,mirrorΩ]
  have he (i : Vantage) : G' true (R i)=G' false i := by
    let v := P.darkField s n Z x
    exact (congrArg₂ (fun (k : (G).Op) (t : ℝ≥0) ↦ k ((S).E t v)) (P.cart_mirror 3 β i) (h i))
  exact totalMirror G B A R (mirrorMeasurable 3) (mirrorHome 3).toMeasurableEquiv.measurableEmbedding
    (funext fun i ↦ congrArg (fun v : G ↦ (f (R i):ℂ) • v) (he i).symm)

lemma dark_field_noZero : (Q).region {w : E4 | YM.time w=0} (P.darkField s n Z x)=0 :=
  Projections.darkTime S T _
lemma smear_noZero (p : SmoothDensity f) : (Q).region {w : E4 | YM.time w=0} (K Z)=0 :=
  (congrArg ((Q).region {w : E4 | YM.time w=0}) (P.pulseDark_reach s n Z f x)).trans
    (reach_dark S T f _ p)

lemma rayPrice (t : SmoothDensity f) (J : P.Ellis 3 x) (p : P.OnFrame s n (η) f 0) :
    P.measureField s n (η) f x= Matrix.gram ℂ (fun Z ↦ K Z) := by
  have ht := mirrorSmooth f 3 t
  ext1 Z Z'
  exact (P.measureField_integral s n Z Z' (η) f 0 x ht.smooth.continuous ht.compact
    t.smooth.continuous t.compact J p).2.trans (congrArg (inner ℂ · (K Z'))
      (P.reflected_dark_eq s n Z f x))

/-- These conditions in particular hold for the specified open interior ball with closure
inside both the *timelike* interior and the spatial octant condition. -/
structure SpectralWindow (D : Set E4) : Prop where
  positive : D.Nonempty
  actual : IsOpen D
  timeInside : D ⊆ Mink.inside
  spatialOctant : ∃ b : Fin 3 → Bool, D ⊆ YM.spatial ⁻¹' alley b

variable (D : Set E4)
local notation "D'" => Cheer.press (P.dew s n) D
abbrev projectionGrant (D : Set E4) (t : ℝ) :=
    (t:ℂ) • (1 : Matrix Window.Family Window.Family ℂ) ≤ Matrix.gram ℂ
      (fun j ↦ (P.seasons 3 (P.otherSpectrum 3 3 x)).ℚmeasure.region (Cheer.press (P.dew s n) D)
        (P.birthCloud x j s n))

lemma everyFrequencyPay (v₀ : P.ManyF 3 β) (U : Summit x)
    (p : SmoothDensity u) (q : TimeDensity g)
    (h : SpectralWindow D) (he : 0 < n) :
    ∀ᵐ y ∂((Q).diagonal v₀).restrict (D'), jointCost T (ClockTest.joined u g) y ≠ 0 := by
  let A := SpectralWindow.spatialOctant h
  let b := A.choose; let k := P.dew s n
  let E := alley b; let E' := Cheer.press k D
  have he' : E' ⊆ YM.spatial ⁻¹' E := fun y p ↦ blaze_keep b k (P.dew_pos s he)
    (A.choose_spec (show Cheer.zoom k y∈ D from p))
  have ht : E' ⊆ Mink.inside := fun y p ↦ by
    apply Set.Subset.trans (Set.preimage_mono (f:= Cheer.zoom k) h.timeInside) _ p
    rw [Cheer.zoom_inside (P.dew_pos s he)]
  exact cost_octant u g E' _ E (alley_open b).measurableSet
    (Cheer.pressured k h.actual.measurableSet) he' ht p q T (P.travelTime_pos s n he)
    (U.footprint (Fin 3) tracks3 3 axleS b v₀)

/-- Both the Gram grant with its projection-level strengthening and the ordinary
macroscopic answer against which the raw-marginal factors will be compared. -/
structure ReflectedGrant : Prop where
  frame : P.OnFrame s n (f ∘ mirrorΩ 3) f 0
  smooth : SmoothDensity f
  reflected : SmoothDensity (f ∘ mirrorΩ 3)
  raw_price : ∀ (Z W : Window.Family), Tendsto
    (fun i ↦ P.measureAt s n i (f ∘ mirrorΩ 3) f x Z W) atTop
      (𝓝 (P.measureField s n (f ∘ mirrorΩ 3) f x Z W))
  answer : P.measureField s n (f ∘ mirrorΩ 3) f x = Matrix.gram ℂ (fun j ↦ K j)
  energy : ∀ j : Window.Family, (Q).region {w : E4 | time w=0} (K j)=0
  price : ∃ d : ℝ, 0 < d ∧
    (d:ℂ) • (1 : Matrix Window.Family Window.Family ℂ) ≤ Matrix.gram ℂ
      (fun j ↦ (Q).region (D') (K j)) ∧
    (d:ℂ) • (1 : Matrix Window.Family Window.Family ℂ) ≤ P.measureField s n (f ∘ mirrorΩ 3) f x

lemma rays_stay (J : P.Ellis 3 x) (U : Summit x) (h : SpectralWindow D)
    (p : SmoothDensity u) (q : TimeDensity g)
    (w₀ : P.TimeFare s n g) {d : ℝ} (e : 0 < d) (hs : P.projectionGrant s n x D d) (he : 0 < n) :
    P.ReflectedGrant s n (ClockTest.joined u g) x D := by
  let f := ClockTest.joined u g
  have hp := P.calendarFrame s n u g w₀
  have hu := joined_density u g p q
  have hh := mirrorSmooth f 3 hu
  let K' := P.measureField s n (f ∘ mirrorΩ 3) f x
  let F (i : Window.Family) := P.darkSmear s n i f 0 x true
  let L (i : Window.Family) := original i
  have ha : K'=Matrix.gram ℂ F := P.rayPrice s n f x hu J hp
  refine ⟨hp,hu,hh,(fun i j ↦ P.measure_tends s n i j _ _ _ x hh.smooth.continuous hh.compact
    hu.smooth.continuous hu.compact J hp),ha, (fun i ↦ P.smear_noZero s n i f x hu), ?_⟩
  let V := T
  have hx := ball_stable G S F L V (P.travelTime_pos s n he) f hu
    (fun i ↦ P.pulseDark_reach s n i f x) (D') (Cheer.pressured (ρ) h.actual.measurableSet)
    (fun y ↦ P.everyFrequencyPay s n u g x D y U p q h he) d e hs
  -- rewriting direction to avoid defeq expense
  refine ⟨hx.choose,hx.choose_spec.1,hx.choose_spec.2.1,le_trans hx.choose_spec.2.2 ha.ge⟩

variable {P x} {C r : ℕ → ℕ} (A : Prototype.Launch P C r)
include A
/-- One threshold (on the given course+character), then *fixed* body index for
all applications. Works for any qualifying positive-time product form. This is
part (i)'s macroscopic measurement (the Ward disqualification proved separately). -/
theorem reflected_six {e : ℕ → ℝ} (Y : Prototype.readyUV P C r x e) (q : Tendsto e atTop (𝓝 0))
    (u : P.lodestarHere 3 (P.otherSpectrum 3 3 x)) (J : P.Ellis 3 x) (U : Summit x)
    (h : SpectralWindow D) : ∀ᶠ i in atTop,
    ∀ f : ClockTest.Space → ℝ, ∀ g : ℝ → ℝ, SmoothDensity f → TimeDensity g →
      P.TimeFare (C i) (r i) g → P.ReflectedGrant (C i) (r i) (ClockTest.joined f g) x D := by
  obtain ⟨d,v',p⟩ := sixGrant A Y q u D h.actual ((Set.inter_eq_self_of_subset_right
    h.timeInside).symm ▸ h.positive)
  exact p.mono fun i k f g hf hg w ↦ P.rays_stay (C i) (r i) f g x D J U h hf hg w v' k (A.unitSize i)

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.reflected_six
