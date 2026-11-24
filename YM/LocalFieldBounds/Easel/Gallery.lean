import YM.LocalFieldBounds.Easel.Stair
import YM.LocalFieldBounds.Easel.Coat
import YM.LocalFieldBounds.Easel.Hedge

/-!
# Pose prices for direct thermometry

Collect the point purchases *at Minkowski poses* with the displayed
regulator heat (three w payments; middle lag continued). Earn their
approach to direct via quadrature at that pad.
-/
noncomputable section
namespace YM.LocalFieldBounds.Easel
open Function Filter Set MeasureTheory
open OS OS.Semigroup SatinRegistration SatinWFixed Carton
open GarnetAct.Cut Boundary Probe
open CF.Buffered.Afterglow.Hierarchy.Seld
open scoped Classical Topology NNReal InnerProductSpace ComplexOrder

variable {H : Hilbert} {S : OS.Semigroup H timeAxis} {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (B : Carton S V)

open ConePrice.Sail


open Marble

variable (w : ℝ≥0)
abbrev Whorl (a : V) (p : Paper) : H := beacon B a p w B.omega
lemma whorl_pure (a : V) (p : Paper) : Whorl B w a p =
    M S (face p) (B.bar w a B.omega) := by
  change M S (face p) (B.bar w a (M S (-face p) B.omega)) = _
  rw [B.stay]

lemma whorl_cozy (a : V) :
    Continuous (Whorl B w a) :=
  (village S B.omega (B.bar w a)).comp cont_face

lemma whorl_tame (a : V) (p : Paper) :
    ‖Whorl B w a p‖ = ‖B.bar w a B.omega‖ := by
  rw [whorl_pure]
  have h (x : H) :
      ‖M S (face p) x‖=‖x‖ := by
    have h := tsees S x x (face p)
    rw [inner_self_eq_norm_sq_to_K,
        inner_self_eq_norm_sq_to_K, ←RCLike.ofReal_pow, ←RCLike.ofReal_pow,
        RCLike.ofReal_inj,sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)] at h
    exact h
  apply h

lemma bill_glass (a : V) (F : Curtain) (p : 0 < w) :
    S.E w (myKet B a F) = ∫ x, Whorl B w a x ∂ F.ppm := by
  have h := B.blue_apply a w (film F) B.vacuum
  have heat : stoveAt S w B.vacuum = B.vacuum := Subtype.ext (B.hot _)
  rw [blue_stove _ _ _ p, heat, vmap, transpire] at h
  exact h

variable {R : InkWaves V} {W : WView V} (t : InkPort B R W)
include t
lemma sight (a : V) (p : 0 < w) (f : Curtain) (x : Paper) :
    W.expect [(a, film f)] = whisper B.omega (beacon B a x w) := by
  rw [t.real_value]
  have h : Integrable (Whorl B w a) f.ppm :=
    Integrable.of_bound (whorl_cozy B w a).aestronglyMeasurable ‖B.bar w a B.omega‖
      (Eventually.of_forall (fun y => (whorl_tame B w a y).le))
  change inner ℂ B.omega (myKet B a f) = inner ℂ B.omega (Whorl B w a x)
  conv_lhs =>
    rw [← B.hot w, S.swing, bill_glass B w a f p, ← integral_inner h]
  simp_rw [whorl_pure B w, tboth, B.stay]
  simp

omit t

def halo (p q : Paper) : ℂ := ↑(w:ℝ) + sideways (q 3 - p 3)
abbrev horizon (p : Paper) := p - elapsed (p 3)

lemma halo_inside (p : 0<w) (x y : Paper) :
    halo w x y ∈ inside := by
  unfold halo; change 0 < Complex.re _
  simpa [sideways] using p

lemma whorl_axis (a : V) (p : Paper) :
    Whorl B w a p = S.edge (p 3) (Whorl B w a (horizon p)) := by
  let r := face (horizon p)
  rw [whorl_pure, whorl_pure, ←timeslot]
  have e : p 3 • basis timeAxis + face (horizon p) = face p := by
    change _ + (face p - p 3 • basis timeAxis) = face p; abel
  have h := (tgo S ((p 3) • basis timeAxis) (face (horizon p))).trans (congrArg (M S) e)
  exact DFunLike.congr_fun h.symm _


lemma kite (a b : V) (p q : Paper) (u : 0<w) :
    inner ℂ (Whorl B w a p) (S.E w (Whorl B w b q)) =
    inner ℂ (Whorl B w a (horizon p))
      (phase S (halo w p q) (Whorl B w b (horizon q))) := by
  have h : (S.edge (p 3)).comp (phase S (halo w p q)) =
      (S.E w).comp (S.edge (q 3)) := by
    rw [← phaseEdge S (halo_inside w u _ _),
      show S.E w = phase S (duration w) from (by rw [duration,width_real,Real.toNNReal_coe]),
      ← phaseHeld S (dur.2 u), halo, sideways, sideways, sideways,
      duration]
    congr 1; push_cast; ring
  rw [whorl_axis B w a p, whorl_axis B w b q]
  conv_rhs => rw [← tsees S _ _ ((p 3) • basis timeAxis), timeslot]
  congr 1
  exact DFunLike.congr_fun h.symm _

variable (J : JMap V) (a b : V) {F G : Curtain} {n : ℕ}
def couple (p q : Paper) :=
  inner ℂ (Whorl B w (J a) p) (S.E w (Whorl B w b q))

variable (A : Coat F n) (C : Coat G n)

def sampling (k : (i : A.Job) → (j : C.Job) → ℂ) :=
  ∑ i, ∑ j, ↑((A.ink i)*(C.ink j)) * k i j

local notation "curl" => couple B w J a b
theorem survey :
    sampling A C (fun i j => curl (A.note i) (C.note j)) =
      inner ℂ (A.offer (Whorl B w (J a))) (S.E w (C.offer (Whorl B w b))) := by
  unfold sampling Coat.offer
  simp_rw [← Complex.coe_smul, map_sum, map_smul, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  simp only [Complex.ofReal_mul, mul_assoc, couple]

abbrev waist (x y : H) :=
  inner ℂ (S.E w x) (S.E w (S.E w y))

def focus (F G : Curtain) : ℂ :=
  waist (S:=S) w (myKet B (J a) F) (myKet B b G)

theorem sail (A : ∀ n, Coat F n) (C : ∀ n, Coat G n) (hp : 0<w) :
    Tendsto (fun n => sampling (A n) (C n) (fun i j => curl
        ((A n).note i) ((C n).note j))) atTop
      (𝓝 (focus B w J a b F G)) := by
  simp_rw [survey, focus, waist, bill_glass _ _ _ _ hp]
  exact (Coat.calibration A (whorl_cozy B w _)).inner
      (((S.E w).continuous.tendsto _).comp (Coat.calibration C (whorl_cozy B w _)))

include t
theorem sea (z : Remembers B J) (F G : Curtain) :
    Tendsto (fun y => focus B y J a b F G) (𝓝 0)
      (𝓝 (W.expect [(a,film F),(b,film G)])) := by
  let x := myKet B (J a) F
  let y := myKet B b G
  have tea (w : ℝ≥0) : S.E w (S.E w y) = S.E (w+w) y := DFunLike.congr_fun (S.time w w).symm y
  have shrink (p : H) : Tendsto (fun w => S.E w p) (𝓝 0) (𝓝 p) :=
    by simpa [S.eZero] using (S.continuousE p).tendsto 0
  rw [nm_pair B J z t]
  change Tendsto (fun w => inner ℂ (S.E w x) (S.E w (S.E w y))) (𝓝 0) (𝓝 (inner ℂ x y))
  simp_rw [tea]
  have h := @tendsto_id ℝ≥0 (𝓝 0)
  have g : Tendsto (fun w : ℝ≥0=> w+w) (𝓝 0) (𝓝 0) := by simpa using h.add h
  exact (shrink x).inner ((shrink y).comp g)

omit t
abbrev Offset (q : Paper) (s : ℝ) := q + elapsed s

lemma timer (q : Paper) (s : ℝ) : Offset q s 3 = q 3+s := by
  simp only [Offset, Pi.add_apply, elapsed, Pi.smul_apply, smul_eq_mul,
    basis, PiLp.single_apply, show (3:Axis)=timeAxis from rfl, ↓reduceIte, mul_one]

lemma still (q : Paper) (s : ℝ) :
    horizon (Offset q s) = horizon q := by
  unfold horizon
  rw [timer]
  unfold Offset elapsed
  rw [add_smul]
  abel

lemma length_Offset (q : Paper) {s r : ℝ} (h : 0 ≤ s) (e : s ≤ r) :
    dist (Offset q s) q ≤ r := by
  apply (dist_pi_le_iff (h.trans e)).2
  intro i
  rw [Offset, elapsed, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Real.dist_eq, basis, PiLp.single_apply]
  split
  · simpa [abs_of_nonneg h] using e
  · simpa using h.trans e

#print axioms survey
end YM.LocalFieldBounds.Easel
