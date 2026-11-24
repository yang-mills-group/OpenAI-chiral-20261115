import YM.LocalFieldBounds.Easel.Fold

/-!
# Small apertures

Work on any Carton. Heated prices of the vacuum vectors for arbitrarily
small real Minkowski smears recover the thermostat's point prices on the nose
in the limit — pays via the CP powers, natural support and representation,
not a point value assumption at the real boundary.
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

open Metric
def Tight (F : ℕ → Curtain) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ᶠ i in atTop, (F i).boxS ⊆ closedBall (0 : Paper) r
lemma tight_issued : ∃ F : ℕ → Curtain, Tight F := by
  choose F p using (fun i : ℕ => Curtain.grows 0 (1/(i+1:ℝ)) (by positivity))
  exact ⟨F, fun _ h => (tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds h)).mono
    (fun i hk => (p i ▸ closedBall_subset_closedBall hk.le))⟩

theorem block_tends {F : ℕ → Curtain} (ht : Tight F) {v : Paper → H} (hv : Continuous v) :
    Tendsto (fun i => ∫ x, v x ∂ (F i).ppm) atTop (𝓝 (v 0)) := by
  have localok (i : ℕ) : Integrable v (F i).ppm := by
    obtain ⟨r, h⟩ := ((F i).ownsK.image hv.norm).bddAbove
    exact Integrable.of_bound hv.aestronglyMeasurable r
      ((F i).inhabits.mono fun _ p => h (mem_image_of_mem _ p))
  apply Metric.tendsto_nhds.2
  intro e he
  obtain ⟨d, hd, h⟩ := Metric.mem_nhds_iff.1 <|
    hv.continuousAt.preimage_mem_nhds (ball_mem_nhds (v 0) (half_pos he))
  filter_upwards [ht (d/2) (half_pos hd)] with i hi
  have hd' : (F i).boxS ⊆ ball (0:Paper) d :=
    hi.trans (closedBall_subset_ball (half_lt_self hd))
  have hb : ∀ᵐ x ∂ (F i).ppm, ‖v x - v 0‖ ≤ e/2 :=
    (F i).inhabits.mono fun _ p =>
      (lt_of_le_of_lt le_rfl (by rw [←dist_eq_norm]; exact h (hd' p))).le
  have e' := norm_integral_le_of_norm_le_const hb
  have es : dist (∫ x, v x ∂ (F i).ppm) (v 0) ≤ e/2 := by
    simpa [integral_sub (localok _) (integrable_const _), dist_eq_norm] using e'
  exact es.trans_lt (half_lt_self he)

theorem valise_tends {F : ℕ → Curtain} (ht : Tight F) (A : H.Op) (y : H) :
    Tendsto (fun i => valise S A (film (F i)) y) atTop (𝓝 (A y)) := by
  simp_rw [vmap, transpire]
  have h := block_tends ht ((village S y A).comp cont_face)
  simpa [Function.comp, face, vroot] using h

abbrev myKet (a : V) (F : Curtain) : H :=
  (B.operator a (film F) B.vacuum).val

private lemma exact_heat (a : V) (w : ℝ≥0) (p : 0 < w) (F : Curtain) :
    S.E w (myKet B a F) = valise S (B.bar w a) (film F) B.omega := by
  have h := (B.blue_apply a w (film F) B.vacuum).symm
  have heat : stoveAt S w B.vacuum = B.vacuum := Subtype.ext (B.hot _)
  rw [blue_stove _ _ _ p, heat] at h
  exact h.symm

lemma at_heat {F : ℕ → Curtain} (ht : Tight F)
    (a : V) (w : ℝ≥0) (p : 0 < w) :
    Tendsto (fun i => S.E w (myKet B a (F i))) atTop
      (𝓝 (B.bar w a B.omega)) := by
  simp_rw [exact_heat B a w p]
  exact valise_tends ht ..

lemma myKet_moves (a : V) (F : Curtain) (o : Paper) :
    myKet B a (sweep F o) = M S (face o) (myKet B a F) := by
  have h := field_translate S _ (B.coherent a) (B.price a)
    (film F) (face o) B.vacuum
  rw [←lantern, show SatinRegistration.shift S (face o) B.vacuum = _
    from (Subtype.ext (B.stay (face o)) : SatinRegistration.shift S (face o) B.vacuum = B.vacuum)] at h
  exact congrArg Subtype.val h.symm

abbrev beacon (a : V) (o : Paper) (w : ℝ≥0) :=
  optx S (B.bar w a) (face o)

lemma beacon_tends {F : ℕ → Curtain} (ht : Tight F)
    (a : V) (o : Paper) (w : ℝ≥0) (p : 0 < w) :
    Tendsto (fun i => S.E w (myKet B a (sweep (F i) o))) atTop
      (𝓝 (beacon B a o w B.omega)) := by
  simp_rw [exact_heat B a w p, lantern, ← precursor]
  exact ((M S (face o)).continuous.tendsto _).comp
    (valise_tends (S := S) ht (B.bar w a) (M S (-face o) B.omega))

variable (J : JMap V) (z : Remembers B J)
open Marble
include z in
lemma beacon_left (a : V) (o : Paper) (w : ℝ≥0) :
    star (beacon B a o w) = beacon B (J a) o w := by
  rw [beacon, beacon, versX, z.bill]; rfl

abbrev amber (p q : Paper) (w : ℝ≥0) (r : ℝ) (a b : V) : ℂ :=
  seam S B.omega r (beacon B a p w) (beacon B b q w)

def satinBlue (L : H.Op) (x y : H) :=
  inner ℂ x (L y) - inner ℂ x B.omega * inner ℂ B.omega y

include z in
lemma amber_apply (p q : Paper) (w : ℝ≥0) (r : ℝ) (a b : V) :
    amber B p q w r a b =
      satinBlue B (S.wax r) (beacon B (J a) p w B.omega)
                              (beacon B b q w B.omega) := by
  rw [amber, seam, hot_pay, satinBlue,
    ← beacon_left B J z]

  unfold whisper
  change _ = _ - inner ℂ ((beacon B a p w).adjoint B.omega) _ * _
  rw [ContinuousLinearMap.adjoint_inner_left]

lemma satinBlue_heat (x y : H) (w r : ℝ≥0) :
    satinBlue B (S.E (w+(r+w))) x y = satinBlue B (S.E r) (S.E w x) (S.E w y) := by
  unfold satinBlue
  rw [S.time, S.time, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ← S.swing, S.swing w x B.omega, ← S.swing w B.omega, B.hot]

abbrev sauce (a b : V) (F G : Curtain) (L : H.Op) :=
  satinBlue B L (myKet B (J a) F) (myKet B b G)

include z in
/-- In the small-aperture limit, staggered Eu pose at **that pad**. In
use below p and q have time zero and the positive gap is w+(max(0,r)+w). -/
theorem simmer (p q : Paper) (w : ℝ≥0) (h : 0 < w) (r : ℝ)
    {F : ℕ → Curtain} (ht : Tight F) (a b : V) :
    Tendsto (fun i =>
      sauce B J a b (sweep (F i) p) (sweep (F i) q) (S.E (w+(r.toNNReal+w))))
      atTop (𝓝 (amber B p q w r a b)) := by
  simp_rw [amber_apply B J z, sauce, satinBlue_heat, satinBlue]
  have v := beacon_tends B ht (J a) p w h
  have u := beacon_tends B ht b q w h
  have t := (tendsto_const_nhds (x := B.omega) (f := atTop (α := ℕ)))
  exact (v.inner (((S.wax r).continuous.tendsto _).comp u)).sub
       ((v.inner t).mul (t.inner u))

end YM.LocalFieldBounds.Easel
