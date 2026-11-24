import YM.LocalFieldBounds.Easel.Gold

/-!
# Edge test for direct staggered prices
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

/-- If a connected intersection is seen with heat, then allowing an open
time lag tests it at the *real edge*, near any desired real lag. Use continuity
after actual test-function smearing, retaining analyticity through the whole
imaginary *lag* of the second operator (right ket). -/
lemma lamp (x y : H) {w : ℝ≥0} (ht : 0 < w)
    (h : satinBlue B (S.E w) x y ≠ 0)
    (l r : ℝ) (o : l < r) :
    ∃ m ∈ Ioo l r, satinBlue B (S.edge m) x y ≠ 0 := by
  by_contra! q
  let I := Complex.I
  let g (z : ℂ) := satinBlue B (phase S (z*I)) x y
  have contour := SatinMacro.Glue.overlap_of_edge (f := fun _ => (0:ℂ)) (g := g)
    (a := -r) (b := -l) (r := -(w:ℝ)-1) (neg_lt_neg o)
    (by linarith only [show (0:ℝ)<w from ht]) analyticOnNhd_const
  have ad : AnalyticOnNhd ℂ g {z | z.im < 0} := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) (isOpen_lt Complex.continuous_im continuous_const)
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.sub_const
    apply ((innerSL ℂ x).differentiableAt).comp z (f:=fun z => phase S (z*I) y)
    apply DifferentiableAt.clm_apply _ (differentiableAt_const _)
    have v : z*I ∈ inside := by
      change 0 < (z*Complex.I).re
      simpa using hz
    exact (phase_ana S _ v).differentiableAt.comp z (differentiableAt_id.mul_const I)
  have cg : Continuous g :=
    (continuous_const.inner (phase_cont S (fun z => z*I) (fun _ => y) continuous_const
      (by fun_prop))).sub continuous_const
  have cr (x' : ℝ) (e : x' ∈ Ioo (-r) (-l)) : 0 = g ↑x' := by
    unfold g
    rw [show (↑x')*I = sideways (-x') by rw [sideways]; push_cast; rw [neg_neg],
        width_imaginary, q (-x') ⟨by linarith [e.2], by linarith [e.1]⟩]
  have m : (sideways (w:ℝ)).im = -(w:ℝ) := by simp [sideways]
  have k : (0:ℂ)= g (sideways (w:ℝ)) := contour ad cg.continuousOn cr
    ⟨by rw [mem_setOf_eq, m]; linarith only,
      by rw [mem_setOf_eq, m, neg_lt_zero]; exact ht⟩
  unfold g at k
  rw [show sideways (w:ℝ)*I = ((w:ℝ):ℂ) by rw [sideways, mul_assoc,
      show Complex.I*I= -1 from Complex.I_mul_I, mul_neg_one, neg_neg], width_real, Real.toNNReal_coe] at k
  exact h k.symm

variable (J : JMap V) (z : Remembers B J) {R : InkWaves V} {W : WView V}
    (t : InkPort B R W)

/-- Direct value via the W joint and two singles. -/
def inkTest (W : WView V) (a b : V) (F G : Curtain) : ℂ :=
  W.expect [(a, film F), (b, film G)]
    - W.expect [(a, film F)] * W.expect [(b, film G)]

include t z
lemma nm_pair (a : V) (F : Curtain) (C : MarkWords V) :
    W.expect ((a, film F)::C) = inner ℂ (myKet B (J a) F) (B.row C).val := by
  have p := InkPort.real_pair J t z [(J a, film F)] C
  unfold WView.kernel wordRev opTag at p
  -- reduce list map
  simp only [List.map_cons, List.map_nil, z.both a, film_real, List.reverse_singleton,
    List.cons_append, List.nil_append] at p
  exact p

lemma ink_P (a b : V) (F G : Curtain) :
    inkTest W a b F G = sauce B J a b F G 1 := by
  unfold inkTest
  rw [nm_pair B J z t, nm_pair B J z t, t.real_value]
  rfl

omit t z

abbrev elapsed (l : ℝ) : Paper :=
  (l • (basis timeAxis).ofLp)

include z t in
/-- Momentum identity over a **real** gap right in W. -/
lemma clockPass (a b : V) (F G : Curtain) (l r : ℝ) :
    inkTest W a b (sweep F (elapsed l)) (sweep G (elapsed r))
    = sauce B J a b F G (S.edge (r-l)) := by
  let D (l : ℝ) := l • basis timeAxis
  have m (l : ℝ) : face (elapsed l) = D l := rfl
  rw [ink_P B J z t]
  unfold sauce satinBlue
  rw [myKet_moves, myKet_moves, m, m, ←timeslot]
  change inner ℂ (M S (D l) _) (M S (D r) _)
    - inner ℂ (M S (D l) _) B.omega * inner ℂ B.omega (M S (D r) _) = _
  have p (o : E4) (x : H) : inner ℂ (M S o x) B.omega = inner ℂ x B.omega := by
    nth_rw 1 [← B.stay o]
    exact tsees ..
  have h (x y : H) :
      inner ℂ (M S (D l) x) (M S (D r) y)
        = inner ℂ x (M S (D (r-l)) y) := by
    conv_rhs => rw [← tsees S _ _ (D l)]
    have e : M S (D l) * M S (D (r-l)) = M S (D r) := by
      rw [tgo]; unfold D; rw [← add_smul]; abel_nf
    rw [show M S (D l) (M S (D (r-l)) y) = M S (D r) y from DFunLike.congr_fun e _]
  rw [p, h, tboth S B.omega, show M S (-D r) B.omega = _ from (B.stay (-D r) : M S (-D r) B.omega=B.omega)]

open Metric
open scoped ENNReal

lemma dual_room {r : ℝ} (_hr : 0 < r)
    {F : Curtain} (hF : F.boxS ⊆ closedBall (0:Paper) (r/2))
    (p : Paper) (l m : ℝ) (h : dist (elapsed m) (elapsed l) ≤ r/2) :
    (sweep (sweep F p) (elapsed m)).boxS ⊆
      closedBall (p + elapsed l) r := by
  rw [sweep_foot]
  rintro _ ⟨x,y,rfl⟩
  have hp : dist x p ≤ r/2 := sweep_room F p hF y
  exact (dist_add_add_le x (elapsed m) p (elapsed l)).trans ((add_le_add hp h).trans (le_of_eq (add_halves _)))

include z t in
/-- Mint a direct crossing with small normalized films translated from
a common shape. Can localize at any desired times (support balls may
even be arranged separately in Minkowski and near a Wick diagnostic). -/
theorem tone (p q : Paper) (w : ℝ≥0) (hw : 0 < w)
    (d : ℝ) (a b : V)
    (hB : amber B p q w d a b ≠ 0)
    (l m r : ℝ) (hr : 0 < r) :
    ∃ F G : Curtain,
      F.boxS ⊆ closedBall (p + elapsed l) r ∧
      G.boxS ⊆ closedBall (q + elapsed m) r ∧
      inkTest W a b F G ≠ 0 := by
  obtain ⟨T,h⟩ := tight_issued
  obtain ⟨i,g,j⟩ :=
    ((h _ (half_pos hr)).and ((simmer B J z p q w hw d h a b).eventually
      (eventually_ne_nhds hB))).exists
  let A := sweep (T i) p
  let C := sweep (T i) q
  let proceed := lamp B (myKet B (J a) A) (myKet B b C)
    (w:=w+(d.toNNReal+w)) (by positivity) j
  have he : Continuous elapsed := continuous_id.smul continuous_const
  have hi : Continuous (fun x => l+x) := continuous_const.add continuous_id
  obtain ⟨δ,hδ,cover⟩ :=
    Metric.continuous_iff.1 (he.comp hi) (m-l) (r/2) (half_pos hr)
  obtain ⟨s,v,hval⟩ := proceed ((m-l)-δ) ((m-l)+δ) (by linarith)
  refine ⟨sweep A (elapsed l), sweep C (elapsed (l+s)),dual_room hr g p l l (by simpa using (half_pos hr).le),dual_room hr g q m _ ?_, ?_⟩
  · have h := cover s (show dist s (m-l) < δ from ?_)
    · simpa [Function.comp] using h.le
    rw [Real.dist_eq]; exact abs_sub_lt_iff.2 ⟨by linarith [v.2], by linarith [v.1]⟩
  rw [clockPass B J z t, add_sub_cancel_left]
  exact hval

#print axioms tone
end YM.LocalFieldBounds.Easel
