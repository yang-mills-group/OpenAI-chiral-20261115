/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SU5.Registration.LineUp.Bourse
import YM.SU5.Registration.Ink.Tolls
/-! adapt Work/C07/Continue,C07 to Ink. At strictly imaginary offsets.
 No joint holomorphy in spacetime coordinates or point Eu smooth law yet. Uses Bourse.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinWFixed.HelioRoof
open Set Boundary Mink Function Filter MeasureTheory Table Analysis Complex Bid
open Work.C07 (scaled_imag test_one testField test_imag integral_orbit fold_derivative fold_smooth orbit_image orbit scaledTimes stretchY foldE scaled_strict_imag incline_cont scaled_one test_zero_off analytic_integral)
open scoped Topology ContDiff BigOperators
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
variable {Y:InkWaves V}{R:Courts V}
private def allowed (K : Set (Points n)) (y : Heights n) : Set ℂ :=
    {z | ∀ p ∈ K, scaledTimes y z p ∈ strict n}

private lemma scaled_cont (y : Heights n) :
    Continuous (uncurry (scaledTimes y)) := by
  change Continuous fun p : ℂ × Points n => scaledTimes y p.1 p.2
  unfold scaledTimes; fun_prop

private lemma allowed_open {K : Set (Points n)} (y : Heights n) (hK : IsCompact K) : IsOpen (allowed K y) := by
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  let W := uncurry (scaledTimes y) ⁻¹' strict n
  have hW : ({z} : Set ℂ) ×ˢ K ⊆ W := by
    rintro ⟨p,q⟩ ⟨hp,hq⟩
    exact (show p=z from hp).symm ▸ hz q hq
  obtain ⟨t,s,ht,-,htz,hsK,H⟩ := generalized_tube_lemma isCompact_singleton hK
    ((open_strict n).preimage (scaled_cont y)) hW
  exact ⟨t, fun a ha b hb => H (mk_mem_prod ha (hsK hb)), ht, htz (mem_singleton z)⟩

private lemma allowed_convex (K : Set (Points n)) (y : Heights n) : Convex ℝ (allowed K y) := by
  rw [convex_iff_forall_pos]
  intro z hz r hr a b ha hb hab p hp i j hij
  have he (k : Fin n) : (scaledTimes y (a • z + b • r) p k).im =
      a * (scaledTimes y z p k).im + b * (scaledTimes y r p k).im := by
    simp only [scaledTimes, add_im, mul_im, ofReal_re, ofReal_im, real_smul,
      I_re, I_im, mul_zero, zero_mul, zero_add, add_zero, mul_one]
    linear_combination -(y k)*hab
  change (scaledTimes y _ p i).im < (scaledTimes y _ p j).im
  rw [he, he]
  exact add_lt_add (mul_lt_mul_of_pos_left (hz p hp hij) ha) (mul_lt_mul_of_pos_left (hr p hp hij) hb)

private lemma allowed_real (K : Set (Points n)) {y : Heights n} (hy : y ∈ east n) (z : ℝ) :
    (z : ℂ) ∈ allowed K y := fun p _ i j h => by simpa [scaledTimes] using hy h

private lemma error_analytic (hr : Y.Region) (R : Courts V) {K : Set (Points n)} (hK : IsCompact K)
    (a : SpaceAxis) (y : Heights n) (v : Fin n → V) (f : Joint n) :
    AnalyticOnNhd ℂ (fun z => ∫ p in K, errorF Y R a y v f z p) (allowed K y) := by
  let U := allowed K y
  apply analytic_integral hK _ (allowed_open y hK)
  · have ht : Continuous (fun p : Points n => trace p) := by unfold trace; fun_prop
    have hu (q : Fin n → V) : ContinuousOn (fun p : ℂ × Points n => seenF Y q y p.1 p.2)
        (U ×ˢ K) :=
      (hr.together n q).comp ((scaled_cont y).prodMk (ht.comp continuous_snd)).continuousOn
        (by rintro ⟨z,p⟩ ⟨hz,hp⟩; exact ⟨hz p hp, mem_univ _⟩)
    change ContinuousOn (fun p : ℂ × Points n => errorF _ _ _ _ _ _ p.1 p.2) _
    have hF : Continuous (fun p : ℂ × Points n => testField a y p.1 f p.2) := by
      unfold testField; refine continuous_finsetSum _ fun i _ => ?_
      have ht (b : Axis) : Continuous (fun p : ℂ × Points n => realTerm i b f p.2) :=
        (realTerm i b f).continuous.comp continuous_snd
      have hi : Continuous (fun p : ℂ × Points n => scaledTimes y p.1 p.2 i) :=
        (continuous_apply i).comp (scaled_cont y)
      exact Continuous.add ((by fun_prop : Continuous fun p : ℂ × Points n => ((p.2 i a.castSucc:ℝ):ℂ)).mul (ht timeAxis))
        ((continuous_fst.mul hi).mul (ht a.castSucc))
    unfold errorF
    exact ((hu _).mul hF.continuousOn).sub ((continuous_fst.continuousOn.mul
      (continuousOn_finsetSum _ fun i _ => hu (Cosm R a v i))).mul
      (f.continuous.comp continuous_snd).continuousOn)
  intro p hp
  have hk : Differentiable ℂ (fun z => scaledTimes y z p) := by
    unfold scaledTimes; fun_prop
  have hs (q : Fin n → V) : DifferentiableOn ℂ (fun z => seenF Y q y z p) U :=
    (hr.hol n q (trace p)).comp hk.differentiableOn fun _ hz => hz p hp
  have hT : Differentiable ℂ (fun z => testField a y z f p) := by
    unfold testField; unfold scaledTimes; fun_prop
  unfold errorF
  apply DifferentiableOn.sub ((hs _).mul hT.differentiableOn)
  exact (differentiableOn_id.mul (DifferentiableOn.fun_sum fun i _ => hs
    (Cosm R a v i))).mul_const _

private theorem error_one (hO : R.Carriage Y)
    (hr : Y.Region) (a : SpaceAxis) (y : Heights n) (hy : y ∈ east n)
    (v : Fin n → V) (f : Joint n) (hK : HasCompactSupport ⇑f) :
    (∫ p in tsupport f, errorF Y R a y v f 1 p) = 0 := by
  let K := tsupport f
  let U := allowed K y
  have h₀ : (0 : ℂ) ∈ U := by simpa using allowed_real K hy 0
  have h₁ : (1 : ℂ) ∈ U := by simpa using allowed_real K hy 1
  apply (error_analytic hr R hK a y v f).eqOn_zero_of_preconnected_of_frequently_eq_zero
    ((allowed_convex K y).isPreconnected) h₀ _ h₁
  intro hh
  have ht : Tendsto (fun w : ℝ => (w : ℂ)*I) (𝓝[>] 0) (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hc : Continuous (fun w : ℝ => (w : ℂ)*I) := by fun_prop
      simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    filter_upwards [self_mem_nhdsWithin] with w hw
    change _ ≠ _; simp [ne_of_gt (show 0<w from hw)]
  have hK' : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ U :=
    Eventually.filter_mono nhdsWithin_le_nhds ((allowed_open y hK).mem_nhds h₀)
  obtain ⟨w,hw,hU⟩ := (ht.eventually (hh.and hK')).exists
  exact hw (error_imag R hO hr a y v f w hK hU)

lemma compact_boost (hO : R.Carriage Y)
    (hr : Y.Region) (hB : Y.Bounds) (a : SpaceAxis) (y : Heights n) (hy : y ∈ east n)
    (v : Fin n → V) (f : Joint n) (hK : HasCompactSupport ⇑f) :
    (∑ i, Y.psi (Cosm R a v i) y f) = Y.psi v y (inclined a y f) := by
  have he (p : Points n) (hp : p ∉ tsupport f) : errorF Y R a y v f 1 p = 0 := by
    rw [errorF, test_zero_off a y _ f hp, image_eq_zero_of_notMem_tsupport hp]
    ring
  let f' := inclined a y f
  let q (i : Fin n) (p : Points n) := seenF Y (Cosm R a v i) y 1 p * f p
  have hq (q : Fin n → V) (p : Points n) : Y.restricted q y p = seenF Y q y 1 p := by rw [seenF, scaled_one]; rfl
  have hI (i) : Integrable (q i) := by
    simp_rw [q, ← hq]; apply hB _ _ _ hy
  have hJ : Integrable (fun p => seenF Y v y 1 p * f' p) := by
    simp_rw [← hq]; apply hB _ _ _ hy
  have h₁ := error_one hO hr a y hy v f hK
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero he] at h₁
  simp_rw [errorF, test_one, one_mul, Finset.sum_mul] at h₁
  change (∫ p, seenF Y v y 1 p * f' p - ∑ i, q i p) = 0 at h₁
  rw [integral_sub hJ (integrable_finsetSum _ fun i _ => hI i),sub_eq_zero,
    integral_finsetSum Finset.univ (fun i _ => hI i)] at h₁
  simp_rw [InkWaves.psi, hq]; exact h₁.symm

lemma continuous_test (hB : Y.Bounds) (ha : Y.Along) (hl : Y.Lines) (hb : Y.Breathes)
    (y : Heights n) (hy : y ∈ east n) (q : Fin n → V) : Continuous (Y.psi q y) := by
  obtain ⟨W,hW⟩ := Y.seeks hB ha hl hb y (bigger hy)
  haveI : (𝓝[east n] y).NeBot := awaits (bigger hy)
  have he (f : Joint n) : Y.psi q y f = W q f :=
    tendsto_nhds_unique (ha n q f y hy) (hW q f)
  rw [funext he]; exact (W q).continuous


def InkBoost (F:InkWaves V)(R:Courts V): Prop:= ∀ (n:ℕ) (v:Fin n→V) (a:SpaceAxis)(f:Joint n)(y:Heights n), y∈east n→ (∑ i, F.psi (Cosm R a v i) y f)=F.psi v y (Bid.inclined a y f)
theorem inkBoost (hr:Y.Region)(hb:Y.Breathes)(ha:Y.Along)(hB:Y.Bounds)(hl:Y.Lines)(hO:R.Carriage Y): InkBoost Y R:=by
  intro n v a f y hy
  let A (u : Joint n) := ∑ i, Y.psi (Cosm R a v i) y u
  let B (u : Joint n) := Y.psi v y (inclined a y u)
  have hA : Continuous A :=
    continuous_finsetSum _ fun i _ => continuous_test hB ha hl hb y hy _
  have hX : Continuous B :=
    (continuous_test hB ha hl hb y hy _).comp (incline_cont a y)
  have he (k : ℕ) : A (Probe.cap k f) = B (Probe.cap k f) :=
    compact_boost hO hr hB a y hy v (Probe.cap k f) (Probe.finite_cap k)
  have hz : Tendsto (fun k : ℕ => A (Probe.cap k f)) atTop (𝓝 (A f)) :=
    (hA.tendsto f).comp (Probe.persistent f)
  simp_rw [he] at hz
  exact tendsto_nhds_unique hz ((hX.tendsto f).comp (Probe.persistent f))

end YM.SatinWFixed.HelioRoof
open YM.SatinWFixed HelioRoof
#print axioms inkBoost
