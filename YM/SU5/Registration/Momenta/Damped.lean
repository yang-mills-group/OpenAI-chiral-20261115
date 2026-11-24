/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.Work.C10
import YM.Work.C11
import YM.Work.C12
import YM.Work.C13
import YM.Work.C14
import YM.Work.C15
import YM.Work.C16
import YM.SU5.Registration.LineUp.OrderEcho
/-!
 # Spectrum on this stencil sector: extension & matching. 
 **Adapts from pinned `YM/Shift/Sol` and Work/C13,14,15,16** (quotes/ports a lot directly).
 Now on actual WView temperatures. Generic in the M12 spin budgets wk.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinWFixed
open Function Set Filter Distribution MeasureTheory Mink Mink.Poincare Boundary
open _root_.YM.Boundary.Probe
open scoped Topology BigOperators ContDiff InnerProductSpace
variable {V:Type*} [AddCommGroup V] [Module ℂ V] {W:WView V} {n:ℕ}
structure Palette (W : WView V) (D : ∀ i : ℕ, Blanket i) where
  lens (n : ℕ) (p : Full n) : Joint n
  shape (n : ℕ) (p : Full n) (h : p∈tube n) : ∀ x, lens n p x = (D n).lens p x

namespace Palette
variable {W : WView V} {D : ∀ i : ℕ, Blanket i} (X : Palette W D)

def emit (v : Fin n → V) (p : Full n) := ((pref (Points n))⁻¹ : ℂ) * Distn.fourier (W.W n v) (X.lens n p)

structure FullBody (F : InkWaves V) : Prop where
  hol (n : ℕ) (v : Fin n → V) : AnalyticOnNhd ℂ (X.emit v) (tube n)
  builds (n : ℕ) (v : Fin n → V) (y : Points n) (hy : y∈fields n) (f : Joint n) :
    (D n).partialD (W.W n v) y f= ∫ x,X.emit v (glow x y) * f x
  leaned (n : ℕ) (v : Fin n → V) (y : Points n) (hy : y∈fields n) (f : Joint n) :
    Integrable (fun x => X.emit v (glow x y) * f x)
  pure (n : ℕ) (v : Fin n → V) (x : Points n) (y : Heights n) (hp : y∈east n) : X.emit v (glow x (dawn y)) = F.restricted v y x

lemma sees {F : InkWaves V} (h : X.FullBody F) (v : Fin n → V) (y : Points n) (p : y∈shores n) (hm : (D n).Modified) (f : Joint n) :
    Tendsto (fun z => ∫ x, X.emit v (glow x z)*f x) (𝓝[fields n] y) (𝓝 ((D n).partialD (W.W n v) y f)) :=
    (((D n).tends hm _ f y p).mono (warmer n)).congr' (Eventually.mono self_mem_nhdsWithin fun _ hz => h.builds n _ _ hz _)

lemma lower {F : InkWaves V} (h : X.FullBody F) (v : Fin n → V) (y : Heights n) (x : Points n) (hp : y∈east n) :
    W.W n v =0 → F.restricted v y x=0 := by
  intro ht
  rw [← h.pure n v x y hp,emit,Distn.fourier_at,ht]; simp
end Palette

namespace Palette
open YM.Work.C13 (phase shiftDeriv hasFDerivAt_shift lens_reserve lens_eq interiorLens interiorLens_apply)
variable {D: ∀ n, Blanket n}
/-- The derivative works for any `Palette`, since it uses the form of the
lens in the open tube only. -/
lemma hasFDerivAt_interior (X : Palette W D) (hw : Bid.Wide n) (p : Full n) (hp : p ∈ tube n) :
    HasFDerivAt (X.lens n) (shiftDeriv (phase n) (X.lens n p)) p := by
  apply hasFDerivAt_shift
  · rw [show (X.lens n p : Points n → ℂ) = (D n).lens p from funext (X.shape n p hp)]
    exact lens_reserve _ hw p hp
  · filter_upwards [(south n).mem_nhds hp] with q hq x
    have h : phase n q x = phase n (q-p) x + phase n p x := by simp
    rw [X.shape n q hq x, X.shape n p hp x, lens_eq, lens_eq, h, Complex.exp_add, mul_assoc]

lemma analytic_interior (X : Palette W D) (hw : Bid.Wide n) (v : Fin n → V) :
    AnalyticOnNhd ℂ (X.emit v) (tube n) := by
  intro p hp
  apply PolyDisc.finiteD
  filter_upwards [(south n).mem_nhds hp] with q hq
  let F := Distn.fourier (W.W n v)
  have h : HasFDerivAt (fun x => F (X.lens n x))
      (F.comp (shiftDeriv (phase n) (X.lens n q))) q := by
    rw [hasFDerivAt_iff_isLittleOTVS]
    have ht := F.isBigOTVS_comp.trans_isLittleOTVS
      ((hasFDerivAt_iff_isLittleOTVS).mp (hasFDerivAt_interior X hw q hq))
    simpa only [Function.comp_def, map_sub, ContinuousLinearMap.comp_apply] using ht
  exact h.differentiableAt.const_mul _


abbrev blanket (n:ℕ):Blanket n:= Classical.choice (Work.C11.answer n)
def ticket (D : ∀ n, Blanket n)(W:WView V):Palette W D:= ⟨fun n=> interiorLens (D n) (Work.C10.answer n),fun n p hp=> interiorLens_apply (D n) (Work.C10.answer n) p hp⟩
lemma modified (B: Blanket n): B.Modified:= Work.C12.answer n (Work.C10.answer n) B
open YM.Work.C14
/-- For fixed strictly admissible imaginary part. No change of regulator or
uniform bound as the imaginary part varies is needed here. -/
lemma emit_integral (Y : Palette W D) (n : ℕ) (v : Fin n → V)
    (y : Points n) (h : y ∈ fields n) (hm : (D n).Modified) (f : Joint n) :
    (D n).partialD (W.W n v) y f = (∫ x, Y.emit v (glow x y) * f x) ∧
    Integrable (fun x => Y.emit v (glow x y) * f x) := by
  let P (x : Points n) := Y.lens n (glow x y)
  let g := P 0
  let w := Distn.fourier (W.W n v)
  have hP (x b : Points n) : P x b = plane b x * (D n).attenuate y b := by
    have hy : glow x y ∈ tube n := by simpa only [tube, mem_preimage, im_glow] using h
    simp only [P, Y.shape n _ hy, Blanket.lens, re_glow, im_glow]
  have hg (b : Points n) : g b = (D n).attenuate y b := by simp only [g, hP, plane_zero, one_mul]
  have hL (x b : Points n) : P x b = plane b x * g b := by rw [hP, hg]
  have he (q : Probe (Points n)) : (D n).diffuser y q = sew g q := by
    ext1 x
    rw [Blanket.diffuser, SchwartzMap.smulLeftCLM_apply_apply (hm.actual y (warmer n h)),
      sews, hg]
    rfl
  refine ⟨?_, modulation_integrable g P hL w f⟩
  change w ((D n).diffuser y (port f)) = _
  rw [he]
  exact modulation_all g P hL w f

open YM.Work.C15 (east_broad blanketed_eq lifts_cancel eq_of_tests)
theorem restricted_bounded {F : InkWaves V} (p : F.Breathes) (v : Fin n → V)
    {y : Heights n} (hy : y ∈ east n) : ∃ K : ℝ, ∀ x, ‖F.restricted v y x‖ ≤ K := by
  obtain ⟨m,C,_,h⟩ := p n v
  obtain ⟨k,hk,hb⟩ := east_broad hy
  exact ⟨_,h y k hk hb⟩

/-- At fixed ordered heights the tested wave really defines a tempered distribution. -/
theorem psi_tempered {F : InkWaves V} (p : F.Breathes) (b : F.Bounds) (v : Fin n → V)
    {y : Heights n} (hy : y ∈ east n) : ∃ u : Distn (Points n), ∀ f : Joint n, u f = F.psi v y f := by
  obtain ⟨K,hK⟩ := restricted_bounded p v hy
  let u : Joint n →ₗ[ℂ] ℂ :=
    { toFun := F.psi v y
      map_add' := by
        intro f g
        unfold InkWaves.psi
        rw [← integral_add (b n v y hy f) (b n v y hy g)]
        apply integral_congr_ae; filter_upwards with x; simp [mul_add]
      map_smul' := by
        intro c f
        change (∫ x, F.restricted v y x * (c • f) x) = c * F.psi v y f
        rw [InkWaves.psi, ← integral_const_mul]; apply integral_congr_ae
        filter_upwards with x; simp; ring }
  have hu : Continuous u := sways (fun f => K * weight f)
    (weight_cont.const_mul K) (by simp) (fun f => compromise f _ _ hK)
  exact ⟨⟨u,hu⟩,fun _ => rfl⟩

/-- Fourier transform of the strict restriction, then back to absolute position variables. -/
theorem partialD_psi {W : WView V} {B : Blanket n} {F : InkWaves V} (hb : B.Modified)
    (hw : W.conical) (p : F.Breathes) (b : F.Bounds) (d : F.during W)
    (v : Fin n → V) {y : Heights n} (hy : y ∈ east n) (f : Joint n) :
    B.partialD (W.W n v) (dawn y) f = F.psi v y f := by
  obtain ⟨u,hu⟩ := psi_tempered p b v hy
  let w := (Distn.fourier (W.W n v)).comp (B.diffuser (dawn y))
  have he (g : Joint n) (hg : HasCompactSupport ⇑g) : w g = Distn.fourier u g := by
    change Distn.fourier (W.W n v) (B.diffuser (dawn y) g) = u (hat g)
    rw [blanketed_eq hb _ (hw n v) _ (warmer n (etched hy)) _ hg,
      d n v y hy _ (remains _ g hg), lifts_cancel, hu]
  have hEq : w = Distn.fourier u := by
    ext1 g
    exact tendsto_nhds_unique_of_eventuallyEq ((w.continuous.tendsto g).comp (persistent g))
      (((Distn.fourier u).continuous.tendsto g).comp (persistent g))
      (Eventually.of_forall fun k => he (cap k g) (finite_cap k))
  change Distn.inverse w f = _
  rw [hEq, Distn.one, hu]

theorem restricted_continuous {F : InkWaves V} (r : F.Region) (v : Fin n → V)
    {y : Heights n} (hy : y ∈ east n) : Continuous (F.restricted v y) := by
  have hc : Continuous (fun x : Points n => (shift x y, Boundary.trace x)) := by
    unfold shift Boundary.trace; fun_prop
  apply continuousOn_univ.mp ((r.together n v).comp hc.continuousOn (fun x _ => ?_))
  refine ⟨?_,mem_univ _⟩
  change (fun i => (shift x y i).im) ∈ east n
  simpa [shift] using hy


theorem available {F:InkWaves V} (Y:Palette W D) (hw:W.conical) (r:F.Region)(p:F.Breathes)(b:F.Bounds)(d:F.during W) : Y.FullBody F:=by
  have hY := fun (n:ℕ) v=> Y.analytic_interior (Work.C10.answer n) v
  have builds:=fun (n:ℕ)(v:Fin n→V) y hy f => (emit_integral Y n v y hy (modified (D n)) f).1
  refine ⟨hY,builds,fun n v y hy f=>(emit_integral Y n v y hy (modified _) f).2,fun n v x y hy=>?_⟩
  have hc : Continuous (fun x : Points n => glow x (dawn y)) :=
    (home n).comp (continuous_id.prodMk continuous_const)
  have ht (x : Points n) : glow x (dawn y) ∈ tube n := by simpa [tube] using etched hy
  have hg : Continuous (fun x => Y.emit v (glow x (dawn y))) :=
    continuousOn_univ.mp ((hY n v).continuousOn.comp hc.continuousOn (fun x _ => ht x))
  apply congr_fun (eq_of_tests _ _ hg (restricted_continuous r v hy) _) x
  intro f
  rw [← builds n v _ (etched hy) f]
  exact partialD_psi (modified (D n)) hw p b d v hy f

open YM.Bid
open YM.Work.C16 (dual_mem_coneM rect_mem_tube)
/-- Pull the lens back to the original frequency coordinates. The difference
is a Schwartz test supported in the open complement of the spectral cone. -/
lemma lens_support (W : WView V)
    (D : ∀ i, Blanket i) (Y : Palette W D) {n : ℕ} (r : Lorentz)
    {x : Full n} (hx : x ∈ tube n) :
    tsupport (Y.lens n x - along (togetherL (Lorentz.dual r) n) (Y.lens n (rect r x))) ⊆
      (coneM n)ᶜ := by
  let A := togetherL (Lorentz.dual r) n
  let U := Y.lens n x - along A (Y.lens n (rect r x))
  change tsupport U ⊆ _
  intro p ht hp
  have hA : A p ∈ coneM n := dual_mem_coneM r hp
  let N := Metric.ball p 1 ∩ (A ⁻¹' Metric.ball (A p) 1)
  have ho : IsOpen N := Metric.isOpen_ball.inter (Metric.isOpen_ball.preimage A.continuous)
  have hn : p ∈ N := ⟨Metric.mem_ball_self zero_lt_one,
    show A p ∈ Metric.ball (A p) 1 from Metric.mem_ball_self zero_lt_one⟩
  have he : Disjoint N (Function.support U) := by
    refine Set.disjoint_left.mpr ?_
    rintro q ⟨hq, hQ⟩ h
    have hc : (D n).cut q = 1 := (D n).immediate q ⟨p, hp, hq⟩
    have hC : (D n).cut (A q) = 1 := (D n).immediate (A q) ⟨A p, hA, hQ⟩
    apply h
    change Y.lens n x q - (along A (Y.lens n (rect r x))) q = 0
    rw [along_at, Y.shape n x hx q, Y.shape n (rect r x) (rect_mem_tube r hx)]
    have phase : plane (A q) (togetherL r n (reality x)) = plane q (reality x) := by
      rw [plane_dot, plane_dot q]
      simp only [plane, A, Boundary.parr]
    simp only [Blanket.lens, Blanket.attenuate, rect, re_glow, im_glow, hc, hC,
      phase, show inner ℝ (togetherL r n (shade x)) (A q) = inner ℝ (shade x) q from
        Boundary.parr r (shade x) q, sub_self]
  exact Set.disjoint_left.1 (he.closure_right ho) hn ht


def Spun (Y:Palette W D) (R:Courts V): Prop:= ∀ n (v:Fin n → V) (K:Lorentz) x, x∈tube n → Y.emit v x=Y.emit (fun i=>R.mi K (v i)) (rect K x)
theorem spun_of_selfSpeaks (K:Courts V)(Y:Palette W D)(hurs:W.SelfSpeaks K)(hcone:W.conical): Y.Spun K:=by
  intro n v r x hx
  let A := togetherL (Lorentz.dual r) n
  let v' := fun i : Fin n => K.mi r (v i)
  let f := Y.lens n (rect r x)
  have he : Distn.fourier (W.W n v) (Y.lens n x) = Distn.fourier (W.W n v) (along A f) := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact ((Distn.due _ _ (closedM n)).1 (hcone n v)) _ (lens_support W D Y r hx)
  have hv (z : Joint n) :
      Distn.fourier (W.W n v') (along A.symm z) = Distn.fourier (W.W n v) z := by
    simp only [Distn.fourier_at, A, Boundary.turns]
    exact hurs.rotation n v (hat z) r
  unfold emit
  rw [he, ← hv (along A f), Probe.along_inv]

end Palette
end YM.SatinWFixed
