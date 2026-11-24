/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SU5.Registration.Momenta.Damped
import YM.SU5.Registration.Momenta.Ventana
import YM.Shift.Exchange
/-!
 # Paint: analytic path-to-edge 
 Reuses proofs from YM pinned `YM/Shift/Exchange` and Work/C19 (verbatim adaptations),
 with M4 WView, Palette (full tube from purchased distributions there), and
 spin from *stock_time* entire extension along the path of Court ordinates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinWFixed
open Function Set Filter Distribution MeasureTheory Mink Mink.Poincare Boundary
open _root_.YM.Boundary.Probe
open scoped Topology BigOperators ContDiff InnerProductSpace
variable {V:Type*} [AddCommGroup V] [Module ℂ V] {W:WView V} {n:ℕ}
namespace Palette
open Metric NearPair
open scoped unitInterval ENNReal
variable {D:∀ i,Blanket i}
variable (P:NearPair n)
structure PairedPanes (X : Palette W D) (v : Fin n → V) (y : Heights n) where
  permitted : P.Fleck y
  original (x : Points n) : x∈P.gap→ Pane (X.emit v) (tube n) (glow x (dawn y))
  tilted (x : Points n) : x∈P.gap→ Pane ((X.emit (v ∘ P.s)) ∘ P.name) (P.name ⁻¹' tube n) (glow x (dawn y))

variable {P} {y : Heights n} {X : Palette W D} {v : Fin n → V} (B : PairedPanes P X v y)
/-- On-Slice Taylor agreement; a substantive port; not implied by equality just at t=0 values! -/
def PairedPanes.sameGround : Prop := ∀ x (h : x∈P.gap), (∀ i : Fin n, YM.time (x i)=0) →
    (B.original x h).extendF =ᶠ[𝓝 (glow x (dawn y))] (B.tilted x h).extendF

theorem PairedPanes.reaches (hx : B.sameGround) (x : Points n) (p : x∈P.gap) :
    (B.original x p).extendF =ᶠ[𝓝 (glow x (dawn y))] (B.tilted x p).extendF := by
  have HH : Continuous (@NearPair.name _ P) := (home n).comp ((P.switch.continuous.comp (cont_Re n)).prodMk (P.switch.continuous.comp (cont_sh n)))
  let q (t : unitInterval) := glow (plain x t) (dawn y)
  let w i := B.original _ (P.north p i)
  let z i := B.tilted _ (P.north p i)
  have he := Pane.propagate (south n) ((south n).preimage HH) q ((home n).comp
    (((cont_plain x).comp continuous_subtype_val).prodMk continuous_const))
    (fun t => ⟨B.permitted.first _,B.permitted.second _⟩) w z 0 1
  have hy := he.1 (hx _ _ (by simp [plain]))
  change (B.original (plain x 1) _).extendF =ᶠ[𝓝 (glow (plain x 1) (dawn y))] (B.tilted (plain x 1) _).extendF at hy
  let R (v : P.gap) : Prop := (B.original v.val v.2).extendF =ᶠ[𝓝 (glow v.val (dawn y))] (B.tilted v.val v.2).extendF
  change R (⟨x,p⟩ : P.gap); change R ⟨plain x 1,P.north p 1⟩ at hy
  rwa [show (⟨plain x 1,P.north p 1⟩ : P.gap)=(⟨x,p⟩ : P.gap) from Subtype.ext (tip x)] at hy

/-- local realization from each pane (full argument). Both at original x,
after change of names in tilted contour including positions and tests. -/
structure PairedPanes.Forms : Prop where
  body (x : Points n) (hx : x∈P.gap) : ∃ r>0, ∀ f : Joint n, HasCompactSupport ⇑f → tsupport f ⊆ ball x r →
    (D n).partialD (W.W n v) (dawn y) f= ∫ i, (B.original x hx).extendF (glow i (dawn y))*f i
  prime (x : Points n) (hx : x∈P.gap) : ∃ r>0, ∀ f : Joint n, HasCompactSupport ⇑f → tsupport f ⊆ ball x r →
    flipW ((D n).partialD (W.W n (v ∘ P.s)) (P.switch (dawn y))) P f= ∫ i,(B.tilted x hx).extendF (glow i (dawn y))*f i

theorem PairedPanes.forgets (hp : B.sameGround) (hx : B.Forms) : IsVanishingOn (fun i =>
    ((D n).partialD (W.W n v) (dawn y)-flipW ((D n).partialD (W.W n (v ∘ P.s)) (P.switch (dawn y))) P) i) P.gap := by
  let Q := (D n).partialD (W.W n v) (dawn y)
  let R := flipW ((D n).partialD (W.W n (v ∘ P.s)) (P.switch (dawn y))) P
  apply (Distn.general_open (Q-R) P.open_gap).2
  apply Set.disjoint_left.2
  intro x H hI
  obtain ⟨r,hr,hR⟩ := hx.body x H
  obtain ⟨s,hs,hS⟩ := hx.prime x H
  let g (i : Points n) := glow i (dawn y)
  have hv : Continuous g := (home n).comp (continuous_id.prodMk continuous_const)
  obtain ⟨k,hk,ht⟩ := Metric.mem_nhds_iff.mp ((hv.tendsto x).eventually (B.reaches hp x H))
  let t := min k (min r s)
  have he := (mem_dsupport_iff_not_isVanishingOn x).mp hI (ball x t) (mem_ball_self (lt_min hk (lt_min hr hs))) isOpen_ball
  apply he; apply (Distn.from_compact (Q-R)).2
  intro f hl hf; change Q f-R f=0; apply sub_eq_zero.2
  rw [show Q f= _ from hR f hf (hl.trans (ball_subset_ball ((min_le_right ..).trans (min_le_left r s)))),
    show R f= _ from hS f hf (hl.trans (ball_subset_ball ((min_le_right ..).trans (min_le_right r s))))]
  classical
  apply integral_congr_ae; filter_upwards with i
  by_cases h : f i=0
  · simp [h]
  rw [show (B.original x H).extendF (g i)= _ from ht (ball_subset_ball (min_le_left k (min r s)) (hl (subset_tsupport _ h)))]

theorem observes (X : Palette W D) (v : Fin n → V) (P : NearPair n) (p : (D n).Modified)
    (hc : ∀ u : Fin n → V, dsupport (Distn.fourier (W.W n u)) ⊆ coneM n)
    (h : ∃ y : ℕ → Heights n, Tendsto (dawn ∘ y) atTop (𝓝 0) ∧
      ∀ m : ℕ, ∃ B : PairedPanes P X v (y m), B.sameGround ∧ B.Forms) : IsVanishingOn (fun f =>
    (W.W n v - flipW (W.W n (v ∘ P.s)) P) f) P.gap := by
  obtain ⟨y,hy,hh⟩ := h
  choose B hb hB using hh
  have he : Tendsto (dawn ∘ y) atTop (𝓝[shores n] 0) := tendsto_nhdsWithin_iff.2 ⟨hy, Eventually.of_forall (fun i => (B i).permitted.here)⟩
  have ht : Tendsto (fun i => P.switch (dawn (y i))) atTop (𝓝[shores n] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall (fun i => (B i).permitted.there)⟩
    simpa only [Function.comp_def,map_zero] using (P.switch.continuous.tendsto 0 |>.comp hy)
  intro f hf
  let t : Joint n := along (P.switch).toContinuousLinearEquiv f
  have ha := ((D n).tends p (W.W n v) f _ (flat _)).tendsto.comp he
  have hw := ((D n).tends p (W.W n (v ∘ P.s)) t _ (flat _)).tendsto.comp ht
  change W.W n v f-W.W n _ _=0
  apply sub_eq_zero.2
  rw [(D n).flatD p (hc v)] at ha
  rw [(D n).flatD p (hc _)] at hw
  exact tendsto_nhds_unique_of_eventuallyEq ha hw (Eventually.of_forall (fun i =>
    sub_eq_zero.mp ((B i).forgets (hb i) (hB i) f hf)))

section C19
variable {F:InkWaves V}
open Complex Bid
/- Complex-linear maps on Full, including the complex boost at *fixed*
rapidity and the change of names. Careful: `reality` and `shade`
individually are only real-linear. -/

private lemma reality_add (x y : Full n) :
    reality (x + y) = reality x + reality y := by
  apply Points.flatten.injective
  ext i
  simp [reality]

private lemma shade_add (x y : Full n) :
    shade (x + y) = shade x + shade y := by
  apply Points.flatten.injective
  ext i
  simp [shade]

private lemma reality_smul (c : ℂ) (x : Full n) :
    reality (c • x) = c.re • reality x - c.im • shade x := by
  apply Points.flatten.injective
  ext i
  simp [shade, reality]

private lemma shade_smul (c : ℂ) (x : Full n) :
    shade (c • x) = c.re • shade x + c.im • reality x := by
  apply Points.flatten.injective
  ext i
  simp [shade, reality]

private lemma glow_ext {x y : Full n} (h : reality x = reality y)
    (k : shade x = shade y) : x = y :=
  (valley x).symm.trans (by rw [h, k, valley])

private def complexMap (A : Points n →ₗ[ℝ] Points n) : Full n →L[ℂ] Full n :=
  LinearMap.toContinuousLinearMap
    { toFun x := glow (A (reality x)) (A (shade x))
      map_add' x y := by
        apply glow_ext <;> simp [reality_add, shade_add]
      map_smul' c x := by
        apply glow_ext <;> simp [reality_smul, shade_smul] }

private def blocks (A : E4 →L[ℝ] E4) : Points n →ₗ[ℝ] Points n where
  toFun x := points fun i => A (x i)
  map_add' x y := PiLp.ext fun i => map_add A (x i) (y i)
  map_smul' c x := PiLp.ext fun i => map_smul A c (x i)

private lemma analytic_name (P : NearPair n) (x : Full n) :
    AnalyticAt ℂ P.name x :=
  (complexMap P.switch.toLinearEquiv.toLinearMap).analyticAt x

private lemma analytic_augment (e : Ray) (z : ℂ) (x : Full n) :
    AnalyticAt ℂ (augment e z) x := by
  let U : Full n →L[ℂ] Full n := ContinuousLinearMap.id ℂ _ +
    Complex.sinh z • complexMap (blocks e.crossT) +
    (Complex.cosh z - 1) • complexMap (blocks e.scalesT)
  have h : augment e z = ⇑U := rfl
  rw [h]
  exact U.analyticAt x

private lemma analytic_boost_path (e : Ray) (x : Full n) (z : ℂ) :
    AnalyticAt ℂ (fun w => augment e w x) z :=
  (analyticAt_const.add (Complex.analyticAt_sinh.smul analyticAt_const)).add
    ((Complex.analyticAt_cosh.sub analyticAt_const).smul analyticAt_const)

/- The change of names must intertwine the action also for the *tilted*
pane. We need this identity only at real rapidities. -/

private lemma augment_real (e : Ray) (t : ℝ) (x : Full n) :
    augment e (↑t) x = rect (e.boost t) x := by
  apply glow_ext
  · simp only [augment, reality_add, reality_smul, sinh_ofReal_im, sinh_ofReal_re,
      sub_im, sub_re, cosh_ofReal_im, cosh_ofReal_re, one_re, one_im, sub_zero,
      zero_smul, rect, re_glow]
    ext1 i
    simp [Ray.shift]
  · simp only [augment, shade_add, shade_smul, sinh_ofReal_im, sinh_ofReal_re,
      sub_im, sub_re, cosh_ofReal_im, cosh_ofReal_re, one_re, one_im, sub_zero,
      zero_smul, add_zero, rect, im_glow]
    ext1 i
    simp [Ray.shift]

private lemma name_rect (P : NearPair n) (A : Lorentz) (x : Full n) :
    P.name (rect A x) = rect A (P.name x) := by
  have h (u : Points n) :
      P.switch (togetherL A n u) = togetherL A n (P.switch u) := PiLp.ext fun _ => rfl
  simp only [NearPair.name, rect, re_glow, im_glow, h]


def emitAt (X : Palette W D) (x : Full n) :
    MultilinearMap ℂ (fun _ : Fin n => V) ℂ :=
  let A : Distn (Points n) →ₗ[ℂ] ℂ :=
    { toFun u := ((pref (Points n))⁻¹ : ℂ) * Distn.fourier u (X.lens n x)
      map_add' u v := by simp [mul_add]
      map_smul' c u := by simp [mul_left_comm] }
  A.compMultilinearMap (W.W n)


lemma emit_annual (X:Palette W D) (hX:X.FullBody F) (z:ℂ)
    (k: Fin n → ℕ)(B: (i:Fin n)→ Fin (k i)→V)(c:(i:Fin n)→ Fin (k i)→ℂ→ℂ)
    (u: ∀ i j, AnalyticAt ℂ (c i j) z) (p:ℂ→Full n) (h:AnalyticAt ℂ p z) (h':p z∈tube n) : AnalyticAt ℂ (fun w=> X.emit (fun i=> ∑ j,c i j w • B i j) (p w)) z:=by
 let E(w:ℂ)(b:(i:Fin n)→ Fin (k i)) : ℂ := X.emit (fun i=>B i (b i)) (p w); have he(w): X.emit (fun i=>∑ j,c i j w • B i j) (p w)=∑ j:(i:Fin n)→Fin (k i),(∏ i,c i (j i) w)* E w j:=by
    change emitAt X _ _ =_; rw [MultilinearMap.map_sum]; exact Finset.sum_congr rfl fun _ _=> MultilinearMap.map_smul_univ ..
 simp_rw [he]; exact Finset.analyticAt_fun_sum _ fun i _=> (Finset.analyticAt_fun_prod _ fun j _=> u j (i j)).mul ((hX.hol _ _ _ h').comp h)
private lemma exhibitAlong (R:Courts V) {X:Palette W D}
 (hX:X.FullBody F) (hTurn:X.Spun R)
    (v : Fin n → V) (e : Ray)
    (N : Full n → Full n) (hN : AnalyticOnNhd ℂ N univ)
    (hReal : ∀ (a : ℝ) l, N (augment e (↑a) l) = rect (e.boost a) (N l))
    (γ : ℝ → ℂ) (hγ : Continuous γ) (h0 : γ 0 = 0) {x : Full n} {t : ℝ} (ht : 0 ≤ t)
    (hend : N (augment e (γ t) x) ∈ tube n)
    (hpath : ∀ᶠ l in 𝓝[N ⁻¹' tube n] x, ∀ b : ℝ, b ∈ Icc 0 t →
      N (augment e (γ b) l) ∈ tube n) :
    Nonempty (Pane (X.emit v ∘ N) (N ⁻¹' tube n) x) := by

  choose k' B c hg hm using fun i=> R.weight_slot (v i) e
  let V' (z : ℂ)(i:Fin n):=∑ j,c i j z • B i j
  let Q (l : Full n) (z : ℂ) := X.emit (V' z) (N (augment e z l))
  refine ⟨⟨fun l => Q l (γ t), ?_, ?_⟩⟩
  · exact (hX.hol n (V' (γ t)) _ hend).comp (f := N ∘ augment e (γ t))
      ((hN _ (mem_univ _)).comp (f := augment e (γ t)) (analytic_augment e (γ t) x))
  filter_upwards [hpath, self_mem_nhdsWithin] with l hl hin
  let k := X.emit v (N l)
  change Q l (γ t) = k
  have ha' : AnalyticOnNhd ℂ (Q l) (γ '' Icc 0 t) := by
    rintro z ⟨b, hb, rfl⟩

    exact X.emit_annual hX (γ b) _ _ _ (fun i j=>hg i j _ (mem_univ _)) _ ((hN _ (mem_univ _)).comp (analytic_boost_path e l _)) (hl b hb)
  have he (r : ℝ) : Q l (↑r) = k := by
    have hV : V' (↑r) = fun i=> R.mi (e.boost r) (v i):= funext fun i=> hm i r
    change X.emit (V' _) (N (augment e _ l)) = _
    rw [hV, hReal]
    exact (hTurn n v (e.boost r) (N l) hin).symm
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), Q l z = k := by
    have hu : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[>] 0) (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · simpa using ((Complex.continuous_ofReal.tendsto 0).mono_left
          (nhdsWithin_le_nhds (s := Ioi 0)))
      filter_upwards [self_mem_nhdsWithin] with r hr
      change (r : ℂ) ≠ 0
      exact Complex.ofReal_ne_zero.mpr (mem_Ioi.mp hr).ne'
    intro hx
    obtain ⟨r, hr⟩ := (hu.eventually hx).exists
    exact hr (he r)
  have hg : EqOn (Q l) (fun _ => k) (γ '' Icc 0 t) :=
    ha'.eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const
      (isPreconnected_Icc.image γ hγ.continuousOn) ⟨0, left_mem_Icc.mpr ht, h0⟩ hfreq
  exact hg ⟨t, right_mem_Icc.mpr ht, rfl⟩


theorem moods (R:Courts V)(X:Palette W D)(hX:X.FullBody F)(hTurn:X.Spun R) (v:Fin n→V)(Z:NearPair n)(y:Heights n)(hy:Z.Fleck y)(ht:∀ x∈Z.gap, ∃ (e:Ray)(t:ℝ), travelable e Z t (glow x (dawn y))) : Nonempty (PairedPanes Z X v y):=by
  have hg (x : Points n) (hx : x ∈ Z.gap) :
      Nonempty (Pane (X.emit v) (tube n) (glow x (dawn y))) ∧
      Nonempty (Pane ((X.emit (v ∘ Z.s)) ∘ Z.name) (Z.name ⁻¹' tube n) (glow x (dawn y))) := by
    obtain ⟨e, t, hp, ho, hs, hpos, hneg⟩ := ht x hx
    constructor
    · exact exhibitAlong R hX hTurn v e id (fun _ _ => analyticAt_id)
        (augment_real e) (fun b => (b : ℂ)*Complex.I) (by fun_prop) (by simp) hp.le ho hpos
    exact exhibitAlong R hX hTurn (v ∘ Z.s) e Z.name (fun x _ => analytic_name Z x)
      (fun b l => by rw [augment_real, name_rect]) (fun b => -(b : ℂ)*Complex.I)
      (by fun_prop) (by simp) hp.le hs hneg
  exact ⟨⟨hy, fun x hx => Classical.choice (hg x hx).1,
    fun x hx => Classical.choice (hg x hx).2⟩⟩

end C19
end Palette
end YM.SatinWFixed
