/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SU5.Registration.Ink.Tolls
import YM.Work.C05
/-! General field module adaption, reusing slope proofs from pinned C05. -/
set_option autoImplicit false
noncomputable section
namespace YM.SatinWFixed.InkWaves
open Boundary Function Set Filter MeasureTheory LineDeriv
open Work.C05 (ray_mem continuous_of_tendsto_slope tendsto_exp_slope clock_hat)
open scoped ContDiff Topology BigOperators FourierTransform InnerProductSpace
variable {n : ℕ}
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (F : InkWaves V)
variable {v : Fin n → V}

def psiL (h : F.Bounds) (v : Fin n → V) (y : Heights n) (hy : y ∈ east n) : Joint n →ₗ[ℝ] ℂ where
  toFun := F.psi v y
  map_add' f g := by
    unfold InkWaves.psi; rw [← integral_add (h n v y hy f) (h n v y hy g)]
    congr 1; ext x; exact mul_add ..
  map_smul' a f := by
    change F.psi v y (a • f) = a • F.psi v y f
    unfold InkWaves.psi; rw [← integral_smul]; congr 1; ext x; exact mul_smul_comm a _ (f x)

lemma tendsto_psi (hb : F.Bounds) (ha : F.Along) (hl : F.Lines) (hp : F.Breathes)
    {Z : Type*} {l : Filter Z} {u : Z → Heights n} {g : Z → Joint n} {f : Joint n} {a : ℂ}
    (hu : ∀ᶠ t in l, u t ∈ east n) (hg : Tendsto g l (𝓝 f))
    (ht : Tendsto (fun t => F.psi v (u t) f) l (𝓝 a)) :
    Tendsto (fun t => F.psi v (u t) (g t)) l (𝓝 a) := by
  obtain ⟨m,C,_,hc⟩ := hp n v
  obtain ⟨h0,hcont⟩ := Waves.tolls (n := n) m C
  have htoll : Tendsto (fun t => Waves.toll (g t - f) C m) l (𝓝 0) := by
    rw [← h0]
    apply (hcont.tendsto 0).comp
    simpa using hg.sub (tendsto_const_nhds (x := f))
  have hh : Tendsto (fun t => F.psi v (u t) (g t - f)) l (𝓝 0) := by
    apply squeeze_zero_norm' ?_ htoll
    filter_upwards [hu] with t h
    rw [← F.meant ha hl _ _ h _ m]
    exact F.cost hc _ (bigger h) _
  rw [← zero_add a]
  apply (hh.add ht).congr'
  filter_upwards [hu] with t h
  change psiL F hb v (u t) h (g t - f) + F.psi .. = _
  rw [map_sub, show psiL F hb v (u t) h f = F.psi v (u t) f from rfl, sub_add_cancel]; rfl

lemma hasDerivAt_zero_psi (hb : F.Bounds) (ha : F.Along) (hl : F.Lines) (hp : F.Breathes)
    (v : Fin n → V) (y : Heights n) (hy : y ∈ east n) (f : ℝ → Joint n) (s : ℝ) (hs : 0 < s)
    (hd : Tendsto (slope f s) (𝓝[≠] s) (𝓝 (- Waves.clock y (f s)))) :
    HasDerivAt (fun t : ℝ => F.psi v (t • y) (f t)) 0 s := by
  have lines (g : Joint n) : HasDerivAt (fun t : ℝ => F.psi v (t • y) g)
      (F.psi v (s • y) (Waves.clock y g)) s := by
    simpa using hl n v g 0 y s (by simpa using ray_mem hy hs)
  have hu : ∀ᶠ t in 𝓝[≠] s, t • y ∈ east n := (eventually_nhdsWithin_of_eventually_nhds (lt_mem_nhds hs)).mono
    (fun _ h => ray_mem hy h)
  have H := tendsto_psi F hb ha hl hp hu hd ((lines (- Waves.clock y (f s))).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  rw [show F.psi v (s • y) (- Waves.clock y (f s)) = -(F.psi v (s • y) (Waves.clock y (f s))) from
    map_neg (psiL F hb v _ (ray_mem hy hs)) _] at H
  rw [hasDerivAt_iff_tendsto_slope, ← neg_add_cancel (F.psi v (s • y) (Waves.clock y (f s)))]
  apply (H.add (lines (f s)).tendsto_slope).congr'
  filter_upwards [hu] with t ht
  simp only [slope_def_module]
  change psiL F hb v _ ht _ + _ = _
  rw [map_smul, map_sub, smul_sub, smul_sub, smul_sub]
  change (t-s)⁻¹ • F.psi v _ _ - (t-s)⁻¹ • F.psi v _ _ + (_ - _) = _
  abel

/-- Absolute-coordinate strict height Fourier transform tested with compact
support after exponential multiplication; the original surface is kept. -/
theorem clock_appointed (W : WView V) (pp : F.Breathes) (hl : F.Lines) (ha : F.Along)
 (hw : F.NonTangentialFree W) : F.during W:= by
  intro n v y hy f hf
  let d := dawn y
  let K (t : ℝ) : Joint n := lifts (t • d) f hf
  let k := fun t => Probe.hat (K t)
  have hk (s : ℝ) : Tendsto (slope k s) (𝓝[≠] s) (𝓝 (-Waves.clock y (k s))) := by
    have he := tendsto_exp_slope d f hf K (by intro t x; simp [K, real_inner_smul_left]) s
    rw [clock_hat, neg_neg]
    apply (Probe.hat.continuous.continuousAt.tendsto.comp he).congr'
    exact Eventually.of_forall fun t => ((Probe.hat.restrictScalars ℝ).toLinearMap.slope_comp K s t).symm
  have hd s (hs : 0 < s) := hasDerivAt_zero_psi F hw.int ha hl pp v y hy k s hs (hk s)
  let A (s : ℝ) := F.psi v (s • y) (k s)
  have const t (ht : 0 < t) : A t = A 1 := by
    refine (convex_Ioi (𝕜 := ℝ) (0:ℝ)).is_const_of_fderivWithin_eq_zero
      (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt) (fun s hs => ?_) ht (show (0:ℝ)<1 from zero_lt_one)
    rw [fderivWithin_of_isOpen isOpen_Ioi hs, (hd s hs).hasFDerivAt.fderiv, ContinuousLinearMap.toSpanSingleton_zero]
  have h0 : k 0 = Probe.hat f := by
    change Probe.hat (lifts _ f hf) = _
    congr 1; ext1 x; simp
  have hlim : Tendsto A (𝓝[>] 0) (𝓝 (W.W n v (k 0))) :=
    tendsto_psi F hw.int ha hl pp (Eventually.mono self_mem_nhdsWithin (fun t ht => ray_mem hy (show 0<t from ht)))
      (((continuous_of_tendsto_slope _ _ hk).tendsto 0).mono_left nhdsWithin_le_nhds) ((F.exposed W hw).profile n v y hy (k 0))
  rw [h0] at hlim
  have hu : Tendsto A (𝓝[>] 0) (𝓝 (A 1)) := tendsto_const_nhds.congr'
    (Eventually.mono self_mem_nhdsWithin (fun t ht => (const t (show 0<t from ht)).symm))
  simpa [A, k, K] using tendsto_nhds_unique hlim hu

end YM.SatinWFixed.InkWaves
