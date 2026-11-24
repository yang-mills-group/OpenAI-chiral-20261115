/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SU5.Registration.Ink.WavePort
import YM.Work.C06
/-! General field module adaptation from pinned C06. -/
set_option autoImplicit false
noncomputable section
namespace YM.SatinWFixed.InkWaves

open Filter Set Function Distribution MeasureTheory Boundary
open scoped Topology BigOperators ContDiff InnerProductSpace
open Work.C06 (lift_falls)
variable {n : ℕ}

private lemma support_lifts (u : Points n) (f : Joint n) (hf : HasCompactSupport ⇑f) :
    tsupport (lifts u f hf) ⊆ tsupport f :=
  tsupport_mul_subset_right

private lemma sunrise_smul {y : Heights n} (hy : y ∈ sunrise n) {t : ℝ} (ht : 0 ≤ t) :
    t • y ∈ sunrise n := fun _ _ h => mul_le_mul_of_nonneg_left (hy h) ht

private lemma dawn_add (x y : Heights n) : dawn (x+y) = dawn x + dawn y := by
  ext1 i
  apply Mink.ext_by <;> simp [dawn, place]

private lemma dawn_smul (x : Heights n) (t : ℝ) : dawn (t • x) = t • dawn x := by
  ext1 i
  apply Mink.ext_by <;> simp [dawn, place]

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (F : InkWaves V) (W : WView V)

private lemma patch (hF : F.Breathes) (hp : F.during W)
    (v : Fin n → V) {y : Heights n} (hy : y ∈ sunrise n) :
    IsVanishingOn (Distn.fourier (W.W n v)) {x : Points n | inner ℝ (dawn y) x < -1} := by
  rw [Distn.from_compact]; intro f hs hf
  let Y (t : ℝ) := t • y + (1 : ℝ) • rate n
  let z := (1 : ℝ) • rate n
  let l (t : ℝ) := lifts (dawn (Y t)) f hf
  have hu : Tendsto l atTop (𝓝 0) := by
    let g := lifts (dawn z) f hf
    have hg : HasCompactSupport ⇑g := remains ..
    have hx (x) (H : x ∈ tsupport g) : inner ℝ (dawn y) x ≤ -1 :=
      le_of_lt (hs (support_lifts (dawn z) f hf H))
    refine (lift_falls (dawn y) g hg hx).congr fun t => ?_
    ext1 x
    change lifts (t • dawn y) g hg x = lifts (dawn (t • y + z)) f hf x
    rw [dawn_add, dawn_smul]
    simp only [g, rises, inner_add_left, Complex.ofReal_add, Complex.exp_add, mul_assoc]
  obtain ⟨m, C, -, H⟩ := hF n v
  have hw : Tendsto (fun t => weight (Probe.hat (l t))) atTop (𝓝 0) := by
    let A : Joint n →L[ℂ] Joint n := Probe.hat
    have hv := (((weight_cont (n := n)).comp A.continuous).tendsto 0).comp hu
    simpa only [Function.comp_def, map_zero, feath] using hv
  have hle : ‖Distn.fourier (W.W n v) f‖ ≤ C * (0 : ℝ) := by
    apply ge_of_tendsto (hw.const_mul C)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have he := sunrise_smul hy ht
    have hy' : Y t ∈ east n := dawns he zero_lt_one
    rw [hp n v (Y t) hy' f hf]
    have h1 : (1 : ℝ) ∈ Ioc (0 : ℝ) 1 := ⟨zero_lt_one, le_rfl⟩
    have h := F.beam m C H he (Probe.hat (l t)) h1
    simp only [one_pow, one_mul] at h
    exact h
  rw [mul_zero] at hle
  exact norm_le_zero_iff.mp hle

theorem shiny_half (hF : F.Breathes) (hp : F.during W) (_hb : F.Bounds) : W.cone_tests := by
  -- `Bounds` need not be invoked explicitly: `during` already gives the identity,
  -- and `beam` from the library can estimate the pairing with just the power bound. (`Bounds` in
  -- our hypotheses does ensure that the integrals used here, at strict heights, are genuine.)
  intro n v p hs
  apply mem_iInter.mpr
  rintro ⟨y, hy⟩
  change 0 ≤ inner ℝ (dawn y) p
  by_contra! hx
  let t := 2 / (-inner ℝ (dawn y) p)
  have ht : 0 < t := div_pos (by norm_num) (neg_pos.mpr hx)
  let s := {x : Points n | inner ℝ (dawn (t • y)) x < -1}
  have hh : IsOpen s := isOpen_lt (by fun_prop) continuous_const
  apply Set.disjoint_left.mp ((Distn.general_open _ hh).mp
    (patch F W hF hp v (sunrise_smul hy ht.le))) _ hs
  change inner ℝ (dawn (t • y)) p < -1
  rw [dawn_smul, real_inner_smul_left]
  have he : t * inner ℝ (dawn y) p = -2 := by
    dsimp only [t]
    field_simp [hx.ne]
  rw [he]
  norm_num

end YM.SatinWFixed.InkWaves
