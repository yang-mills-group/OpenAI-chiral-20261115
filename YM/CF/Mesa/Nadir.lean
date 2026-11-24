import YM.CF.Matter.Rep
import Mathlib.MeasureTheory.Measure.Hausdorff

/-! Point omission for Lipschitz integer cubical patches. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mesa
open Function Set Filter MeasureTheory Measure Metric
open scoped Topology NNReal BigOperators InnerProductSpace ENNReal
abbrev Board (d:ℕ):= Fin d→ℝ
abbrev Peri (E:Type*) [NormedAddCommGroup E] := sphere (0:E) 1
variable {d:ℕ}
private lemma hei : (hausdorffMeasure (d:ℝ):Measure (Board d))=volume := by
  simpa using hausdorffMeasure_pi_real (ι:=Fin d)
lemma shadow (h:d≤3) : hausdorffMeasure 3 (Peri (Board d))=0 := by
  have he:(d:ℝ)≤3:=by exact_mod_cast h
  refine nonpos_iff_eq_zero.mp ((hausdorffMeasure_mono he _).trans (le_of_eq ?_))
  rw [hei]; exact addHaar_sphere_of_ne_zero _ _ one_ne_zero
lemma shade {f:Board d→Board 3}{K:ℝ≥0}(h:LipschitzOnWith K f (Peri (Board d)))(hp:d≤3) : ¬ ball 0 (1/4:ℝ) ⊆ f '' Peri (Board d):=by
  intro hc
  have hi:=h.hausdorffMeasure_image_le (d:=3) (by norm_num)
  rw [shadow hp,mul_zero] at hi
  have hx: (hausdorffMeasure 3 : Measure (Board 3))=volume:=by norm_num at *; exact hei -- fix
  rw [hx] at hi
  exact (not_le.mpr (Metric.measure_ball_pos volume (0:Board 3) (by norm_num : (0:ℝ)<1/4))) ((measure_mono hc).trans hi)
variable {n:Type*}[Fintype n][DecidableEq n]
def blink (i j:n) (u: Ket n):Board 3:=![ (u i).re,(u i).im,(u j).re ]
lemma blinking (i j:n) : ∃ K,LipschitzWith K (blink i j):=by
  let F : Ket n→ₗ[ℝ]Board 3:=⟨⟨blink i j,?add⟩,?scalar⟩
  case' add =>
    intro x y; ext k; fin_cases k<;> simp [blink]
  case' scalar =>
    intro c x; ext k; fin_cases k <;> simp [blink]
  exact ⟨_,F.toContinuousLinearMap.lipschitz⟩
lemma touching (i j:n)(h:i≠j) : ball 0 (1/4:ℝ)⊆ blink i j '' Peri (Ket n):=by
  rintro z hz
  rw [Metric.mem_ball,dist_zero_right] at hz
  let E:ℝ:= z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2
  have hb (i:Fin 3) := lt_of_le_of_lt (norm_le_pi_norm z i) hz
  have hE : E≤1 := by
    have hc (i:Fin 3) := abs_lt.mp (show |z i| < 1/4 from hb i); have h0:=hc 0; have h1:=hc 1; have h2:=hc 2
    unfold E; nlinarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2]
  let x:= EuclideanSpace.single (𝕜:=ℂ) i (⟨z 0,z 1⟩:ℂ)
  let y:= EuclideanSpace.single (𝕜:=ℂ) j (⟨z 2,Real.sqrt (1-E)⟩:ℂ)
  refine ⟨x+y,?_,?_⟩
  · rw [mem_sphere,dist_zero_right]
    apply sq_eq_sq₀ (norm_nonneg _) zero_le_one|>.mp
    rw [← inner_self_eq_norm_sq (𝕜:=ℂ)]; have he:= Real.sq_sqrt (sub_nonneg.mpr hE)
    simp only [inner_add_left,inner_add_right]; unfold x y; simp only [EuclideanSpace.inner_single_left]; simp [Complex.mul_re,h,h.symm] -- check star
    unfold E at *; nlinarith
  ext k; fin_cases k <;> simp [blink,x,y,h,h.symm]
lemma misses (i j:n)(h:i≠j){f:Board d→Ket n}{K:ℝ≥0}(ht:LipschitzOnWith K f (Peri (Board d)))(hp:d≤3) : ∃ u:Ket n, u∈Peri (Ket n) ∧ u ∉ f '' Peri (Board d) := by
  by_contra! hh
  obtain ⟨J,hJ⟩:= blinking i j
  refine shade (hJ.comp_lipschitzOnWith ht) hp ?_
  rw [image_comp]
  exact (touching i j h).trans (image_mono fun x hx=>hh _ hx)
end YM.CF.Mesa
