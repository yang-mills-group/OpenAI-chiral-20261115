import YM.Gauge.Size
import YM.Gauge.Nearest
import YM.Gauge.Curvature
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
Group-side prices use **chord** on the faithful matrix, not `dist` on some other norm
choice. Normalize ball densities with the same probability Haar also for all noises. Use
ambient packing variant of the Haar ball cost (still pays eq:B-ang-M).
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof
open Gauge NormedSpace MeasureTheory Set Function Filter Metric
open scoped Matrix.Norms.Frobenius BigOperators Topology ContDiff ENNReal
variable {G : Gauge}
-- G implicit infer from? abbreviations El, might fail. use explicit
def cd (G : Gauge) (u v : G.El) := G.chord (u⁻¹*v)
variable (G) (u v w W : G.El)

@[simp] lemma cd_nonneg : 0 ≤ cd G u v := G.chord_nonneg _
lemma cd_norm : cd G u v=‖G.mat u-G.mat v‖/G.colorScale := by
 unfold cd chord; rw [← G.mat_one,← inv_mul_cancel u,G.mat_mul,G.mat_mul,← mul_sub,mul_frob_eq _ _ (G.mat_star_mul _),norm_sub_rev]; rfl
lemma mat_norm_dist : dist (G.mat u) (G.mat v) = cd G u v * G.colorScale := by rw [cd_norm,div_mul_cancel₀ _ G.colorScale_pos.ne',dist_eq_norm]
lemma cd_symm : cd G u v=cd G v u := by rw [cd_norm,cd_norm,norm_sub_rev]
@[simp] lemma cd_one : cd G 1 u=G.chord u := by simp [cd]
@[simp] lemma cd_self : cd G u u=0 := by simp [cd]
@[simp] lemma cd_mul_left : cd G (u*v) (u*w)=cd G v w := by simp [cd]
@[simp] lemma cd_mul_right : cd G (v*u) (w*u)=cd G v w := by
 rw [cd_norm,cd_norm, mat_mul,mat_mul,←sub_mul,frob_mul_eq _ _ (G.mat_mul_star u)]
lemma cd_triangle : cd G u w ≤ cd G u v+cd G v w := by
 rw [cd_norm,cd_norm,cd_norm,← add_div]; exact div_le_div_of_nonneg_right (norm_sub_le_norm_sub_add_norm_sub ..) G.colorScale_pos.le
lemma cd_perturb : cd G (u*v) (w*W) ≤ cd G u w + cd G v W := (cd_triangle G _ (w*v) _).trans (by simp)
@[simp] lemma cd_inv : cd G u⁻¹ v⁻¹=cd G u v := by rw [← cd_mul_left G u, mul_inv_cancel, ← cd_mul_right G v,_root_.mul_assoc,inv_mul_cancel,mul_one,one_mul,cd_symm]
@[simp] lemma cd_zero : cd G u v=0 ↔ u=v := by simp only [cd_norm,div_eq_zero_iff,G.colorScale_pos.ne',or_false,norm_eq_zero,sub_eq_zero,G.mat_injective.eq_iff]
lemma cd_pos : 0< cd G u v ↔ u ≠ v := by rw [lt_iff_le_and_ne,ne_comm,ne_eq,cd_zero,and_iff_right (cd_nonneg ..)]
@[fun_prop] lemma continuous_cd : Continuous (fun x : G.El × G.El => cd G x.1 x.2) := by unfold cd; fun_prop
lemma norm_le_scale {x y : G.El} {h : ℝ} : cd G x y ≤ h ↔ ‖G.mat x-G.mat y‖≤h*G.colorScale := by rw [cd_norm]; exact div_le_iff₀ G.colorScale_pos

/-- Chord ball (closed). -/
def Shell (r : ℝ) (u : G.El) := (fun v => u⁻¹*v) ⁻¹' G.shell r
@[simp] lemma mem_shell (r : ℝ) : v ∈ Shell G r u ↔ cd G u v ≤ r := Iff.rfl
lemma shell_set (r : ℝ) : MeasurableSet (Shell G r u) := (measurable_const_mul _ ) (G.shell_meas r)

lemma ballHaar (r : ℝ) : G.probHaar (Shell G r u) = G.probHaar (G.shell r) := (measurePreserving_mul_left G.probHaar u⁻¹).measure_preimage (G.shell_meas _).nullMeasurableSet
abbrev matDim (G : Gauge) := Module.finrank ℝ G.Mat
def ballH (r : ℝ) := (G.probHaar.real (G.shell r))⁻¹
lemma ball_positive {r : ℝ} (h : 0 < r) (u : r ≤ 1) : 0 < ballH G r := inv_pos.mpr ((show 0<(r/4)^matDim G by positivity).trans_le (G.shell_ge r h u))
lemma ball_pays {r : ℝ} (h : 0<r) (u : r ≤ 1) : ballH G r ≤ (4/r)^matDim G := by
 apply le_trans (inv_anti₀ (by positivity) (G.shell_ge r h u)); rw [←inv_pow,inv_div]

def density (r : ℝ) (u v : G.El) : ℝ := indicator (Shell G r u) (fun _ => ballH G r) v
lemma density_c (r : ℝ) : Measurable (Function.uncurry (density G r)) := by
 classical
 let S:= {p : G.El × G.El|cd G p.1 p.2 ≤ r}; have hs:MeasurableSet S:=(isClosed_le (continuous_cd G) continuous_const).measurableSet
 convert measurable_const.indicator (f:=fun _=>ballH G r) hs using 1
 ext1 x; unfold Function.uncurry density Set.indicator; congr!
lemma density_apply (r : ℝ) : density G r u v=if cd G u v ≤ r then ballH G r else 0 := by classical by_cases h:cd G u v ≤ r <;> simp [density,indicator,h]
lemma density_both (r : ℝ) {a b : G.El} : density G r (a*u*b) (a*v*b) = density G r u v := by simp only [density_apply,cd_mul_left,cd_mul_right]
@[simp] lemma density_inv (r : ℝ) : density G r u⁻¹ v⁻¹=density G r u v := by simp only [density_apply,cd_inv]
lemma density_pay {r : ℝ} (h : 0<r) (a : r≤1) : 0≤density G r u v ∧ density G r u v ≤ (4/r)^matDim G := by
 rw [density_apply]; split
 · exact ⟨(ball_positive G h a).le,ball_pays G h a⟩
 exact ⟨le_rfl,by positivity⟩
lemma density_unit {r : ℝ} (h : 0<r) (a : r ≤1) : ∫ v,density G r u v ∂G.probHaar=1 := by
 unfold density
 rw [integral_indicator (shell_set ..),setIntegral_const,measureReal_def,ballHaar]; have hp:= ball_positive G h a; unfold ballH Measure.real at hp ⊢; rw [smul_eq_mul,mul_inv_cancel₀ (inv_pos.mp hp).ne']

lemma cd_nhds : Tendsto (cd G u) (𝓝 u) (𝓝 0) := by
 rw [← cd_self G u]; apply Continuous.tendsto; unfold cd; fun_prop
lemma cd_mem {r : ℝ} (h : 0<r) : ∀ᶠ v in 𝓝 u, cd G u v < r := cd_nhds G u (gt_mem_nhds h)
lemma cd_open {p : G.El → Prop} (h : ∀ᶠ v in 𝓝 u,p v) : ∃ r : ℝ,0<r∧∀ v,cd G u v≤r→p v := by
 let S := {v | p v}; obtain ⟨T, ht, hT, hf⟩ := _root_.mem_nhds_iff.mp h
 obtain ⟨L,hL,he⟩:= (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.isInducing.isOpen_iff.mp hT
 obtain ⟨r,hr,hq⟩:= Metric.mem_nhds_iff.mp (hL.mem_nhds (show G.mat u∈ L from by simpa only [←mem_preimage,he] using hf))
 refine ⟨r/(2*G.colorScale),by have := G.colorScale_pos; positivity, fun v hv => ht ?_⟩
 rw [← he]; apply hq; rw [Metric.mem_ball, dist_comm,mat_norm_dist]; have := G.colorScale_pos; rw [le_div_iff₀ (by positivity)] at hv; linarith
end YM.CF.BProof
