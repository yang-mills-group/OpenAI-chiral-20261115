import YM.CF.Vp929.Analysis.Stencil
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Measure
set_option autoImplicit false
noncomputable section
namespace YM.CF.VolumeRate
open Set Filter Complex MeasureTheory Metric

local notation "M"=> widthS
variable {n:ℕ}{t y:ℝ}{z:ℂ}
def Ledge (n:ℕ)(t y:ℝ):Set ℂ:={z|y/2+(widthS n+3)*t<z.re ∧ z.re<2*y-(widthS n+3)*t∧ |z.im|< t}
theorem ledge_open : IsOpen (Ledge n t y):= IsOpen.inter (isOpen_lt continuous_const Complex.continuous_re) (IsOpen.inter (isOpen_lt Complex.continuous_re continuous_const) (isOpen_lt Complex.continuous_im.abs continuous_const))
local notation "ν"=> ball z.re t
abbrev limiter (z:ℂ)(t:ℝ)(y:ℝ):= if |y-z.re| ≤ t then y else z.re
abbrev centers (z:ℂ)(t:ℝ):= ae (volume.restrict (Metric.ball z.re t))
def pillar (n:ℕ)(z:ℂ)(t:ℝ)(y:ℝ): panel n→ℝ:= fun i=> wooden n (limiter z t y) t i
variable (hm:z∈Ledge n t y)
include hm
lemma Ledge.pos : 0<t:= lt_of_le_of_lt (abs_nonneg _) hm.2.2
lemma Ledge.real : y/2≤ z.re ∧ z.re ≤2*y:= by constructor<;> have h:((widthS n+3):ℝ)*t>0:=mul_pos (by positivity) (Ledge.pos hm) <;> linarith [hm.1,hm.2.1]
omit hm
lemma nearby_r : ‖z-(z.re:ℂ)‖=|z.im|:= by
 rw [show z-(z.re:ℂ)=↑z.im * Complex.I from by apply Complex.ext <;> simp]; simp [norm_mul]
lemma Ledge.neBot (h:0<t): (centers z t).NeBot:= by rw [centers,ae_neBot,Ne,Measure.restrict_eq_zero]; exact (Metric.measure_ball_pos volume z.re h).ne'
lemma Ledge.clamp(x:ℝ)(h:0<t): |limiter z t x - z.re| ≤ t:= by unfold limiter; split; assumption; rw [sub_self,abs_zero]; exact h.le
lemma Ledge.centerBasis (x:Set ℝ)(h:x∈ ae (volume:Measure ℝ))(i: panel n): ∀ᶠ y' in centers z t,pillar n z t y' i ∈ x:= by
 let f(y:ℝ):= wooden n y t i; have hx:MeasurePreserving f volume volume:= (measurePreserving_add_right volume _)
 filter_upwards [(ae_restrict_mem Metric.isOpen_ball.measurableSet : ∀ᶠ y' in centers z t,y'∈Metric.ball z.re t), ae_restrict_of_ae (show ∀ᶠ y' in ae (volume:Measure ℝ), f y' ∈ x from hx.quasiMeasurePreserving.tendsto_ae h)] with y hy hv; change f (limiter z t y)∈x; unfold limiter; rw [if_pos (by simpa only [← Real.dist_eq] using (Metric.mem_ball.mp hy).le)]; exact hv
lemma Ledge.near (h:0<t){b:ℝ} (i:panel n): |wooden n b t i-b| ≤ M n * t:= by
 unfold wooden; rw [add_sub_cancel_left,abs_mul,abs_of_nonneg h.le]; refine mul_le_mul_of_nonneg_right (abs_le.mpr ⟨?_,?_⟩) h.le
 · linarith [Nat.cast_nonneg (α:=ℝ) i.val]
 have h:=Finset.mem_range.mp i.prop; have p:i.val ≤ 2*M n:= Nat.le_of_lt_succ h; have u:=Nat.cast_le (α:=ℝ).mpr p; push_cast at u; linarith
include hm
lemma Ledge.fence (x:ℝ): ‖z-(limiter z t x:ℂ)‖≤ 2*t:= by
 let u:= limiter z t x; let z0:ℂ:= z.re; have p:‖z0-u‖≤t:=by rw [norm_sub_rev]; exact le_trans (le_of_eq (by change ‖(u:ℂ)-(↑z.re:ℂ)‖ = |u-z.re|; simp only [← Complex.ofReal_sub,norm_real,Real.norm_eq_abs])) (Ledge.clamp x (Ledge.pos hm))
 have hx := norm_sub_le_norm_sub_add_norm_sub z z0 (u:ℂ); exact hx.trans (by unfold z0 at *; rw [nearby_r]; linarith [hm.2.2])
lemma Ledge.pillar_b (x:ℝ)(i:panel n): let b:=pillar n z t x i; y/2 ≤ b∧ b≤ 2*y ∧ ‖z-(b:ℂ)‖ ≤ (widthS n+3:ℝ)*t := by
 intro b; let v:=limiter z t x; have hv := (Ledge.pos hm); have hr:|b-v| ≤ M n*t:= Ledge.near hv i; have hb:|v-z.re| ≤ t:= Ledge.clamp x hv
 obtain ⟨u,w⟩:= abs_le.mp hr; obtain ⟨a,c⟩:=abs_le.mp hb
 refine ⟨by linarith [hm.1],by linarith [hm.2.1],?_⟩; have he:‖z-(v:ℂ)‖ ≤ 2*t:= Ledge.fence hm x; have hh:= norm_sub_le_norm_sub_add_norm_sub z (v:ℂ) (b:ℂ); rw [norm_sub_rev (↑v:ℂ),←Complex.ofReal_sub,norm_real,Real.norm_eq_abs] at hh; linarith
lemma Ledge.plea (x:ℝ) : ∃ gw:ℂ, ‖gw‖ ≤ 2∧ (limiter z t x:ℂ)+gw*t=z:= by
 let V:ℂ:=limiter z t x
 refine ⟨(z-V)/(t:ℂ),?_ ,?_⟩; swap
 · rw [div_mul_cancel₀ _ (ofReal_ne_zero.mpr (Ledge.pos hm).ne')]; ring
 rw [norm_div,norm_real,Real.norm_of_nonneg (Ledge.pos hm).le]; exact (div_le_iff₀ (Ledge.pos hm)).mpr (Ledge.fence hm x)
end YM.CF.VolumeRate
