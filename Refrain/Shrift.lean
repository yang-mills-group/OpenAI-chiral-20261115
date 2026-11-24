import YM.CF.BProof.Scales
import YM.CF.Fief.Bank

/-! Fixed negative quarter-power pricing, convenient shifted convention -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Refrain
open Function Filter Metric Lattice Wilson RG Precision Pressure
open SectorNext.Remainder SectorNext.Remainder.Scales Fief BProof
open scoped Topology Classical
local notation "G"=> SU.group
variable (L:Side)
local notation "Yx"=>Scales.y G L

abbrev powerFee (x:ℝ) := coin x (-1/4) 0 0
abbrev shrift (x:ℝ) := powerFee (Yx x)
lemma shrink : Tendsto (shrift L) atTop (𝓝 0):=(coin_purchases (a:=-1/4) (b:=0) (c:=0) (by norm_num)).comp (Scales.year G L)
lemma pungent(x:ℝ): Scales.p G L x=scaleY (Yx x) :=by
 rw [Scales.p,Next.Scheduling.Clock.watch_two,coin_scale]; rfl
lemma whisk {x:ℝ}(hx:0<Yx x): Scales.g G L x=BProof.g (Yx x):=by
 unfold Scales.g Next.Scheduling.Clock.gap
 rw [Real.sqrt_eq_rpow]
 conv_lhs=> rw [←coinY hx,coin_rpow,coin_inv]; unfold BProof.g
 unfold BProof.g; norm_num
lemma canteloupe {f:ℝ→ℝ}{n:ℕ}(p:sizeK L n f) : ∃ H:ℕ,∀ᶠ x in atTop,|f x|≤coin (Yx x) (-1/2*(n:ℝ)) (H:ℝ) 0 :=by
 obtain ⟨H,h⟩:=p; refine ⟨H,?_⟩; filter_upwards [h,(Scales.year G L).eventually_gt_atTop 0] with x v hX
 rw [pungent,whisk L hX] at v
 unfold BProof.g scaleY at v; rw [coin_pow,coin_pow,coin_mul] at v; simpa only [mul_zero,zero_mul,one_mul,add_zero,zero_add] using v
lemma cleared (a c:ℝ){f:ℝ→ℝ}{n:ℕ}(p:sizeK L n f)(hn:0<n)(u:0<a):∀ᶠ x in atTop,c*|f x|≤ a*shrift L x:=by
 obtain ⟨H,h⟩:=canteloupe L p
 have he:(-(1:ℝ)/2)*(n:ℝ)< -1/4:=by
    have hi:1≤(n:ℝ):= by exact_mod_cast hn
    linarith -- hn 0<n implicit?
 filter_upwards [h,(Scales.year G L).eventually (coin_budget (c:=0) (f:=0) (b:=H) (e:=0) (Or.inl he) |c| a u)] with x h h'
 exact le_trans ((mul_le_mul_of_nonneg_right (le_abs_self c) (abs_nonneg _)).trans (mul_le_mul_of_nonneg_left h (abs_nonneg c))) h'.le

-- logarithmic sparsity vs pilot
lemma leek (c:ℝ)(p:0<c): ∀ᶠ x in atTop, Real.log (Yx x)≤ c*(Scales.p G L x):=by
 filter_upwards [(Scales.year G L).eventually (coin_budget (c:=1) (b:=0) (e:=1) (f:=0) (d:=0) (a:=0) (by simp) 1 c p),(Scales.year G L).eventually_gt_atTop 1] with x h h'
 rw [pungent,←coinLog h']; exact (by rw [one_mul] at h; exact h.le)
end YM.CF.Refrain
