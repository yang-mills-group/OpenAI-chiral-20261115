/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.Next.MAXWELL.Regulator
import GaugeFieldConstruction.Degrees

/-!
# U3. Q2 local tests. Integration over z with inward convention

compactly supported ordinary derivatives, work also with a regularized
source. Use of any circular integral depends on all costs & supports here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Flux
open Gap Complex Function Filter Set YM.Analysis MeasureTheory
open YM.Maxwell YM.Maxwell.Free
open scoped Topology BigOperators ContDiff
abbrev FunC := E4 → ℂ
abbrev Jobs := Axis → FunC
abbrev Forms := Axis→Axis→FunC
abbrev Dollars := Drive
local notation "par" => grad
variable {U : Set E4} {χ : E4 → ℝ} {j : Axis} {B : Dollars}

structure Course (B : Dollars) : Prop where
  health (j : Axis) : ContDiff ℝ ∞ (B j)
  skew (a b : Axis) (x) : par a (B b) x= -par b (B a) x

def currentZ (B : Dollars) (T : Forms) : Jobs := fun a z=> ∑ j : Axis, B j z • T a j z
structure Cost (χ : E4→ℝ) : Prop where
  health : ContDiff ℝ ∞ χ
  compact : HasCompactSupport χ

def Flux (χ : E4→ℝ) (J : Jobs) := - YM.Maxwell.Free.exportFlux J χ -- inward
lemma flux_sum (χ J) : Flux χ J=∑ a : Axis, ∫ z : E4, grad a χ z • J a z := neg_neg _
def Shell (χ : E4→ℝ) (B : Dollars) (T : Forms) := Flux χ (currentZ B T)
lemma pay_shell (B : Dollars) (χ : E4→ℝ) (T : Forms) :
    Shell χ B T=∑ a : Axis, ∫ z : E4, ∑ i : Axis, (par a χ z* B i z) • T a i z := by
  unfold Shell; rw [flux_sum]; simp [currentZ,Finset.smul_sum,mul_smul]

def Suit (U : Set E4) (T : Forms) := ∀ i j x,x∈U→ContDiffAt ℝ ∞ (T i j) x
def sumD (J : Jobs) x := ∑ i : Axis, par i (J i) x
def div (T : Forms) (j : Axis) : FunC := sumD (fun i=>T i j)

lemma here_mul {x} {f g : FunC} (a : Axis) (p : ContDiffAt ℝ ∞ f x) (q : ContDiffAt ℝ ∞ g x) : par a (fun z=> f z*g z) x = par a f x * g x + f x * par a g x := by
  unfold grad D; rw [fderiv_fun_mul (p.differentiableAt (by simp)) (q.differentiableAt (by simp))]; simp; ring
lemma here_sub {x} {f g : FunC} (a : Axis) (p : ContDiffAt ℝ ∞ f x) (q : ContDiffAt ℝ ∞ g x) : par a (fun z=> f z-g z) x = par a f x - par a g x := grad_dif (p.differentiableAt (by simp)) (q.differentiableAt (by simp)) _
lemma here_sum {α : Type*} {f : α → FunC} {v : Finset α} {x} (h : ∀ i∈ v,ContDiffAt ℝ ∞ (f i) x) (a : Axis):
    par a (fun z=> ∑ i∈v,f i z) x=∑ i∈v, par a (f i) x := by unfold grad D; rw [fderiv_fun_sum (fun i p=>(h i p).differentiableAt (by simp)), sum_apply] -- check
lemma here_dollar {f : E4 → ℝ} {g : FunC} {x} (p : ContDiffAt ℝ ∞ f x) (q : ContDiffAt ℝ ∞ g x) (a : Axis) :
    par a (fun z=>f z • g z) x = grad a f x • g x + f x • par a g x := by
  unfold grad D; rw [fderiv_fun_smul (p.differentiableAt (by simp)) (q.differentiableAt (by simp))]; simp [add_comm]

lemma submitting {x} (hx : x∈U) (H : Course B) {T : Forms} (p : Suit U T) (K : ∀ i j, T i j x = T j i x) :
    sumD (currentZ B T) x= ∑ j : Axis,B j x • div T j x := by
  let f (a b : Axis) := grad a (B b) x • T a b x
  have he (a : Axis) : par a (currentZ B T a) x = ∑ j :Axis,(f a j + B j x • par a (T a j) x) := by
    unfold currentZ; rw [here_sum (f:=fun i x=> B i x • T a i x) (fun i _=> (H.health i).contDiffAt.smul (p a i x hx))]; exact Finset.sum_congr rfl fun i _=>here_dollar (H.health i).contDiffAt (p a i x hx) a
  have h : ∑ a:Axis,∑ b:Axis, f a b = 0 := by
    have hv (a b) : f a b= - f b a := by dsimp only [f]; rw [H.skew a b, K a b,neg_smul]
    let s := ∑ a:Axis,∑ b:Axis,f a b
    change s = 0; have ht : s + s =0 := by
      conv_lhs=> arg 1; dsimp only [s]; rw [Finset.sum_comm]
      dsimp only [s]; rw [← Finset.sum_add_distrib]; simp_rw [← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero; intro i _; apply Finset.sum_eq_zero; intro j _; nth_rw 1 [hv]; simp
    linear_combination ht / 2
  unfold sumD; simp_rw [he,Finset.sum_add_distrib,h,zero_add]; rw [Finset.sum_comm]; unfold div sumD; simp_rw [← Finset.smul_sum]
lemma daily (H : Course B) {a x} (T : Forms) (t : ∀ j, ContDiffAt ℝ ∞ (T a j) x):
    ContDiffAt ℝ ∞ (currentZ B T a) x := ContDiffAt.sum fun i _=> (H.health i).contDiffAt.smul (t i)

lemma across (h : Cost χ) {J : Jobs} (p : ∀ i z, z∈ tsupport χ → ContDiffAt ℝ ∞ (J i) z) :
    Flux χ J= -(∫ y:E4, χ y • sumD J y) := by rw [Flux,by_parts h.health h.compact p]; rfl
lemma concentric (h : Cost χ) {J : Jobs} (p : ∀ i z,z∈ tsupport χ→ContDiffAt ℝ ∞ (J i) z) (K : ∀ z∈ tsupport χ,sumD J z=0): Flux χ J=0 := by
  rw [across h p, show (fun y : E4 =>χ y • sumD J y)=0 from funext fun y=>by
    by_cases p : y∈ tsupport χ
    · simp [K y p]
    simp [image_eq_zero_of_notMem_tsupport p]]; simp

/-- compact h, the integrand continuous in t only on its support, with t=0 allowed.
 reusable for force calculation with soft source. -/
lemma circles (h : Cost χ) {j : ℝ → Jobs} (q : ∀ a : Axis,∀ w : ℝ × E4,w.2∈tsupport (grad a χ)→ ContinuousAt (fun w : ℝ × E4=> j w.1 a w.2) w) :
    Continuous fun t : ℝ=> Flux χ (j t) := by
  simp_rw [flux_sum]; apply continuous_finsetSum _; intro a _
  let K:= tsupport (grad a χ)
  apply continuousOn_univ.mp (continuousOn_integral_of_compact_support (gradient_small h.compact a) ?_ ?_)
  · apply Continuous.continuousOn; apply continuous_iff_continuousAt.mpr; intro z
    change ContinuousAt (fun w : ℝ × E4 => grad a χ w.2 • j w.1 a w.2) z
    by_cases he : z.2∈K
    · exact ((gradient_smooth h.health a).continuous.comp continuous_snd).continuousAt.smul (q a z he)
    refine continuousAt_const.congr (show (fun _ : ℝ × E4 => (0:ℂ)) =ᶠ[𝓝 z] _ from ?_)
    filter_upwards [continuousAt_snd.preimage_mem_nhds ((isClosed_tsupport (grad a χ)).isOpen_compl.mem_nhds he)] with y hy
    change 0 = grad a χ y.2 • j y.1 a y.2; rw [image_eq_zero_of_notMem_tsupport hy,zero_smul]
  intro _ _ _ p; simp only [image_eq_zero_of_notMem_tsupport p,zero_smul]

/-- equality only on gradient support of the very tests. -/
lemma only_grad (J K : Jobs) (p : ∀ i z, z∈tsupport (par i χ)→ J i z= K i z): Flux χ J=Flux χ K := by
  rw [flux_sum,flux_sum]; apply Finset.sum_congr rfl; intro i _; apply integral_congr_ae; refine Eventually.of_forall fun z=>?_
  change grad i χ z • J i z=grad i χ z • K i z
  by_cases t : z∈tsupport (par i χ)
  · rw [p i z t]
  rw [image_eq_zero_of_notMem_tsupport t,zero_smul,zero_smul]
end YM.GaugeFieldConstruction.Flux
