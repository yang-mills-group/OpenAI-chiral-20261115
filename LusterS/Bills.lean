import Refrain.Shrift
import YM.CF.BProof.PL
import Refrain.Shrift
import YM.SU5.Gleam.Innate
import Refrain.Kernel
/-! # Sparse defect treatment under outer-threshold tree purchase -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.flexible false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Gleam.Luster
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ v' ν θ ω':ℝ}{U:Config G n}{A:Support c}{m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
variable {X Y:fieldDir G n 1}{D:Finset (Cell n)}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)(D':LocalRatio J)

namespace Almanac
open CF.BProof Asymptotics
local notation "p_"=>scaleY
variable {a b a' b':ℝ}{f g:ℝ→ℝ}
-- Stronger pricing than PL. `grade` ignores fixed powers of p_ by retaining budget over direct X
-- Convenient using norm being paid by ONE coin monomial times constant (absorb in b).
def Grade (a:ℝ)(f:ℝ→ℝ):Prop:=∃ b:ℝ,∀ᶠ x in atTop, |f x| ≤ coin x a b 0
namespace Grade
lemma cash (hf:Grade a f)(h:∀ᶠ x in atTop,|g x| ≤|f x|):Grade a g:=by obtain ⟨b,hf⟩:=hf; exact ⟨b,(hf.and h).mono (fun i h=> h.2.trans h.1)⟩
lemma budget (hf:Grade a f) (b c h:ℝ)(ha:a<b)(p:0<h):∀ᶠ x in atTop,|f x|≤h*coin x b c 0:=by
 obtain ⟨w,hf⟩:=hf; filter_upwards [hf,coin_budget (a:=a) (b:=w) (c:=0) (d:=b) (e:=c) (f:=0) (Or.inl ha) 1 h p] with x u v
 rw [one_mul] at v; exact u.trans v.le
lemma grow (hf:Grade a f)(ha:a≤b):Grade b f:=by
 rcases ha.eq_or_lt with h|h; · subst b; exact hf
 exact ⟨0,(hf.budget b 0 1 h zero_lt_one).mono fun x h=>one_mul (coin x b 0 0) ▸ h⟩
lemma stock(a b:ℝ):Grade a (fun x=>coin x a b 0):=⟨b,Eventually.of_forall (fun _=>by rw [abs_of_nonneg (coin_pos ..).le])⟩
lemma roots{α:ℝ}(p:Grade α f)(ha:α<0):Tendsto f atTop (𝓝 0):=by
 obtain ⟨b,hf⟩:=p
 exact squeeze_zero_norm' (f:=f) hf (coin_purchases (b:=b) (c:=0) (Or.inl ha))
lemma fromLog (hf:PL f):Grade 0 f:=⟨1,(coin_strongLt (b:=1) (by simp) hf).mono fun x h=> h.le⟩
lemma block (c:ℝ):Grade 0 (fun _=> c):= fromLog (PL.const c)
lemma radiusBill:Grade 0 (fun x=>(radiusB x:ℝ)):=by apply fromLog; exact PL.ceil (PL.log_y.pow 2) (Eventually.of_forall fun i=>sq_nonneg _)
lemma radius_log:PL (fun x=>(radiusB x:ℝ)):= PL.ceil (PL.log_y.pow 2) (Eventually.of_forall fun i=>sq_nonneg _)
lemma mul (hf:Grade a f)(hg:Grade b g):Grade (a+b) (fun x=>f x*g x):=by
 obtain ⟨u,p⟩:=hf; obtain ⟨v,q⟩:=hg; refine ⟨u+v,?_⟩; filter_upwards [p,q] with x hp ht; rw [abs_mul]; exact (mul_le_mul hp ht (abs_nonneg _) ((abs_nonneg _).trans hp)).trans_eq (by rw [coin_mul,add_zero])
lemma pwr (hf:Grade a f)(n:ℕ) : Grade (a*n) (fun i=> f i^n):=by
 induction n with
 | zero=> simp only [Nat.cast_zero,mul_zero,pow_zero]; exact block _
 | succ n ih=>
    convert! ih.mul hf using 1; · push_cast; ring
lemma plus (p: Grade a f)(q:Grade a g):Grade a (fun x=>f x+g x):=by
 obtain ⟨u,p⟩:=p; obtain ⟨v,q⟩:=q; let w:=max u v+1; have he:max u v<w:=lt_add_one _; refine ⟨w,?_⟩; have h: (1/2:ℝ)>0:= by norm_num
 filter_upwards [coin_budget (c:=0) (f:=0) (b:=u) (a:=a) (d:=a) (e:=w) (Or.inr (Or.inl ⟨rfl,(le_max_left ..).trans_lt he⟩)) 1 _ h,coin_budget (c:=0) (f:=0) (b:=v) (a:=a) (d:=a) (e:=w) (Or.inr (Or.inl ⟨rfl,(le_max_right ..).trans_lt he⟩)) 1 _ h,p,q] with x h1 h2 h3 h4
 linarith only [abs_add_le (f x) (g x),h1,h2,h3,h4]
lemma scaleB (c:ℝ)(hf:Grade a f) : Grade a (fun x=>c*f x):=by simpa only [zero_add] using (block c).mul hf
lemma pitch (a:ℝ):Grade a (fun x:ℝ=> x^a):=by
 apply cash (stock a 0); filter_upwards [eventually_gt_atTop (0:ℝ)] with x h; unfold coin; simp_rw [mul_zero,add_zero,Real.rpow_def_of_pos h]; exact le_rfl
lemma cost_p (p:Grade a f)(h:a<b):∀ᶠ x:ℝ in atTop,|f x|≤ x^b:=by
 filter_upwards [p.budget b 0 1 h zero_lt_one,eventually_gt_atTop (0:ℝ)] with x v hx; simpa [coin,Real.rpow_def_of_pos hx] using v
lemma x_id : Grade 1 (id:ℝ→ℝ):=by have h:=pitch 1; simp_rw [Real.rpow_one] at h; exact h
lemma ceil_float {f:ℝ→ℝ}{a:ℝ}(p:Grade a f)(hf:∀ᶠ i:ℝ in atTop, 0 ≤ f i)(ha:0≤a):Grade a (fun i=> (⌈f i⌉₊:ℝ)):=by
 apply Grade.cash (p.plus ((block 1).grow ha)); filter_upwards [hf] with i h; rw [abs_of_nonneg (by positivity:(0:ℝ)≤⌈f i⌉₊), abs_of_nonneg (by positivity: 0≤f i+1)]; exact (Nat.ceil_lt_add_one h).le
lemma temp_b : Grade (-1/2) temp:= by apply cash (stock (-1/2) 1); filter_upwards [eventually_gt_atTop (0:ℝ)] with x p; rw [←thresh_eq p]
lemma trail_b {η:ℝ}(p:0<η) : Grade (-1) (fun x=> trail η (radiusB x)):=by
 apply cash (pitch (-1)); filter_upwards [eventually_gt_atTop (0:ℝ),clocks.tail_gone (G:=CF.SU.group) η p] with x h v; unfold trail; rw [abs_of_pos (Real.exp_pos _),Real.rpow_neg h.le,Real.rpow_one,abs_of_pos (inv_pos.mpr h)]; exact v
end Grade
end Almanac
end YM.Gleam.Luster
