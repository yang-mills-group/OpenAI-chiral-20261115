import YM.Pressure.Seeds
import YM.Next.SCHEDULE.Clocks

/-! eq:Bscales, eq:Bwidths. Account in terms of ONE real variable y, hence all `Eventually`
bounds yield a single delay independent of history, M, j, n. Use `lscale` = 1+radiusB
(polylog on these hats) as convenient currency. -/

set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress
open Filter Next.Scheduling.Clock Pressure
open scoped Topology
abbrev g := Next.Scheduling.Clock.gap
def drift := watch 2
lemma drift_eq (y : ℝ) : drift y=Real.exp ((Real.log (Real.log y))^2) := watch_two _
lemma temp_eq (y : ℝ) : temp y=g y * drift y:= by rw [drift_eq]; rfl
lemma drift_pos (y : ℝ) : 0 < drift y:=wp ..
lemma g_pos {y : ℝ} (h : 0<y) : 0<g y:= gp h
lemma temp_pos {y : ℝ} (h : 0<y) : 0<temp y:= by rw [temp_eq]; exact mul_pos (g_pos h) (drift_pos _)
lemma gscale {y : ℝ} (h : 0≤y) : g y ^2=y⁻¹:=by rw [g,gap,inv_pow,Real.sq_sqrt h]
lemma drift_one (y : ℝ) : 1 ≤ drift y:=by rw [drift_eq]; exact Real.one_le_exp (by positivity)

def mA (y : ℝ) := temp y / drift y ^ ((1:ℝ)/4)
def aA (y : ℝ) := Real.sqrt (mA y)
def wc (y : ℝ) := temp y / Real.sqrt (drift y)
def xi (y : ℝ) := g y^3
def sigmaN (y : ℝ) := drift y ^ (-(1:ℝ)/8)

def lscale (y : ℝ) : ℝ := 1+(radiusB y:ℝ)
lemma lscale_one (y : ℝ) : 1 ≤ lscale y:= by simp [lscale]
lemma lscale_late : Tendsto lscale atTop atTop := tendsto_atTop_add_const_left atTop _ (tendsto_natCast_atTop_atTop.comp counting)

structure PL (f : ℝ → ℝ) : Prop where
  bound : ∃ (k : ℕ), ∀ᶠ y in atTop, |f y| ≤ lscale y ^ k
structure NPL (f : ℝ → ℝ) : Prop where
  vanish (k : ℕ) : Tendsto (fun y=> lscale y ^ k * f y) atTop (𝓝 0)
variable {F G : ℝ → ℝ} {y : ℝ}
lemma PL.mono (H : PL F) (e : ∀ᶠ y in atTop, |G y| ≤ |F y|) : PL G:=by obtain ⟨k,h⟩:=H.bound; exact ⟨k,(e.and h).mono fun i p=>p.1.trans p.2⟩
lemma PL.const (c : ℝ) : PL (fun _=> c):= ⟨1,by simpa using (lscale_late.eventually_ge_atTop |c|)⟩
lemma PL.scale : PL lscale:=⟨1, Eventually.of_forall fun y=> by rw [abs_of_pos (zero_lt_one.trans_le (lscale_one _)),pow_one]⟩
lemma PL.mul (H : PL F) (E : PL G) : PL (fun y=> F y * G y):=by
 obtain ⟨k,h⟩:=H.bound; obtain ⟨i,p⟩:=E.bound; refine ⟨k+i, (h.and p).mono fun y g=> ?_⟩; rw [abs_mul,pow_add]; exact mul_le_mul g.1 g.2 (abs_nonneg _) ((abs_nonneg _).trans g.1)
lemma PL.pow (H : PL F) (k : ℕ) : PL (fun y=> F y^k):=by induction k with|zero=> simp_rw [pow_zero]; exact PL.const _| succ n ih=> simp_rw [pow_succ]; exact ih.mul H
lemma PL.add (H : PL F) (E : PL G) : PL (fun y=> F y + G y):=by
 obtain ⟨k,h⟩:=H.bound; obtain ⟨i,p⟩:=E.bound; refine ⟨k+i+1,?_⟩; filter_upwards [h,p,lscale_late.eventually_ge_atTop 2] with y h p e; apply ((abs_add_le ..).trans (add_le_add h p)).trans; let x:=lscale y; have e' : 2 ≤ x:= e; have hx : 1 ≤ x:= lscale_one y; let S:= x^(k+i); change x^k+x^i≤_; rw [pow_succ]; change _ ≤ S*x; rw [← le_sub_iff_add_le]; have hp : S+S≤ S*x:=by rw [← mul_two]; gcongr
 have h₁ : x^k ≤ S:= pow_le_pow_right₀ hx (by omega); have h₂ : x^i ≤ S:= pow_le_pow_right₀ hx (by omega); linarith
lemma PL.ceil (p : PL F) (h : ∀ᶠ y in atTop, 0≤F y) : PL (fun y=> (⌈F y⌉₊:ℝ)) :=
  (p.add (PL.const 1)).mono (h.mono fun i t=> by rw [abs_of_nonneg (Nat.cast_nonneg _),abs_of_nonneg (by linarith : 0≤ F i+1)]; exact (Nat.ceil_lt_add_one t).le)
lemma PL.log : PL Real.log:=by
 apply PL.scale.mono; filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1] with y p; rw [abs_of_pos (zero_lt_one.trans_le p),abs_of_pos (zero_lt_one.trans_le (lscale_one y))]; have h : Real.log y ^2 ≤ (radiusB y:ℝ):=Nat.le_ceil _; unfold lscale; nlinarith
lemma NPL.drop (H : NPL F) : Tendsto F atTop (𝓝 0) := by simpa using H.vanish 0
lemma NPL.pl (H : NPL F) : PL F:= (PL.const 1).mono (H.drop.abs.eventually (show ∀ᶠ x:ℝ in 𝓝 (|(0:ℝ)|), x ≤ (|(1:ℝ)|) from ge_mem_nhds (by norm_num)))
lemma NPL.mono (H : NPL F) (e : ∀ᶠ y in atTop, |G y| ≤ |F y|) : NPL G:=by
 constructor; intro n; rw [tendsto_zero_iff_norm_tendsto_zero]; refine squeeze_zero' (Eventually.of_forall fun _=> norm_nonneg _) ?_ (tendsto_zero_iff_norm_tendsto_zero.mp (H.vanish n)); filter_upwards [e] with y p; rw [norm_mul,norm_mul]; exact mul_le_mul_of_nonneg_left p (norm_nonneg _)
lemma NPL.const_mul (H : NPL F) (c : ℝ) : NPL (fun y=> c*F y):= by constructor; intro k; simpa only [mul_zero,mul_left_comm c] using (H.vanish k).const_mul c
lemma NPL.mul (H : NPL F) (E : PL G) : NPL (fun y=> F y* G y):=by
 obtain ⟨k,h⟩:=E.bound; refine (show NPL (fun y=> F y * lscale y ^ k) from ?_).mono ?_
 · constructor; intro i; simpa only [pow_add,mul_assoc,mul_comm (lscale _^k) (F _)] using H.vanish (i+k)
 refine h.mono fun y e=>?_ ; simp only [abs_mul]; exact mul_le_mul_of_nonneg_left (e.trans (le_abs_self _)) (abs_nonneg _)
lemma PL.times (H : PL F) (E : NPL G) : NPL (fun y=> F y* G y):=(E.mul H).mono (Eventually.of_forall fun y=> by rw [mul_comm])
lemma NPL.add (H : NPL F) (E : NPL G) : NPL (fun y=> F y + G y):= by constructor; intro k; simpa only [zero_add,mul_add] using (H.vanish k).add (E.vanish k)
lemma npl_drift (a : ℝ) (h : 0<a) : NPL (fun y=> (drift y ^ a)⁻¹):= ⟨fun k=> by simp_rw [← div_eq_mul_inv]; exact ceiling_cheaper _ _ _ (by norm_num) h⟩
lemma npl_drift_g (a c : ℝ) (h : 0<c) : NPL (fun y=> drift y ^ a * g y ^ c):=by
 constructor; intro k; have he:= ((npl_drift 1 zero_lt_one).vanish k).mul (light 2 (1+a) c h); rw [zero_mul] at he; refine he.congr fun y=>?_ ; have hx:0 < drift y:=drift_pos _; rw [Real.rpow_add (show 0<watch 2 y from hx),Real.rpow_one,Real.rpow_one]; change _*(drift y * _ * _)=_; field_simp; unfold drift; ring
lemma npl_g : NPL g:= by simpa using npl_drift_g 0 1 zero_lt_one
lemma npl_temp : NPL temp:= (npl_drift_g 1 1 zero_lt_one).mono <| Eventually.of_forall fun y=>by simp only [Real.rpow_one,temp_eq,mul_comm,le_refl]
lemma npl_mA : NPL mA:= by
 apply npl_temp.mono; refine Eventually.of_forall fun y=>?_ ; unfold mA; rw [abs_div,abs_of_nonneg (Real.rpow_pos_of_pos (drift_pos _) _).le]; exact div_le_self (abs_nonneg _) (Real.one_le_rpow (drift_one _) (by norm_num))
lemma mA_pos (h : 0<y) : 0<mA y:= div_pos (temp_pos h) (Real.rpow_pos_of_pos (drift_pos y) _)
lemma aA_positive (h : 0<y) : 0<aA y:= Real.sqrt_pos.mpr (mA_pos h)
lemma xi_pos (h : 0<y) : 0<xi y:=pow_pos (g_pos h) _
end YM.CF.BPress
