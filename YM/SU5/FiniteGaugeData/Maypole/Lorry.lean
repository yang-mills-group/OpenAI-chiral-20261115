import YM.SU5.FiniteGaugeData.Maypole.Xmas
/-! # Diagonal spectrum: time-skew tilt, moment poles -/
set_option autoImplicit false
set_option maxHeartbeats 360000
noncomputable section
set_option linter.unusedSectionVars false
namespace YM.CF.Buffered.Afterglow.Hierarchy.Vp.Juno
open Function Set MeasureTheory OS OS.Semigroup Complex Filter NormedSpace Metric Bornology Rimbaud
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder BigOperators
variable {X:Type*} [MeasurableSpace X] {A U:X→ℝ} {n i j k:ℕ}{μ:Measure X}[IsFiniteMeasure μ]{r s t e x C:ℝ} {z:ℂ}
-- scalar energies. slope with both directions, measured.P_Eq (OS proof later)
variable (P:Payer μ A U)
include P
local notation "E"=> Real.exp
abbrev speed:ℝ:=512
private lemma wageL {S:Set X}(h: MeasurableSet S)(q:Chunk t C μ A U) {a:ℝ}(e:0<a)(p:∀ x∈S,A x ≤ a ∧ speed*a ≤ |U x|) (n:ℕ): μ.real S*(Real.exp (-t*a)*(speed*a)^(2*n)) ≤ billow t C n:=by
 let f:=blow A U t n; let D:= E (-t*a)*(speed*a)^(2*n); obtain ⟨u,w⟩:= Momentum P q n; change Integrable f μ at u; have he:= q.live; have hC: ∫ x in S,D ∂μ ≤ ∫ x in S,f x ∂μ:=by
    refine setIntegral_mono_on (integrableOn_const (C:=D) ..) u.integrableOn h (fun x y=>?_); apply mul_le_mul ?_ ?_ (by unfold speed; positivity : 0≤(speed*a)^(2*n)) (Real.exp_pos _).le; · apply Real.exp_monotone; exact mul_le_mul_of_nonpos_left (p x y).1 (neg_nonpos.mpr he.le)
    apply pow_le_pow_left₀ (by unfold speed; positivity); refine (p x y).2.trans ?_; have hv:= Complex.abs_im_le_norm (Ar (A x) (U x)); rwa [show (Ar (A x) (U x)).im= U x by simp [Ar]] at hv
 have hp:= setIntegral_le_integral (s:=S) u (Eventually.of_forall (fun x:X=>blow_nn x)); rw [setIntegral_const] at hC; exact hC.trans (hp.trans w) -- tune signature
local notation "α" a:max=>512*a
set_option maxHeartbeats 340000 in
lemma spent {a:ℝ}(e:0<a) {S:Set X}(h:MeasurableSet S)(p:∀ x∈S, A x ≤ a ∧ speed*a ≤ |U x|)(P0:∀ᶠ t:ℝ in atTop,Chunk t C μ A U): μ S=0:=by
 let R(n:ℕ):ℝ:= (n+1:ℕ) / a; have hr:Tendsto R atTop atTop:= Tendsto.atTop_div_const e (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)) -- label?
 have he:∀ᶠ n in atTop,μ.real S≤ C*E 1*((E 1)/16)^n:=by
    filter_upwards [hr.eventually P0] with n u; have t:R n=(n+1:ℕ)/a:=rfl; let z:= Real.exp (-(R n)*a)*(speed*a)^(2*n); have hv:0<z:=by unfold z speed; positivity
    refine le_of_mul_le_mul_right ((wageL P h u e p n).trans (le_of_eq ?_)) hv; unfold billow; let B:=n+1; have hc: burn (R n) n=(64*a)⁻¹:=by unfold burn; rw [t]; push_cast; field_simp;
    have hp:E (-(R n)*a)=((E 1)^ (n+1))⁻¹ := by rw [t]; push_cast; rw [show -(((n:ℝ)+1)/a)*a= -((n:ℝ)+1) by field_simp,Real.exp_neg,Real.exp_add]; rw [pow_succ,show E (n:ℝ)=(E 1)^n by nth_rw 1 [←mul_one (n:ℝ)]; rw [Real.exp_nat_mul]]; -- tune
    rw [hp,hc,inv_inv]; unfold speed; -- reduce powers relation `(64 a)= (512a)/8` cancel
    rw [pow_succ (E 1),show (512:ℝ)*a=8*(64*a) from (by ring),mul_pow _ (64*a), pow_mul (8:ℝ) 2]; -- want $8^(2*n)=64^n$
    rw [div_pow]; field_simp; rw [show (8:ℝ)^2=4*16 from (by norm_num), mul_pow]; ring

 have ht:|E 1/16|<1:=by rw [abs_of_nonneg (by positivity)]; linarith [Real.exp_one_lt_d9]
 have hj:Tendsto (fun n:ℕ=>(E 1/16)^n) atTop (𝓝 0):= tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ((abs_lt.mp ht).2)
 have hv:μ.real S≤0:= ge_of_tendsto (show Tendsto (fun n:ℕ=>C*E 1*(E 1/16)^n) atTop (𝓝 0) from (by simpa only [mul_zero] using hj.const_mul (C*E 1))) he
 exact (measureReal_eq_zero_iff (measure_ne_top μ S)).1 (le_antisymm hv measureReal_nonneg)
omit P
lemma insideCap(a r:ℝ)(p:speed*a<r)(_h:0≤a):∃ v:ℝ,a<v ∧ speed*v<r:= by
 have ht:speed>0:=by unfold speed; positivity
 obtain ⟨z,t,e⟩:=exists_between p; refine ⟨z/speed,?_,?_⟩; · apply (_root_.lt_div_iff₀ ht).2; rwa [_root_.mul_comm]
 rwa [mul_div_cancel₀ _ ht.ne'] -- tune
-- specialize to E4.L(A.S.).
end YM.CF.Buffered.Afterglow.Hierarchy.Vp.Juno
