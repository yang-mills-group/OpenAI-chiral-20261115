import YM.SU5.Reconstruction.Seams.Lift
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
/-!
# Mellin integrals of the imaginary movers we need
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Multiplier
open Function Set Filter MeasureTheory Spectral Analysis Metric
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
namespace Chirp
open Complex
variable (u:ℝ)
local notation "ℬ" => (Ioi (0:ℝ))
local notation "X" => (volume.restrict ℬ)
-- true marker choice at ALL y incl zero; spectral projections paid separately
noncomputable def sing (u t:ℝ) : ℂ := exp ( (Real.log t:ℂ)*I*(u:ℂ))
local notation "θ" => sing (-u)
def west (u:ℝ) (a:ℂ) (t:ℝ) := sing (-u) t * exp (-a*(t:ℂ))
@[simp] lemma nice (x:ℝ):‖sing u x‖=1:= by simp [sing,norm_exp,mul_re,mul_im]
@[fun_prop] lemma measurable_sing : Measurable (sing u) := by unfold sing; fun_prop
@[simp] lemma origin (x:ℝ) : sing 0 x=1:=by simp [sing]
lemma sing_cont (x:ℝ)(p:x≠0):ContinuousAt (sing u) x:= by unfold sing; fun_prop
lemma rains (a:ℂ) : Measurable (west u a):= by unfold west; fun_prop
@[fun_prop] lemma singOn : ContinuousOn (sing u) ℬ:= fun t v=> (sing_cont u t (mem_Ioi.mp v|>.ne')).continuousWithinAt
@[simp] lemma wind (a:ℂ)(t:ℝ): ‖west u a t‖= Real.exp (-a.re*t):= by simp [west,norm_exp,mul_re]
lemma affordable (a:ℂ)(p:0<a.re): Integrable (west u a) (volume.restrict (Ioi 0)) := by
 refine Integrable.mono' (integrableOn_exp_mul_Ioi (a:= -a.re) (by linarith) 0) (rains u _).aestronglyMeasurable ?_
 exact Eventually.of_forall fun x=> (wind ..).le
-- Laplace for a in positive halfplane; no length units changed
def swapT (u:ℝ):ℂ:= 1-I*u
lemma band : 0 < (swapT u).re:=by simp [swapT,mul_re]
local notation "σ" => swapT u
local notation "G" => Gamma σ
noncomputable def song (u:ℝ) (a:ℂ) : ℂ := ∫ t in Ioi (0:ℝ), west u a t
lemma realSong (x:ℝ)(p:0<x): song u x = exp (log (x:ℂ)* -σ) * G := by
 have ht(t:ℝ)(h:0<t): sing (-u) t=(t:ℂ)^(σ-1):= by
   rw [cpow_def_of_ne_zero (by exact_mod_cast h.ne')]; unfold sing swapT; congr 1; push_cast;  rw [← ofReal_log h.le]; ring
 rw [song,setIntegral_congr_fun (g:=fun t:ℝ=>(t:ℂ)^(σ-1)*exp (-((x:ℂ)*t))) measurableSet_Ioi (fun t u' => show west u _ _ = _ from by unfold west; rw [ht t (mem_Ioi.mp u'), neg_mul])]
 rw [integral_cpow_mul_exp_neg_mul_Ioi (band _) p, one_div,← ofReal_inv,cpow_def_of_ne_zero (by exact_mod_cast (inv_pos.mpr p).ne')]
 rw [←ofReal_log (inv_pos.mpr p).le,← ofReal_log p.le, Real.log_inv,ofReal_neg, neg_mul,mul_neg]
local notation "D" => {a:ℂ| 0<a.re}
set_option maxHeartbeats 320000 in
lemma holsong : AnalyticOnNhd ℂ (song u) {a:ℂ|0<a.re} := by
 apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const (by fun_prop)); intro a p
 let r:= a.re/2; have hr: 0< r:=half_pos (show 0<a.re from p); let B:={v:ℂ| r<v.re}
 let W a (t:ℝ):= - (t:ℂ) * west u a t; let k(t:ℝ) := t*Real.exp (-r*t)
 apply DifferentiableAt.differentiableWithinAt
 refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=west u) (F':=W) (μ:=X) (bound:=k)
   ((isOpen_lt continuous_const (by fun_prop : Continuous Complex.re)).mem_nhds (show a∈B from by dsimp [B]; unfold r at *; linarith))
   (Eventually.of_forall fun _=> (rains u _).aestronglyMeasurable) (affordable u a p)
   (((continuous_ofReal.measurable.neg).mul (rains u a)).aestronglyMeasurable) ?_ ?_ (ae_of_all _ (fun t w _=> ?_))).2.differentiableAt
 · filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with t v b w
   have hv:0<t:=v; have hw:r<b.re:=w
   unfold W k; simp only [norm_mul,norm_neg, Complex.norm_real,Real.norm_eq_abs,abs_of_pos hv, wind]; gcongr
 · have hi:= integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num : (-1:ℝ)<1) (p:=1) le_rfl hr
   simpa [k,IntegrableOn] using hi
 · convert (((((hasDerivAt_id' w).neg).mul_const (t:ℂ)).cexp).const_mul (sing (-u) t)) using 1 <;> try rfl
   unfold W west; simp only [Pi.neg_apply]; ring
lemma complexSong (a:ℂ)(p:0<a.re): song u a=exp (log a * -σ)*G:= by
 let W(a:ℂ):= exp (log a * -σ)*G
 apply ConePrice.Sail.pioneer (N:=W) (A:=D) (convex_halfSpace_gt reCLM.toLinearMap.isLinear 0|>.isPreconnected) (w:=1) (wA:=by simp) 0 2 (by norm_num) (holsong u) (fun x h=>?_) (fun x v=>realSong _ x v.1) p
 unfold W; exact ((analyticAt_clog (show x∈slitPlane from Or.inl h)).mul analyticAt_const).cexp.mul analyticAt_const
-- Mellin constants; reversal signs as used for modular
noncomputable def reward (u:ℝ)(a:ℂ): ℂ:= exp (log a * I * u)*Gamma (swapT u)
lemma reward_ne (a:ℂ): reward u a≠0:= mul_ne_zero (exp_ne_zero _) (Gamma_ne_zero_of_re_pos (band _))
lemma tax (a:ℂ)(p:0<a.re)(x:ℝ)(b:0<x):
    a*(x:ℂ)*song u (a*x)=reward u a * sing u x:= by
 let z:ℂ:=a*x; have hc:0 < z.re:=by simp [z,mul_re]; exact mul_pos p b
 have h:a≠0:=fun v=>by simp [v] at p
 have hz:z≠0:= fun v=>by simp [v] at hc
 change z*_= _; rw [complexSong u z hc]; dsimp only [reward,sing]; nth_rw 1 [← exp_log hz]; unfold swapT
 rw [← mul_assoc, ← Complex.exp_add]; rw [mul_right_comm, ← Complex.exp_add]; congr 2 -- unify log
 unfold z; rw [log_mul_ofReal x b a h]; ring
/-- in light orientation e (±1). contour point z(Eu j)=1-εi. -/
noncomputable def sail (ε:ℝ) : ℂ := 1-ε*I
noncomputable def wages (ε u:ℝ) : ℝ := Real.exp (-ε*Real.pi*u/2)
@[simp] lemma sail_re (ε:ℝ): (sail ε).re=1:=by simp [sail,mul_re]

lemma wages_pos (ε u:ℝ): 0 < wages ε u:= Real.exp_pos _
lemma toKite (ε:ℝ)(e:ε=1∨ε=-1) : log (sail (-ε))-log (sail ε)= I* ((ε*Real.pi/2:ℝ):ℂ):=by
 have h: log (sail (-1))-log (sail 1)= I* ((Real.pi/2:ℝ):ℂ):=by
   let z:=sail 1; have hp: log (sail (-1))=log z+log I:= by
     have v: z≠0:= fun p=>by have h:= congrArg Complex.re p; simp [z] at h
     rw [show sail (-1)= z*I from by simp [z,sail, sub_mul,add_comm]]
     apply log_mul v I_ne_zero; rw [arg_I]; have ht:= abs_le.mp ((abs_arg_le_pi_div_two_iff (z:=z)).2 (by unfold z; simp))
     constructor <;> linarith [Real.pi_pos]
   rw [hp]; simp only [sub_eq_iff_eq_add]; rw [log_I]; push_cast; unfold z; ring
 rcases e with rfl|rfl
 · simpa using h
 have hv:=congrArg Neg.neg h; rw [neg_sub] at hv; simp; push_cast at hv ⊢; rw [hv]; ring
lemma bridge (ε:ℝ)(p:ε=1∨ε=-1): reward u (- (ε:ℂ)* I * (- sail ε)) = (wages ε u:ℂ) *reward u (sail ε):=by
 -- left arg = i ε *sail
 have he: - (ε:ℂ)* I * (- sail ε)=sail (-ε):=by rcases p with p|p <;> rw [p] <;> simp [sail,mul_sub] <;> ring_nf <;> simp <;> ring
 rw [he, reward,reward,wages,Complex.ofReal_exp,←mul_assoc,← Complex.exp_add]; congr 2; rw [sub_eq_iff_eq_add.mp (toKite ε p)]; push_cast; ring_nf; simp <;> ring
lemma sails (ε:ℝ) (p:ε=1∨ε=-1): reward u (sail (-ε)) = (wages ε u:ℂ) * reward u (sail ε):= by
 have he:= bridge u ε p; rw [show sail (-ε) = _ from ?_]; exact he
 rcases p with p|p <;> rw [p]<;> simp [sail,mul_sub] <;> ring_nf<;> simp <;> ring
lemma team (b v:ℝ): sing u b*sing v b=sing (u+v) b:=by unfold sing; rw [← exp_add]; congr 1; push_cast; ring
lemma neg_time (b:ℝ): sing (-u) b= star (sing u b):=by unfold sing; simp [← exp_conj]
-- character Re(p)*inner usage later
lemma voices (b t:ℝ)(p:0<b)(q:0<t):sing u (b*t)=sing u b*sing u t:= by unfold sing; rw [Real.log_mul p.ne' q.ne',←exp_add]; congr 1; push_cast; ring
@[simp] lemma worthless : sing u 0=1:=by simp [sing]
end Chirp
end YM.Multiplier
