import YM.SU5.Cheer.Flank
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
/-!
# Upgrade *one-side* Euclidean Lévy to Minkowski: polynomial cost.
NOTE: no analyticity inputs other than **paired coefficients** with true semigroup. Applies to measures on a half, including nu tangent (scaled). No assumptions on eigen or spectral gap.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Cheer
open Function Metric Set Filter Complex MeasureTheory Measure Mink
open scoped Real Topology NNReal ENNReal InnerProductSpace BigOperators Polynomial
abbrev Narrow:= FiniteMeasure E4
variable (μ ν:Narrow)(x:Space3)(u:ℂ)(F:ℕ→Narrow)
local notation "M"=> Measure E4
def Brilliant (μ:Narrow):Prop:=∀ᵐ w ∂(μ:M), 0≤ time w
def FLap := ∫ w, tendsK x u w ∂(μ:M)
lemma launched_z : FLap μ 0 0=↑(μ.mass:ℝ):=by
 unfold FLap tendsK; simp [measureReal_def,← FiniteMeasure.ennreal_mass,Complex.real_smul] -- v
lemma mono_pos (r s:Pasture): ∀ᵐ v ∂ moving r s,0 ≤ time v:=by -- maybe move to VelvetWay
 rw [moving]; refine (ae_map_iff prom_cont.measurable.aemeasurable ((isClosed_le continuous_const Mink.clock_cont).measurableSet)).mpr (ae_of_all _ fun v=>?_); simp only [Prom,clock_add,pierT]; exact add_nonneg (add_nonneg (bill_p _) (bill_p _)) (add_nonneg (bill_p _) (bill_p _))
structure Lyrical : Prop where
  there(i:ℕ) : Brilliant (F i)
  bright : Brilliant μ
  meets (x:Space3)(r:ℝ≥0): Tendsto (fun i=> FLap (F i) x (r:ℝ)) atTop (𝓝 (FLap μ x (r:ℝ)))
lemma destined (h:Brilliant μ)(e:0≤u.re): Integrable (tendsK x u) (μ:M):= by
 apply (integrable_const 1).mono' (airy x u |>.aestronglyMeasurable); exact Eventually.mono h fun i v=> withinK x u i e v
namespace Lyrical
variable{μ F}(A:Lyrical μ F)
include A
lemma massR : Tendsto (fun i:ℕ=> ((F i).mass:ℝ)) atTop (𝓝 (μ.mass:ℝ)):=by
 have he:= Complex.continuous_re.continuousAt.tendsto.comp (A.meets 0 0)
 simp only [NNReal.coe_zero,ofReal_zero,launched_z, Function.comp_def,ofReal_re] at he; exact he
omit A
def eon (x:E4):=Real.exp (-max 0 (time x))
@[fun_prop] lemma e_cont : Continuous eon:=by unfold eon; fun_prop
lemma e_inside (x:E4) : eon x∈ Icc (0:ℝ) 1:= ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr (le_max_left ..))⟩
private abbrev Wave:=C(Set.Icc (0:ℝ) 1, ℝ)
def meter (x:E4):Icc (0:ℝ) 1:= ⟨eon x,e_inside _⟩
@[fun_prop] lemma m_cont : Continuous meter:= by unfold meter; fun_prop
variable (a:Narrow)(f g : Wave)
def windCell (f:Wave)(y:E4):= tendsK x 0 y* (f (meter y):ℂ)
def ride := ∫ y, windCell x f y ∂(a:M) -- def `windCell f` binder? expect x f
@[fun_prop] lemma v_cont : Continuous (windCell x f):=by unfold windCell; fun_prop
lemma gentle(y:E4): ‖tendsK x 0 y‖=1:=by simp [tendsK,norm_exp]
lemma norm_cell (y:E4): ‖windCell x f y‖≤ ‖f‖:= calc
 _ = ‖f (meter y)‖:=by simp [windCell,gentle]
 _ ≤ ‖f‖:=ContinuousMap.norm_coe_le_norm .. -- formatting
lemma rideB : Integrable (windCell x f) (a:M) := (integrable_const _).mono' (v_cont x f |>.aestronglyMeasurable) (ae_of_all _ (norm_cell x f))
lemma ride_add : ride x a (f+g)= ride x a f+ride x a g := by unfold ride; simp_rw [windCell, ContinuousMap.add_apply,ofReal_add,mul_add]; exact integral_add (rideB ..) (rideB ..) -- tune
lemma price : ‖ride x a f - ride x a g‖ ≤ (a.mass:ℝ)* ‖f-g‖:= by
 rw [sub_eq_of_eq_add (show ride x a f= ride x a (f-g)+ride x a g by rw [← ride_add, sub_add_cancel])]; unfold ride
 refine (norm_integral_le_integral_norm _).trans ((integral_mono (rideB .. |>.norm) (integrable_const _) (norm_cell x (f-g))).trans_eq ?_)
 rw [integral_const]; rfl
include A
lemma poly (p :ℝ[X]): Tendsto (fun i=> ride x (F i) (p.toContinuousMapOn _)) atTop (𝓝 (ride x μ (p.toContinuousMapOn _))) := by
 induction p using Polynomial.induction_on' with
 | add p q h z=> simp only [← Polynomial.toContinuousMapOnAlgHom_apply,map_add,ride_add]; exact h.add z
 | monomial n a =>
    have he (b:Narrow)(k:Brilliant b) : ride x b ((Polynomial.monomial n a).toContinuousMapOn _) = ↑a * FLap b x (n:ℂ):= by
       rw [ride, FLap, ← integral_const_mul]; apply integral_congr_ae (Eventually.mono k (fun y h=>?_))
       simp only [windCell,Polynomial.toContinuousMapOn_apply, Polynomial.toContinuousMap_apply, Polynomial.eval_monomial,meter,eon,max_eq_right h]; push_cast
       unfold tendsK; rw [← Complex.exp_nat_mul]; generalize (inner ℝ (spatial y) x :ℂ)*I=w
       rw [show w-(n:ℂ)* ↑(time y) = w + n * (-(time y:ℂ)) by ring, Complex.exp_add]; ring_nf -- tune
    have hy:= (A.meets x n).const_mul (a:ℂ); simp only [NNReal.coe_natCast,ofReal_natCast] at hy
    rw [he μ A.bright]; exact hy.congr fun i=> (he (F i) (A.there i)).symm
lemma small_wave : Tendsto (fun i=> ride x (F i) f) atTop (𝓝 (ride x μ f)):= by
  apply Metric.tendsto_nhds.mpr; intro ε h
  let m:ℝ:= μ.mass; let q:=ε/3; let e:=q/(m+1); have hm:0≤m:= μ.mass.property; have ht :0<m+1:=by linarith
  have hv:0<e:= div_pos (by unfold q; positivity) ht
  obtain ⟨p,P⟩:=exists_polynomial_near_continuousMap 0 1 f e hv
  let r:Wave:= p.toContinuousMapOn _; have he:∀ a:Narrow,(a.mass:ℝ)< m+1 → dist (ride x a r) (ride x a f) < q :=fun a H=>by
    rw [dist_eq_norm]; refine lt_of_le_of_lt (price ..) ((calc
         (a.mass:ℝ)*‖r-f‖ ≤ (a.mass:ℝ)*e:= mul_le_mul_of_nonneg_left P.le a.mass.property
         _ < (m+1)*e := mul_lt_mul_of_pos_right H hv
         _ = q:= by unfold e; field_simp): _ < q)
  filter_upwards [A.massR.eventually (gt_mem_nhds (show m<m+1 by linarith)), Metric.tendsto_nhds.mp (A.poly x p) q (by unfold q; positivity)] with i hp hx
  grw [dist_triangle (ride x (F i) f) (ride x (F i) r), dist_comm (ride x (F i) f),dist_triangle (ride x (F i) r) (ride x μ r) (ride x μ f), he (F i) hp, he μ (by change m<m+1; linarith)]
  change dist (ride _ _ _) _ < q at hx; unfold q at *; linarith -- tune
lemma voices (h: 0<u.re): Tendsto (fun i=>FLap (F i) x u) atTop (𝓝 (FLap μ x u)):= by
 let k : C(Set.Icc (0:ℝ) 1, ℂ):= ⟨fun i=> ((i.val:ℝ):ℂ) ^ u, (continuous_ofReal_cpow_const h).comp continuous_subtype_val⟩
 let f:Wave:=⟨re ∘ k,(continuous_re.comp k.continuous)⟩
 let g:Wave:=⟨im ∘ k,(continuous_im.comp k.continuous)⟩
 have hw (b:Narrow) (p:Brilliant b): FLap b x u = ride x b f + ride x b g * I:= by
   rw [FLap,ride,ride,← integral_mul_const, ← integral_add (rideB ..) (rideB x b g|>.mul_const _)]; apply integral_congr_ae (Eventually.mono p (fun i h=>?_))
   unfold windCell; rw [mul_assoc,← mul_add,show ↑(f _) + ↑(g _) * I=k (meter i) from Complex.re_add_im (k (meter i))]; change _= _ * (↑(Real.exp (-max 0 (time i))) :ℂ)^u
   rw [max_eq_right h, Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr (Real.exp_pos _).ne'), ← ofReal_log (Real.exp_pos _).le, Real.log_exp]; unfold tendsK; rw [←exp_add]; simp; ring_nf
 rw [hw μ A.bright]; exact ((A.small_wave x f).add ((A.small_wave x g).mul_const I)).congr fun i=>(hw (F i) (A.there i)).symm
end Lyrical
end YM.Cheer
#print axioms YM.Cheer.Lyrical.voices
