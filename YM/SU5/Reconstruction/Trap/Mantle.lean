import YM.SU5.Reconstruction.Trap.Chirp
import YM.SU5.Reconstruction.Trap.Awning
/-!
# SOT Mellin for light energy. Null part also registered.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
set_option linter.unusedSectionVars false
namespace YM.Multiplier
open Function Set Filter MeasureTheory Spectral Analysis Metric
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
variable {X : Type*} [MeasurableSpace X] {H : Hilbert} (P : PVM H X)
local notation "𝔪" x:max => P.diagonal x
namespace Chirp
open Complex
-- nonnegative measurable frequencies. Using REAL type.
variable (L : X→ℝ)(m : Measurable L) (b:∀ x, 0≤ L x)(a : ℂ)(p:0<a.re)
-- zero singular projection function dedicated
def onboard (L:X→ℝ) : Set X := {x|0<L x}
include m
lemma arc : MeasurableSet (onboard L) := measurableSet_lt measurable_const m
omit m in
noncomputable def singers (u:ℝ) : H.Op:= order P (fun x=> sing u (L x))
omit m in
noncomputable def starry (u:ℝ) : H.Op:= order P ((onboard L).indicator (fun x=>sing u (L x)))
local notation "O" => onboard L
lemma sings (u:ℝ):Registers P (fun x=>sing u (L x)) (singers P L u) :=
 order_reads _ ⟨(measurable_sing u).comp m,1,zero_le_one,fun _=> (nice ..).le⟩
lemma payStar (u:ℝ):Registers P ((onboard L).indicator (fun x=>sing u (L x))) (starry P L u) := order_reads P ((sings P L m u).price.mask (arc L m))
lemma refreshing (u:ℝ): starry P L u= P.region (onboard L)*singers P L u := (payStar P L m u).single ((sings P L m u).mask (arc L m) ((sings P L m u).comm (arc L m)))
lemma star_zero : starry P L 0=P.region (onboard L) := by apply (payStar P L m 0).single; simp_rw [origin]; exact Registers.box P (arc L m) -- tune
lemma choir (u:ℝ): singers P L u * singers P L (-u)=1:=by
 apply ((sings P L m u).times (sings P L m _)).single
 convert Registers.one P using 1
 ext x; exact (team u (L x) (-u)).trans (by simp)
omit m
noncomputable def slopeRay (a:ℂ)(L:X→ℝ)(z:ℂ) (x:X) := Complex.exp (-a*z*L x)
noncomputable def sailsOn:= {z:ℂ| 0<(a*z).re}
lemma sails_open : IsOpen (sailsOn a) := isOpen_lt continuous_const (by fun_prop)
include p
lemma realRay (x:ℝ)(t:0<x): (x:ℂ)∈ sailsOn a:= by unfold sailsOn; simp [mul_re]; exact mul_pos p t
omit p
lemma rayValue {z} (x:X): HasDerivAt (fun p=> slopeRay a L p x) (-a*L x*slopeRay a L z x) z := by
 convert (((((hasDerivAt_id' z).const_mul (-a)).mul_const ((L x:ℂ))).cexp)) using 1 <;> try rfl
 unfold slopeRay; ring
include b
lemma ray_cost {z:ℂ} (e:z∈ sailsOn a) (x:X) : ‖slopeRay a L z x‖ ≤ 1:=by
 rw [slopeRay,norm_exp,Real.exp_le_one_iff]; rw [neg_mul,neg_mul, neg_re, mul_re]; simp only [Complex.neg_re,ofReal_im,mul_zero,sub_zero,ofReal_re] -- tuned rw order
 have p:0<(a*z).re:=e; exact neg_nonpos.mpr (mul_nonneg p.le (b x))
include m
lemma rays {z} (e:z∈ sailsOn a) : Registers P (slopeRay a L z) (order P (slopeRay a L z)) := order_reads _ ⟨by unfold slopeRay; fun_prop,1,zero_le_one,ray_cost L b a e⟩
lemma bill : AnalyticOnNhd ℂ (fun z=> order P (slopeRay a L z)) (sailsOn a):= full_roofs P (sails_open a) _ 1 _ (fun z e=>rays P L m b a e) (fun x z _=> (rayValue L a x).differentiableAt.differentiableWithinAt) (fun _ e=> ray_cost L b a e) (fun _=> by unfold slopeRay; fun_prop)
lemma rayChange (z:ℂ)(w:z∈ sailsOn a): Registers P (fun x=> -a*(L x:ℂ)*slopeRay a L z x) (deriv (fun z=> order P (slopeRay a L z)) z) := rooftop_deriv P (sails_open a) _ 1 _ (fun z e=> rays P L m b a e) (fun x z _=> (rayValue L a x).differentiableAt.differentiableWithinAt) (fun z e=> ray_cost L b a e) (fun _=> by unfold slopeRay; fun_prop) z w (fun x=> rayValue L a x)
omit m b
-- approximate intervals. positive. biased powers.
noncomputable def juice (u t:ℝ) (x:X) : ℂ := a*L x*west u (a*L x) t
@[simp] lemma juice_norm (u t:ℝ) (x:X) : ‖juice L a u t x‖=‖a‖ * |L x| * Real.exp (-a.re * L x*t):= by simp [juice,Complex.norm_real, Real.norm_eq_abs, wind,mul_re]
noncomputable def page (i:ℕ): Set ℝ:= Icc (1/((i:ℝ)+1)) i
noncomputable def header (u:ℝ)(i:ℕ) (x:X) : ℂ:=∫ t in page i, juice L a u t x ∂volume
local notation "ν" i:max=> volume.restrict (page i)
instance (i:ℕ): IsFiniteMeasure (volume.restrict (page i)):= by unfold page; infer_instance
lemma pagePos (i:ℕ): page i ⊆ Ioi 0:= fun x h=> lt_of_lt_of_le (by positivity) (show 1/((i:ℝ)+1) ≤ x from h.1)
include b p
lemma justice (u:ℝ)(x:X) : IntegrableOn (fun t=>juice L a u t x) (Ioi 0) := by
 rcases eq_or_lt_of_le (b x) with h|h
 · simp [juice,h.symm]
 exact (affordable u (a*L x) (by simp [mul_re]; exact mul_pos p h)).const_mul _
set_option maxHeartbeats 260000 in
lemma limit (u:ℝ)(x:X): Tendsto (fun i=> header L a u i x) atTop (𝓝 ((O).indicator (fun x=> reward u a*sing u (L x)) x)):= by
 have hx: AECover (volume.restrict (Ioi (0:ℝ))) atTop page:= AECover.inter (aecover_Ioi_of_Ici tendsto_one_div_add_atTop_nhds_zero_nat) (aecover_Iic tendsto_natCast_atTop_atTop)
 have he (i): page i ∩ Ioi 0=page i:= inter_eq_left.mpr (pagePos _)
 have hp := hx.integral_tendsto_of_countably_generated (justice L b a p u x)
 have q (i:ℕ):MeasurableSet (page i):= measurableSet_Icc
 unfold header; simp_rw [Measure.restrict_restrict (q _), he] at hp
 rcases eq_or_lt_of_le (b x) with h|h
 · simp [juice,h.symm,indicator_of_notMem,show x∉O from by simp [onboard,h.symm]]
 rw [indicator_of_mem (s:=onboard L) h]; convert hp using 2
 dsimp only [juice]; rw [integral_const_mul]; exact (tax u a p (L x) h).symm -- tune
lemma bounded_header (u:ℝ)(i:ℕ)(x:X): ‖header L a u i x‖ ≤ ‖a‖/a.re:= by
 rcases eq_or_lt_of_le (b x) with h|h
 · simp [header,juice,h.symm]; positivity
 let k:= -a.re*L x; have t:k<0:= mul_neg_of_neg_of_pos (by linarith) h
 unfold header; refine (norm_integral_le_integral_norm _).trans ?_
 refine (setIntegral_mono_set (μ:=volume) (justice L b a p u x).norm (Eventually.of_forall fun x=> norm_nonneg _) (Filter.Eventually.of_forall ?_)).trans_eq ?_
 · exact fun x=>fun h=>pagePos i h
 simp_rw [juice_norm, abs_of_pos h, integral_const_mul]; change ‖a‖*L x*(∫ p:ℝ in Ioi 0, Real.exp (k*p))=_; rw [integral_exp_mul_Ioi t]
 have hg: a.re≠0:= p.ne'; have hz:L x≠0:=h.ne'; simp [k]; field_simp
include m
omit b p in
@[fun_prop] lemma juice_meas (u:ℝ): Measurable (uncurry (juice L a u)):= by unfold uncurry juice west; fun_prop
lemma solid (u:ℝ)(i:ℕ) : Tag (header L a u i):=
 ⟨((juice_meas L m a u).stronglyMeasurable.integral_prod_left).measurable, ‖a‖/a.re,by positivity, bounded_header L b a p u i⟩
omit b p
lemma cutoff (u:ℝ): Registers P ((onboard L).indicator (fun x=> reward u a * sing u (L x))) (reward u a • starry P L u) := by
 have he:= (payStar P L m u).scale (reward u a); refine he.agrees (Tag.mask ((sings P L m _).price.scale _) (arc L m)) (fun x=> Eventually.of_forall ?_); intro y; by_cases h:y∈O <;> simp [h,smul_eq_mul]
end Chirp
end YM.Multiplier
