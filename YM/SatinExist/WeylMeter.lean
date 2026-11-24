import YM.Heat.Duration
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-! ## Energy resolution of a Schwartz measurement on the same orbit.

Used for unpadding with only positive energy (not assuming cone): pay on the vector at E(t),
using (I+H)^(-N) for that semigroup. Full norm of the requested space-time answer, not
merely determining weak convergence on a dense set. No norm-continuity of U(x) needed. -/

set_option autoImplicit false
set_option maxHeartbeats 260000
noncomputable section
namespace YM.SatinJets
open Function Filter Metric InnerProductSpace Set Complex MeasureTheory Measure
open Analysis Boundary Spectral OS.Semigroup
open scoped NNReal ENNReal Topology BigOperators InnerProductSpace ComplexOrder Classical
variable {H : Hilbert}

section space
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] (S : Orbit H X)

/-- For each fixed vector, continuous throughout the price book. -/
def tuned (v:H) : Probe X →L[ℂ] H.space:=by
 let G: Probe X →ₗ[ℂ] H.space:= (ContinuousLinearMap.apply ℂ H.space v).toLinearMap.comp (SNAG.send S)
 refine ⟨G,?_⟩; apply continuous_of_continuousAt_zero G
 let a: Probe X →L[ℂ] MeasureTheory.Lp (α:=X) ℂ 1 volume := (SchwartzMap.toLpCLM ℂ ℂ 1 volume).comp SNAG.cut
 have ht : Tendsto (fun b=> ‖a b‖ * ‖v‖) (𝓝 0) (𝓝 0):=
   Continuous.tendsto' (a.continuous.norm.mul_const _) _ _ (show ‖a 0‖ * ‖v‖=0 from (by simp))
 apply Metric.tendsto_nhds.mpr; intro ε h
 filter_upwards [ht.eventually (gt_mem_nhds h)] with b p
 rw [map_zero,dist_zero_right]
 apply lt_of_le_of_lt _ p
 change ‖SNAG.send S b v‖≤‖a b‖*_
 rw [show ‖a b‖=_ from (show ‖a b‖=∫ x, ‖SNAG.cut b x‖ from SchwartzMap.norm_toLp_one),SNAG.sending]
 refine (norm_integral_le_integral_norm _).trans ?_; simp_rw [norm_smul,S.unitary,integral_mul_const,le_refl]

lemma tuned_eq (f:Probe X)(v:H): tuned S v f= SNAG.send S f v:=rfl

theorem sent_money {P:PVM H X}(T:S.Spectrum P)(f:Probe X)(v:H) :
     inner ℂ v (SNAG.send S f v) = ∫ p, f p ∂P.diagonal v:=by
 rw [SNAG.sending,← integral_inner (SNAG.over ..)]
 unfold Orbit.Spectrum at T
 simp_rw [inner_smul_right,← T, SNAG.cut, _root_.smul_apply,smul_eq_mul, mul_assoc, mul_comm (Probe.hat f _),integral_const_mul,Spectral.wave_integral]
 rw [Complex.real_smul,←mul_assoc,←ofReal_mul]; simp only [SNAG.normer,inv_mul_cancel₀ Probe.prepos.ne', ofReal_one,one_mul]
end space

variable {j : Axis} (S : OS.Semigroup H j) (n:ℕ)
local notation "Φ" => SNAG.send S.unit

lemma symmetrize_eq (f g:H.Op)(h:∀ v:H,inner ℂ v (f v)=inner ℂ v (g v)): f=g:=by
 have hx: f.toLinearMap=g.toLinearMap:= (ext_inner_map _ _).mp (fun x=> by change inner ℂ (f x) x=inner ℂ (g x) x; rw [←inner_conj_symm (f x) x,h x, inner_conj_symm])
 ext x; exact LinearMap.congr_fun hx x

lemma adjoin (u:Probe E4)(s:ℝ≥0):
    (Φ u).comp (S.E s)=(S.E s).comp (Φ u):=by
 ext1 x
 simp only [ContinuousLinearMap.comp_apply,SNAG.sending]; rw [← ContinuousLinearMap.integral_comp_comm (S.E s) (SNAG.over ..)]
 congr 1; funext b; rw [map_smul]; rw [← ContinuousLinearMap.comp_apply _ _ x,← S.overE]; rfl

/-- On the PRINTED Fourier sign and radian factors. Damped reads pay once. -/
lemma paid (u:Probe E4)(t:ℝ)(h:0≤t)(v:H):
    inner ℂ v (SNAG.send S.unit u (S.E t.toNNReal v))=
      ∫ p:E4, Real.exp (-t*p j) • u p ∂ S.ℚmeasure.diagonal v:=by
 let w:= t.toNNReal
 let s:ℝ≥0:= w/2
 have hc(x:H):(Φ u) (S.E s x)=S.E s (Φ u x):=DFunLike.congr_fun (adjoin S u s) x
 have he: s+s=w:=add_halves _
 calc
  _= inner ℂ (S.E s v) (SNAG.send S.unit u (S.E s v)):=by
    simp only [show S.E t.toNNReal=S.E (s+s) from congrArg S.E he.symm, S.time, ContinuousLinearMap.comp_apply]
    rw [hc (S.E s v)]; conv_rhs=> lhs; arg 1; rw [←S.sym s]
    rw [ContinuousLinearMap.adjoint_inner_left]
  _= ∫ y,(u y) ∂S.ℚmeasure.diagonal (S.E s v):= sent_money S.unit S.joint ..
  _=_:=by
    rw [S.damp,he,show (w:ℝ) = t from Real.coe_toNNReal t h]; unfold transform
    rw [integral_withDensity_eq_integral_smul (OS.Semigroup.measurable ..)]; rfl

-- Degree price; d(h)=h^n exp(-h)/n!
def thermalMass (t:ℝ):ℝ:= Real.exp (-t)*t^n/(n.factorial:ℝ)
local notation "μ"=> volume.restrict (Ioi (0:ℝ))
local notation "δ" n:max t:max=> thermalMass n t

lemma mass_set : Integrable (thermalMass n) μ:=by
 have he:= Real.GammaIntegral_convergent (by positivity: 0<(n:ℝ)+1)
 simp_rw [add_sub_cancel_right,Real.rpow_natCast] at he; exact he.integrable.div_const _
lemma mass_sign {t:ℝ}(h:0≤t):0≤ thermalMass n t:=by unfold thermalMass; positivity

lemma pocket (p:ℝ)(h:0≤p):
    (∫ t, thermalMass n t * Real.exp (-t*p) ∂ μ)= 1/(1+p)^(n+1):=by
 let a:= (1+p); have ht:0<a:=by unfold a; linarith only [h]
 let f:=(fun t:ℝ=> t^n * Real.exp (-(a*t)))
 have he: (∫ t,f t ∂ μ)=(1/a)^(n+1)*(n.factorial:ℝ):=by
   unfold f; rw [← Real.Gamma_nat_eq_factorial]
   have ht:= Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity : 0<(n:ℝ)+1) ht
   rw [add_sub_cancel_right,← Nat.cast_add_one,Real.rpow_natCast] at ht
   simpa only [Real.rpow_natCast,Nat.cast_add_one] using ht
 have hz(t:ℝ):thermalMass n t*Real.exp (-t*p)=f t/(n.factorial:ℝ):=by
   unfold f thermalMass; rw [show -(a*t)= -t+ -t*p from (by unfold a; ring), Real.exp_add]; ring
 simp_rw [hz,integral_div]; rw [he]; rw [div_pow]; unfold a; unfold a at ht; field_simp; exact one_pow _

lemma heft (x:H): Integrable (fun t:ℝ=> (δ n t:ℂ) • S.E t.toNNReal x) μ:=by
 have hx:Continuous (fun t:ℝ=> S.E t.toNNReal x):=(S.continuousE x).comp continuous_real_toNNReal
 have he:Continuous (thermalMass n):=by unfold thermalMass; fun_prop
 refine ((mass_set n).norm.mul_const ‖x‖).mono ((continuous_ofReal.comp he).smul hx |>.aestronglyMeasurable) ?_
 apply Eventually.of_forall; intro t; rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (show 0 ≤ ‖thermalMass n t‖ * ‖x‖ by positivity)]
 exact mul_le_mul_of_nonneg_left (((S.E _).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (S.shrinks _))) (norm_nonneg _)

def StampPower : H.Op := LinearMap.mkContinuous (σ:= RingHom.id ℂ) {
    toFun x:= ∫ t:ℝ, ((thermalMass n t):ℂ) • S.E t.toNNReal x ∂ μ
    map_add' u v:=by simp_rw [map_add,smul_add,integral_add (heft ..) (heft ..)]
    map_smul' c x:=by simp_rw [map_smul,smul_comm _ c, integral_smul]; rfl
  } (∫ t:ℝ,‖thermalMass n t‖∂ μ) (fun x=> show ‖∫ t:ℝ, (δ n t:ℂ) • S.E t.toNNReal x ∂ μ‖ ≤ _ from (norm_integral_le_integral_norm _).trans (by
    rw [← integral_mul_const]; refine integral_mono (heft ..|>.norm) ((mass_set n).norm.mul_const _) (fun t=>?_)
    rw [norm_smul,Complex.norm_real]; exact mul_le_mul_of_nonneg_left (((S.E _).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (S.shrinks _))) (norm_nonneg _)))

lemma meter (x:H) : StampPower S n x= ∫ t:ℝ, (δ n t:ℂ) • S.E t.toNNReal x ∂ μ:=rfl

private def ramp(j:Axis)(v:E4):ℂ:= ↑((1+v j)^(n+1):ℝ)
private lemma ramp_up : HasTemperateGrowth (ramp n j):=by
 have h: (fun v:E4=> v j) = (fun v:E4=>inner ℝ (basis j) v):=by simp_rw [basis_inner]
 have he: HasTemperateGrowth (fun v:E4=> v j):=by rw [h]; fun_prop
 exact hasTemperateGrowth_ofReal.comp (((HasTemperateGrowth.const 1).add he).pow _)

def winter (j:Axis) (n:ℕ) : Probe E4 →L[ℂ] Probe E4:= SchwartzMap.smulLeftCLM ℂ (ramp n j)
lemma winter_eq (g:Probe E4)(p:E4): winter j n g p=(↑((1+p j)^(n+1):ℝ):ℂ)*g p:=by
 unfold winter; rw [SchwartzMap.smulLeftCLM_apply]; rfl; exact ramp_up _

private lemma on_pilot (u:Probe E4)(x:H) :
   inner ℂ x (SNAG.send S.unit u (StampPower S n x))=
      ∫ p:E4, (1/(1+p j)^(n+1):ℝ) • u p ∂(S.ℚmeasure.diagonal x):=by
 let ν:= S.ℚmeasure.diagonal x
 let f(t:ℝ):= (δ n t:ℂ) • S.E t.toNNReal x
 rw [meter, ←ContinuousLinearMap.integral_comp_comm (SNAG.send S.unit u) (heft S n x), ←integral_inner ((Φ u).integrable_comp (heft S n x))]
 simp_rw [map_smul,inner_smul_right]
 let K(t:ℝ)(p:E4):= (thermalMass n t * Real.exp (-t*p j)) • u p
 calc
  _= ∫ t,(∫ p:E4, K t p∂ ν)∂ μ:=by
    refine integral_congr_ae ((ae_restrict_mem measurableSet_Ioi).mono fun t (ht:0 < t)=>?_); dsimp only; rw [paid S u t ht.le x]
    unfold K; simp_rw [mul_smul]; rw [integral_smul]; exact Complex.real_smul.symm
  _= ∫ p:E4, (∫ t,K t p∂ μ)∂ ν:= integral_integral_swap (by
    have he: Continuous (Function.uncurry K):=by unfold Function.uncurry K thermalMass; fun_prop
    refine ((mass_set n).norm.mul_prod (u.integrable («μ»:=ν)).norm).mono he.aestronglyMeasurable ?_
    apply (MeasureTheory.Measure.ae_prod_iff_ae_ae ?_).mpr
    refine (ae_restrict_mem measurableSet_Ioi).mono fun t (ht:0<t)=> (S.bright x).mono fun p hp=> ?_
    · change ‖K t p‖ ≤ ‖‖thermalMass n t‖ * ‖u p‖‖; unfold K; rw [norm_smul,norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le,Real.norm_of_nonneg (by positivity : 0 ≤ ‖thermalMass n t‖ * ‖u p‖)]
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht.le) hp))) (norm_nonneg _)
    have ht:Continuous (thermalMass n):=by unfold thermalMass; fun_prop
    exact isClosed_le he.norm (((ht.norm.comp continuous_fst).mul (u.continuous.norm.comp continuous_snd)).norm) |>.measurableSet)
  _=_:=integral_congr_ae ((S.bright x).mono (fun y h=>by simp only [K,integral_smul_const,pocket n (y j) h]))

/-- Norm-tested on the FULL vector. -/
lemma worth (g:Probe E4): (SNAG.send S.unit (winter j n g)).comp (StampPower S n)= SNAG.send S.unit g:=by
 apply symmetrize_eq
 intro x; rw [ContinuousLinearMap.comp_apply,on_pilot,sent_money _ S.joint]
 apply integral_congr_ae; filter_upwards [S.bright x] with p hp
 have ht:0<1+p j:=by linarith only [hp]
 simp only [winter_eq,Complex.real_smul]; rw [←mul_assoc,← ofReal_mul,one_div,inv_mul_cancel₀ (pow_ne_zero _ ht.ne'),ofReal_one,one_mul]
end YM.SatinJets
