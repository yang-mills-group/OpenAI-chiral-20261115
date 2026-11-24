import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace Factory
open Function MeasureTheory ProbabilityTheory Real Filter
open scoped Topology ENNReal NNReal RealInnerProductSpace BigOperators Classical
variable {E:Type*} [NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E]
variable (ν:ℝ)
abbrev wheel (t:ℝ):=exp (ν*t^2/2)
lemma differentiator: deriv (wheel ν)= fun t=>ν*t*wheel ν t:=by
 funext x
 unfold wheel
 rw [_root_.deriv_exp (by fun_prop)]
 simp only [deriv_div_const, differentiableAt_const, differentiableAt_fun_id, Nat.cast_ofNat,
        DifferentiableAt.fun_pow, deriv_fun_mul, deriv_const', zero_mul, deriv_fun_pow,
        Nat.add_one_sub_one, pow_one, deriv_id'', mul_one, zero_add]; ring
lemma industry(n:ℕ):iteratedDeriv (n+2) (wheel ν) 0= ν*(n+1)*iteratedDeriv n (wheel ν) 0:=by
 rw [iteratedDeriv_succ',differentiator,show (fun t=>ν*t*wheel ν t)=(fun t=>ν*(t*wheel ν t)) from funext (fun _=> mul_assoc ..),iteratedDeriv_const_mul_field] -- tune for left const
 rw [iteratedDeriv_fun_mul (by fun_prop) (by unfold wheel; fun_prop)]; simp_rw [iteratedDeriv_fun_id_zero]
 simp [mul_assoc]
variable (L:StrongDual ℝ E)
local notation "μ*"=>stdGaussian E
local notation "τ"=>‖L‖^ (2:ℕ)
lemma exportT (n:ℕ): (∫ i,L i^n∂μ*)=iteratedDeriv n (wheel τ) 0:=by
 let g:= gaussianReal 0 (τ).toNNReal
 have h:(μ*).map L=g:=by unfold g; rw [IsGaussian.map_eq_gaussianReal]; simp [variance_dual_stdGaussian]
 rw [show (∫ i,L i^n∂μ*)= (∫ x:ℝ,x^n ∂g) from (by rw [←h]; rw [integral_map L.continuous.aemeasurable (Measurable.aestronglyMeasurable (by fun_prop))])]; change (∫ x:ℝ, ((fun x:ℝ=>x)^n) x ∂ g)=_; rw [←iteratedDeriv_mgf_zero (μ:=g)]
 · rw [mgf_fun_id_gaussianReal]; simp only [Real.coe_toNNReal _ (sq_nonneg _), zero_mul,zero_add]
 · unfold g; simp
lemma twice :(∫ i,L i^2∂ μ*)=τ:=by rw [exportT,show 2=0+2 from rfl,industry]; simp [wheel]
lemma tetra :(∫ i,L i^4∂ μ*)=3*‖L‖^4:=by rw [exportT,show 4=2+2 from rfl,industry,← exportT L, twice L]; push_cast; ring
lemma sexta :(∫ i,L i^6∂ μ*)=15*‖L‖^6:=by rw [exportT,show 6=4+2 from rfl,industry,← exportT L, tetra L]; push_cast; ring
lemma norm_int(n:ℕ): Integrable (fun i=>‖L i‖^n) μ*:= (IsGaussian.memLp_dual (μ:=μ*) L n (by simp)).integrable_norm_pow'
lemma pow_int(n:ℕ): Integrable (fun i=> L i^n) μ*:=by
 have h:=norm_int L n
 apply h.mono' ((L.continuous.pow n).aestronglyMeasurable)
 exact Eventually.of_forall fun _=> (norm_pow _ n).le
end Factory
