import YM.SU5.Reconstruction.Sleet.Spend
import YM.SU5.Reconstruction.UVPrice.Walls
/-! # Real power simulation budget from time observation -/
set_option autoImplicit false
noncomputable section
namespace YM.ConePrice.Storm
open Function Set Filter Metric MeasureTheory Measure Complex Sail Spectral Analysis InnerProductSpace Multiplier OS Semigroup Picket
open scoped Topology NNReal ENNReal Real ComplexOrder InnerProductSpace Classical BigOperators

variable {D:Type*}(μ:D→ℝ)(p:∀ u,0≤ μ u) {H:Hilbert} {j:Axis} (S:OS.Semigroup H j)
local notation "F₀" t:max=> S.E (Real.toNNReal (μ t))
include p
lemma timestep (c:D→ℂ)(s:Finset D)(C:ℝ)
    (h: ∀ i:ℝ,0 ≤ i→ ‖∑ t∈s,c t*(Real.exp (-(μ t)*i):ℂ)‖≤C): ‖∑ t∈s,c t • F₀ t‖≤ C:=by
 let K(t:D)(i:E4):= (Real.exp (-(μ t)*max 0 (i j)):ℂ)
 have k(t:D):Registers S.ℚmeasure (K t) (F₀ t):= by
    have ht:= Roy.costT S (Real.toNNReal (μ t))
    unfold Roy.favor at ht; rw [Real.coe_toNNReal _ (p t)] at ht; exact ht
 have he(s:Finset D): Registers S.ℚmeasure (∑ i∈s,c i • K i) (∑ i∈s,c i • F₀ i):= by
    induction s using Finset.induction_on with
    | empty=> rw [Finset.sum_empty,Finset.sum_empty]; exact Registers.none _ 
    | insert i s ih h=>rw [Finset.sum_insert ih,Finset.sum_insert ih]; exact ((k i).scale _).add h
 refine (he s).fare ((norm_nonneg _).trans (h 0 le_rfl)) (fun i=>?_); simp only [Finset.sum_apply,Pi.smul_apply]; exact h _ (le_max_left ..)
lemma timeEarn (x y:H)(C:ℝ)(v:‖x‖*‖y‖≤ C): Voucher μ (fun z=> inner ℂ x ((F₀ z) y)) C:=by
 intro c s M m
 have ht:=timestep μ p S c s M m; let Q: H.Op:=∑ i∈s,c i • F₀ i
 have hM:0≤M:= (norm_nonneg _).trans ht
 simp only
 rw [show ∑ i∈s,c i * inner ℂ x ((F₀ i) y) = inner ℂ x (Q y) from ?_]
 swap
 · unfold Q; simp_rw [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,inner_sum,inner_smul_right] -- sig
 apply (norm_inner_le_norm ..).trans; calc
   _ ≤ ‖x‖ * (M*‖y‖):= mul_le_mul_of_nonneg_left ((Q.le_opNorm y).trans (mul_le_mul_of_nonneg_right ht (norm_nonneg _))) (norm_nonneg _)
   _ ≤ C*M:= (by rw [mul_left_comm,mul_comm C]; exact mul_le_mul_of_nonneg_left v hM)
end YM.ConePrice.Storm
