import YM.CF.DPress.Chess.Floor.Porch
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Chess
open Function Filter Lattice RG Wilson MeasureTheory ProbabilityTheory Push.GridApprox FD Skye Tree Precision Rush Spire Scree Lift Transit Bough Turn Push.SectorMeasure Tulip
open Fock Finset Girt Sermon
open Cube (More assembly node)
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal Bough ComplexOrder Matrix.Norms.L2Operator YM.CF.BPress
attribute [local instance] opCStarAlgebra
variable (W:Wall) {n m:Side}{ℓ d r:ℕ}{β u k:ℝ}{P:Loom n}
namespace Slit
open Complex
-- exact magnitude log-pricing (only on the Auxiliary). Includes the hidden real-impart condition.
private lemma realCs {x y q:ℝ} (p:0≤x)(g:0≤y)(v:0 ≤ q)(h:∀ t:ℝ,0 ≤ x-2*t*q+t^2*y*q) : q ≤ x*y:=by
 rcases g.eq_or_lt with rfl|g
 · by_contra! u; rw [mul_zero] at u; have he:=h ((x+1)/q); field_simp at he; nlinarith -- tune
 have ht:=h (1/y); field_simp at ht; nlinarith
lemma own {x y a b:ℂ}(p:0≤x)(q:0≤y)(h:∀ k:ℂ,0≤ x+k*a+star k*b+(star k*k)*y): ‖a‖^2≤ ‖x‖*‖y‖:=by
 let M:= ‖x‖; let N:=‖y‖; have he(k):0 ≤ (M:ℂ) + k*a+ star k * b+(star k*k)*(N:ℂ):= (by rw [←show x=(M:ℂ) from eq_coe_norm_of_nonneg p,←show y=(N:ℂ) from eq_coe_norm_of_nonneg q]; exact h k); have hu:= (Complex.nonneg_iff.mp (he 1)).2; have hv:= (Complex.nonneg_iff.mp (he Complex.I)).2; have hb:b=star a :=by
    simp [mul_im] at hu hv; apply Complex.ext <;> simp [Complex.star_def] <;> linarith
 change ‖a‖^2 ≤ M*N; apply realCs (norm_nonneg _) (norm_nonneg _) (sq_nonneg _); intro t; have hz:= he (- (t:ℂ)* star a); rw [hb] at hz; let Q:=normSq a; have ht:star a*a=(Q:ℂ):= normSq_eq_conj_mul_self.symm; suffices h:0 ≤ (M-2*t*Q+t^2*N*Q :ℝ) by rw [←normSq_eq_norm_sq]; exact h
 rw [show (↑M :ℂ)+(- (t:ℂ)*star a)*a + star (- (t:ℂ)*star a)*star a + (star (-(t:ℂ) *star a)*(-(t:ℂ)*star a))*(N:ℂ)=( ( (M-2*t*Q+t^2*N*Q:ℝ)):ℂ) from ?_] at hz; exact (Complex.nonneg_iff.mp hz).1
 push_cast; rw [← ht,star_mul,star_star,star_neg, show star (t:ℂ)=(t:ℂ) from Complex.conj_ofReal t]; ring
end Slit
end YM.CF.DPress.Chess
