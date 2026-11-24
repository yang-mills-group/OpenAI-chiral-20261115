import YM.CF.Neige.Niche
set_option autoImplicit false
noncomputable section
namespace YM.CF.Neige
open Char Summit
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric Newt Jet
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching
open Push.SectorMeasure Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad PatchReads
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{A A':Stores S}{F F':Forest S.ratio}{k k':S.Choices} {V W:Config G c}{x C:ℝ}{r l:ℕ}
 {Y: LinkArray G (Frozen A x F)}{Y':LinkArray G (Frozen A' x F')}{o:Site c}
variable {α E:Type} [Fintype α][DecidableEq α] [NormedAddCommGroup E][NormedSpace ℝ E] {p:α→Site c}{a:ℕ} {K v d s t:ℝ} {n:ℕ}
open Finset Filter
def varyP(n:ℕ)(C:ℝ):= C+(2^n*C)^2
def delve(n:ℕ)(C:ℝ):= (2^n*C)^3+(2^n*C)^4+(2^n*C)^5
variable {W Z B : E→ Shelf α}{x₀:E}
lemma pitchM(h:Protected n W x₀ (C*t))(hC:0 ≤ C)(ht:0 ≤ t)(hp:t ≤ 1):Protected n (punt∘W) x₀ (varyP n C * t):=by
 have hh:=climb h 2; have hb:=wrap_r hh (3/8); have hv:=wrap_r h (-1/2); have ht:= attach hv hb
 refine (ht.mono ?_).germ (Eventually.of_forall fun y=>by dsimp only; unfold punt Function.comp;  dsimp only; rw [smul_neg,← neg_smul, neg_div]) -- tune
 rw [abs_of_nonpos (by norm_num : (-1/2:ℝ) ≤ 0), abs_of_nonneg (by norm_num : 0 ≤ (3/8:ℝ)),varyP]; let u:= C*t; have he :0 ≤ u:=mul_nonneg hC ‹_›
 apply le_trans (add_le_add (show -(-(1:ℝ)/2)*(C*t) ≤  u from mul_le_of_le_one_left he (by norm_num)) (show (3/8:ℝ)*_ ≤  _ from mul_le_of_le_one_left (sq_nonneg _) (by norm_num))) ?_
 rw [add_mul, ← mul_assoc, mul_pow]; exact add_le_add (show u ≤ C*t from le_rfl) (mul_le_mul_of_nonneg_left (pow_le_of_le_one (show 0≤t by assumption) hp (show (2:ℕ)≠0 by norm_num)) (sq_nonneg _))
lemma relic_p(h:Protected n W x₀ (C*t))(hC:0 ≤ C)(ht:0 ≤ t)(hp:t ≤ 1): Protected n (relic∘W) x₀ (delve n C*t^3):=by
 have he(i:ℕ)(hi:3 ≤ i)(a:ℝ)(ha:|a|  ≤ 1):Protected n (fun y=> a • W y^i) x₀ ((2^n*C)^i*t^3):=by
    apply (wrap_r (climb h i) a).mono; apply (mul_le_of_le_one_left (by positivity) ha).trans; rw [← mul_assoc,mul_pow]; exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ht hp hi) (by positivity)
 exact (((attach (attach (he 3 le_rfl (5/8) (by norm_num)) (he 4 (by norm_num) (-15/64) (by norm_num))) (he 5 (by norm_num) _ (show |(9/64:ℝ)| ≤ 1 by norm_num))).mono (le_of_eq (by unfold delve; ring))).germ (Eventually.of_forall (fun y=> congr_arg paintO (report _).symm)))
def fuseQ (X A:Shelf α): Shelf α:= X.transpose * A * X
def perturb(X A:Shelf α):= fuseQ X A - 1
def white(X A:Shelf α):= X*port (perturb X A)
def legacy(X A:Shelf α):= perturb (white X A) A
lemma width_s (X A:Shelf α)(h:A.IsSymm): (perturb X A).IsSymm:=by unfold perturb; apply Matrix.IsSymm.sub _ Matrix.isSymm_one; unfold fuseQ Matrix.IsSymm; rw [transpose_mul,transpose_mul,h.eq,transpose_transpose,Matrix.mul_assoc]
lemma turnQ(X A:Shelf α)(h:A.IsSymm): (white X A).transpose=port (perturb X A)*X.transpose:=by unfold white; rw [transpose_mul,(plat (width_s X A h)).eq]
lemma legacy_eq(X A:Shelf α)(h:A.IsSymm): legacy X A = relic (perturb X A):=by
 unfold legacy; rw [perturb,fuseQ,turnQ X A h]; unfold relic; rw [show 1+perturb X A=fuseQ X A from add_sub_cancel ..]; unfold fuseQ white; simp only [Matrix.mul_assoc]
lemma fuseP (hW: Protected n W x₀ K)(ht: Protected n (fun y=>(W y).transpose) x₀ K)(hp: Protected n B x₀ C) : Protected n (fun y=> fuseQ (W y) (B y)) x₀ (2^n*(2^n*K*C)*K):= fuseN (fuseN ht hp) hW
lemma unitInv (X A:Shelf α)(h:‖paintO (τ:=α) (perturb X A)‖ ≤ 1/2)(hp:‖paintO X.transpose‖ ≤ C)(hr:‖paintO A‖ ≤ C):
 IsUnit X.det ∧ ‖paintO X⁻¹‖ ≤  2*C*C:=by
 obtain ⟨ht,hm⟩:=low_invP (fuseQ X A) h
 let Q:=fuseQ X A; let P:=Q⁻¹ * X.transpose * A; have hP : P*X=1:=by rw [show P*X=Q⁻¹*Q from by unfold P; change _*_=_*(X.transpose*A*X); simp only [Matrix.mul_assoc], Matrix.nonsing_inv_mul _ ht]
 have hc:0  ≤  C:= (norm_nonneg _).trans hp
 refine ⟨Matrix.isUnit_det_of_left_inverse hP,?_⟩
 rw [Matrix.inv_eq_left_inv hP]; unfold P; rw [paint_mul,paint_mul]; apply (ContinuousLinearMap.opNorm_comp_le ..).trans
 apply mul_le_mul _ hr (norm_nonneg _) (by positivity); exact (ContinuousLinearMap.opNorm_comp_le ..).trans (mul_le_mul hm hp (norm_nonneg _) (by norm_num))
end YM.CF.Neige
