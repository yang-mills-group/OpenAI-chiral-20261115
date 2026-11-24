import GaugeFieldConstruction.Warpcast
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 28000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix Classical Matrix.Norms.L2Operator
open Fock Tulip Lat Spire Phase Cube
open FlightFlux Fluxim
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
local notation "GS"=> SU.group
variable {n:Side}{p: BudgetPoint}{Q: InkD n}{o:Skye.Seat n}{X:Scree.Hub n}{h c:ℝ}
namespace Flot
open scoped NNReal
-- Basis mechanisms
abbrev BasisH:= EuclideanSpace.basisFun SU.group.ColorIndex ℝ
def locusC(z:SU.group.ColorIndex)(x:ComG):Gem:=⟨fun i j=> x.val i j z,fun i j=>by change _ + x.val j i z=0; exact congrArg (fun x:SU.group.Color=>x z) (x.property i j)⟩
def locusT(z:SU.group.ColorIndex)(x:ComT):Sut:= by
 refine ⟨fun i j k=> x.val i j k z, fun i j k=>?_,fun i j k=>?_⟩
 · exact congrArg (fun x:SU.group.Color=>x z) (x.property.1 i j k)
 exact congrArg (fun x:SU.group.Color=>x z) (x.property.2 i j k)
lemma trade_Z(C:ComG): C= ∑ i:SU.group.ColorIndex, hem (locusC i C) (BasisH i):=by
 apply Subtype.ext; ext i j k; rw [Submodule.coe_sum]; simp_rw [Finset.sum_apply]; -- use expansion
 have he:=BasisH.sum_repr (C.val i j); exact congrArg (fun x:SU.group.Color=> x k) (by
    refine he.symm.trans (sum_congr rfl (fun i t=> ?_)); rfl) -- tune
lemma trade_X(C:ComT): C= ∑ i:SU.group.ColorIndex, loomH (locusT i C) (BasisH i):=by
 apply Subtype.ext; ext i j k x; rw [Submodule.coe_sum]; simp_rw [Finset.sum_apply]; have he:=BasisH.sum_repr (C.val i j k); exact congrArg (fun y:SU.group.Color=>y x) he.symm -- tune
variable (e₀:PressB p X Q h c)(p₀:0≤ h)
local notation "γ"=> X.val.1
include e₀ p₀
lemma plating_Z (x y:ComG) : luke o Q p x y = ∑ i: SU.group.ColorIndex,fave p o Q (locusC i x) (locusC i y):=by
 calc _= ∑ i:SU.group.ColorIndex,∑ j:SU.group.ColorIndex,luke o Q p (hem (locusC i x) (BasisH i)) (hem (locusC j y) (BasisH j)):= by nth_rw 1 [trade_Z x]; rw [map_sum,ContinuousLinearMap.sum_apply]; apply sum_congr rfl; intro i _; exact (congrArg _ (trade_Z y)).trans (map_sum ..)
      _=_:=by simp_rw [formC_Ps e₀ p₀]; apply sum_congr rfl; intro i _; rw [sum_eq_single i]
              · rw [real_inner_self_eq_norm_sq,OrthonormalBasis.norm_eq_one,one_pow,Complex.ofReal_one,mul_one]
              · intro j _ p; rw [BasisH.orthonormal.inner_eq_zero (Ne.symm p), Complex.ofReal_zero, mul_zero] -- tune
              simp
set_option maxHeartbeats 75000 in
lemma plating_X (x:ComG)(y:ComT) : klem o Q p x y=∑ i: SU.group.ColorIndex, claw p o Q (locusC i x) (locusT i y):=by
 calc _= ∑ i:SU.group.ColorIndex,∑ j:SU.group.ColorIndex,klem o Q p (hem (locusC i x) (BasisH i)) (loomH (locusT j y) (BasisH j)):=by nth_rw 1 [trade_Z x]; rw [map_sum,ContinuousLinearMap.sum_apply]; apply sum_congr rfl; intro i _; exact (congrArg _ (trade_X y)).trans (map_sum ..)
      _=_:=by simp_rw [formT_Ps e₀ p₀]; apply sum_congr rfl; intro i _; rw [sum_eq_single i]
              · rw [real_inner_self_eq_norm_sq,OrthonormalBasis.norm_eq_one,one_pow,Complex.ofReal_one,mul_one]
              · intro j _ p; rw [BasisH.orthonormal.inner_eq_zero (Ne.symm p), Complex.ofReal_zero, mul_zero]
              simp
lemma symm_f : (fave p o Q).flip=fave p o Q:=by ext i j <;> first| exact ploy_herm e₀ p₀ ..| exact congrArg _ (ploy_herm e₀ p₀ ..) -- tune ext
lemma skim : 0 ≤ c:= (eraF _ _ e₀ p₀ _ (ping_f p _)).grade
omit e₀ p₀
private lemma shoot_cost (x:Gem): ‖hem x (spike SU.group)‖ ≤ ‖x‖:=by
 apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2; intro i; apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2; intro j; change ‖x.val i j • spike SU.group‖≤_; rw [norm_smul,spike_norm Thera.yet_one,mul_one]; exact (norm_le_pi_norm (x.val i) _).trans (norm_le_pi_norm x.val i)
private lemma soot_cost(x:Sut): ‖loomH x (spike SU.group)‖ ≤ ‖x‖:=by
 apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2; intro i; apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2; intro j; apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2; intro k; change ‖x.val i j k • spike SU.group‖≤_; rw [norm_smul,spike_norm Thera.yet_one,mul_one]; exact (norm_le_pi_norm (x.val i j) _).trans ((norm_le_pi_norm (x.val i) _).trans (norm_le_pi_norm x.val _))
lemma price_desk {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]{V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V](f:E→L[ℝ] V)(p:0< c)(v:0≤h)(z:∀ x:E,‖x‖≤ c→‖f x‖≤h) : ‖f‖≤ c⁻¹ *h:=by
 apply ContinuousLinearMap.opNorm_le_bound _ (by positivity); intro x; rcases eq_or_lt_of_le (norm_nonneg x) with H|H
 · rw [show x=0 from norm_eq_zero.mp H.symm,map_zero,norm_zero,norm_zero,mul_zero]
 let a:= c*‖x‖⁻¹; have ha:0<a:=by unfold a; positivity
 have hp:‖a • x‖=c:=by rw [norm_smul, Real.norm_of_nonneg ha.le]; unfold a; field_simp
 have hx:= z (a • x) hp.le; rw [map_smul,norm_smul,Real.norm_of_nonneg ha.le,← one_mul h] at hx; unfold a at hx; field_simp at hx ⊢; linarith only [hx]
lemma price_heap {E F:Type*}[NormedAddCommGroup E][NormedAddCommGroup F][NormedSpace ℝ E][NormedSpace ℝ F](p:0< c)(v:0≤ h)(f:leadF E F)(z:∀ x:E,‖x‖≤ c→∀ y:F, ‖y‖≤c→ ‖f x y‖≤ h): ‖f‖≤ c⁻¹ * (c⁻¹*h):= price_desk f p (by positivity) (fun i a=> price_desk _ p v (z i a))
include e₀ p₀
lemma ploy_priced (a b:tangD n)(e:p.dirBound γ a)(v:p.dirBound γ b): ‖ploy Q a b‖≤c:=by rw [ploy_iter]; apply (eraF Q _ e₀ p₀ _ (ping_f p _)).token 2 ((by decide:2≤6).trans p.order_ge); intro i; fin_cases i <;> first|exact e|exact v -- tune
lemma bill_G : ‖fave p γ Q‖ ≤ 2500*c:=by
 refine (price_heap (show 0<(1/50:ℝ) by norm_num) (skim e₀ p₀) (fave p γ Q) (fun i l j e=>?_)).trans_eq (by ring); exact ploy_priced e₀ p₀ _ _ (formC_life (hem i (spike SU.group)) γ p ((shoot_cost i).trans l)) (formC_life (hem j (spike SU.group)) γ p ((shoot_cost j).trans e))
lemma bill_T : ‖claw p γ Q‖ ≤ 2500*c:=by
 refine (price_heap (show 0<(1/50:ℝ) by norm_num) (skim e₀ p₀) (claw p γ Q) (fun i l j e=>?_)).trans_eq (by ring); exact ploy_priced e₀ p₀ _ _ (formC_life (hem i (spike SU.group)) γ p ((shoot_cost i).trans l)) (formT_life (loomH j (spike SU.group)) γ p ((soot_cost j).trans e))
end Flot
end YM.CF.TableF
end
