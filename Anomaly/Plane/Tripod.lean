import Anomaly.Plane.Trapeze
/-! pay formulas on receipts of (128) polynomial. Cross coins on Wick salary.
-/
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option quotPrecheck false
noncomputable section
namespace YM.Regis.Head.Brecht.Pier
open Function Filter Metric MeasureTheory NormedSpace ProbabilityTheory Finset
open GeometryP
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace Classical
variable {E: Type}[NormedAddCommGroup E][InnerProductSpace ℝ E][MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E] {ι:Type*} [Fintype ι] (x y z w:E) {D k:ℝ}
local notation "μ"=>stdGaussian E
variable { K:Type} [Fintype K]
section linear
variable {X : (Fin 2 → K)→ E→ℝ}{Y:(Fin 2 → K)→ E→ℝ}(U: (Fin 2 → K)→ℂ)(V:(Fin 2 → K)→ℂ)
def treasury (U: (Fin 2 → K)→ℂ)(X:(Fin 2 → K)→E→ℝ)(x:E):=∑ i,X i x • U i
lemma tally_I (p:∀ i,Integrable (X i) μ): (∫ x, treasury U X x ∂μ)=∑ i,(∫ x,X i x∂μ) • U i:=by unfold treasury; rw [integral_finsetSum _ (fun i _=>(p i).smul_const _)]; simp_rw [integral_smul_const]
def tally (f g:E→ℂ):= ∫ x, f x*g x∂μ
lemma pairing_K(v:E): treasury U X v* treasury V Y v=∑ i,∑ j,(X i*Y j) v • (U i*V j):=by
 rw [treasury,treasury,sum_mul_sum]; -- need direction? sum_mul_sum theorem a b s
 apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; rw [smul_mul_assoc, mul_smul_comm]; exact (mul_smul ..).symm
lemma integral_k (p:∀ i j,Integrable (X i*Y j) μ): Integrable (fun x=>treasury U X x*treasury V Y x) μ:=by simp_rw [pairing_K]; apply integrable_finsetSum; intro i _; exact integrable_finsetSum univ fun j _=>(p i j).smul_const _
lemma launch (p:∀ i j,Integrable (X i*Y j) μ): tally (treasury U X) (treasury V Y)= ∑ i,∑ j,(∫ x,X i x * Y j x∂μ) • (U i*V j):=by
 unfold tally; simp_rw [pairing_K]; have hp(i j:(Fin 2 → K)): Integrable (fun x=>(X i*Y j) x • (U i*V j)) μ:=(p i j).smul_const _; rw [integral_finsetSum univ (fun i _=> integrable_finsetSum univ (fun j _=>hp i j))]; simp_rw [integral_finsetSum _ (fun j _=>hp _ j),integral_smul_const,Pi.mul_apply]
end linear
variable (U: (Fin 2 → K) → ℂ)(F G:K→E)
local notation "Φ" x:max y:max z:max w:max=>(mats_bold x y).integrable_mul (mats_bold z w)
private lemma tuneEQ : ∀ i:(Fin 2 → K),Integrable (mats (F (i 0)) (F (i 1))) μ:=fun i=> (mats_bold _ _).integrable (show (1:ℝ≥0∞)≤2 by norm_num)
abbrev curly:= treasury U (fun i:(Fin 2→K)=> mats (F (i 0)) (F (i 1)))
lemma values_K : (∫ x,curly U F x ∂μ)=∑ i:(Fin 2 → K),A (F (i 0)) (F (i 1)) • U i:=by
 rw [curly,tally_I U (tuneEQ F)]; apply sum_congr rfl; intro i _; exact congrArg (· • U i) (appraisal (F (i 0)) (F (i 1))) -- simp_rw
abbrev spun (F G : K→E)(s t:K) :ℝ:= A (F s) (G t)
def twinB (R:K→K→ℝ)(s t:(Fin 2 → K)):ℝ:= R (s 0) (t 0)*R (s 1) (t 1)+R (s 0) (t 1)*R (s 1) (t 0)
def lodging (Y:K→K→ℝ)(U V:(Fin 2 → K)→ℂ):= ∑ i,∑ j,twinB Y i j • (U i*V j)
lemma spurn(V:(Fin 2 → K)→ℂ) : tally (curly U F) (curly V G)=(∫ x,curly U F x ∂μ)*(∫ x,curly V G x∂μ)+ lodging (spun F G) U V:=by
 rw [values_K,values_K,sum_mul_sum]; unfold curly lodging; rw [launch (X:=fun i:(Fin 2→K)=> mats (F (i 0)) (F (i 1))) (Y:=fun i:(Fin 2→K)=> mats (G (i 0)) (G (i 1))) _ _ (fun i j=> Φ _ _ _ _),←sum_add_distrib]; apply sum_congr rfl; intro i _; rw [←sum_add_distrib]; apply sum_congr rfl; intro j _; rw [smul_mul_assoc,mul_smul_comm,←mul_smul,←add_smul]; apply congrArg (· • _); exact (canticle ..).trans (by rw [add_assoc]; rfl)
abbrev choppy(k:ℝ):= treasury U (fun i:(Fin 2 → K)=> pat (F (i 0)) (F (i 1)) k)
lemma yank (V:(Fin 2 → K)→ℂ)(p:1 ≤ k)(h:∀ i,‖F i‖≤D)(u:∀ i,‖G i‖≤ D) : ‖tally (choppy U F k) (choppy V G k)-tally (curly U F) (curly V G)‖ ≤ (∑ i,∑ j,fare4 D k * (‖U i‖*‖V j‖)):=by
 have hx:0 < k:=by linarith
 have he(i j:(Fin 2 → K)): Integrable (pat (F (i 0)) (F (i 1)) k *pat (G (j 0)) (G (j 1)) k) μ:=(pat_bold hx).integrable_mul (pat_bold hx)
 unfold choppy curly; rw [launch U V he,launch U V (fun i j=> Φ _ _ _ _), ←sum_sub_distrib]; simp_rw [←sum_sub_distrib,←sub_smul]
 refine (norm_sum_le ..).trans (?_); apply sum_le_sum; intro i _; refine (norm_sum_le ..).trans ?_; apply sum_le_sum; intro j _; rw [norm_smul,Real.norm_eq_abs,norm_mul]; refine mul_le_mul_of_nonneg_right (?_) (by positivity)
 let Rν:Fin 4→ E:=![F (i 0), F (i 1), G (j 0), G (j 1)]; have ht(P:Fin 4): ‖Rν P‖ ≤ D:=by fin_cases P <;> first|exact h _|exact u _
 exact peace4 p Rν _ ht
lemma relief (V:(Fin 2 → K)→ℂ)(p:1 ≤ k)(h:∀ i,‖F i‖≤D)(u:∀ i,‖G i‖≤ D) : ‖tally (choppy U F k) (choppy V G k)-tally (curly U F) (curly V G)‖ ≤ fare4 D k*((∑ i,‖U i‖)*(∑ i,‖V i‖)):=by rw [sum_mul_sum]; simp_rw [mul_sum]; exact yank U F G V p h u
end YM.Regis.Head.Brecht.Pier
