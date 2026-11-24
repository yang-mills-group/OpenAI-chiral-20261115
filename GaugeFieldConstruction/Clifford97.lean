import GaugeFieldConstruction.Announcement
/-!
# γ_B for (97) action. Actual Axis cost. H vector output with SO sign.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Flux.One
open Cauchy Matrix Function Finset
open scoped Matrix BigOperators
open CF (grading gammaOp SpinIdx Op)

def rotary (Ω : Ortho.Skew) : Op SpinIdx := (1/4:ℂ) • (∑ i : Axis, ∑ j : Axis,(Ω.val j i : ℂ) • (gammaOp j * gammaOp i))
lemma skewP (Ω : Ortho.Skew) (i j) : Ω.val i j= - Ω.val j i := congr_arg (fun a : M4=>a j i) (show star Ω.val=-Ω.val from Ω.property)
lemma rotary_star (Ω) : star (rotary Ω)= -rotary Ω := by
  simp only [rotary, star_smul,star_sum, star_mul,(CF.gammaAdj _).star_eq]
  rw [Finset.sum_comm,← smul_neg]; norm_num [← Finset.sum_neg_distrib]
  congr 1; ext1 a; apply Finset.sum_congr rfl; intro b _; nth_rw 1 [skewP]; simp
lemma zero_gamma (i : Axis) (b) : Cauchy.block (gammaOp i) b b=0 := by ext s t; cases b <;> fin_cases i <;> fin_cases s <;> fin_cases t <;> rfl
lemma lift_fee (Ω : Ortho.Skew) (k : Axis) : rotary Ω*gammaOp k-gammaOp k * rotary Ω = ∑ i:Axis,(Ω.val i k:ℂ) • gammaOp i := by
  let A : Lattice:= Ω.val
  let G:=gammaOp
  have ht (i j) : G j*G i * G k - G k *(G j*G i)=(if i=k then (2:ℂ) • G j else 0) - if j=k then (2:ℂ) • G i else 0 := by
    split_ifs with p q
    · subst i; subst j; rw [show G k * G k=1 from CF.gammaOne ..,one_mul,mul_one]
      simp
    · subst i; rw [mul_assoc,show G k * G k=1 from CF.gammaOne .., ← mul_assoc (G k), show G k * G j= -(G j*G k) from CF.gammaSwap _ _ (Ne.symm q), neg_mul, mul_assoc, show G k*G k=1 from CF.gammaOne k]; simp [two_smul]
    · subst j; rw [← mul_assoc (G k) (G k) (G i),mul_assoc (G k) (G i), show G i * G k= -(G k*G i) from CF.gammaSwap _ _ p, mul_neg, ← mul_assoc, show G k * G k=1 from CF.gammaOne ..]; simp [sub_eq_add_neg,two_smul]
    rw [mul_assoc (G j), show G i * G k= -(G k * G i) from CF.gammaSwap _ _ p, mul_neg, ← mul_assoc (G j), show G j * G k= -(G k*G j) from CF.gammaSwap _ _ (by assumption)]; simp [mul_assoc]
  change ((1/4:ℂ) • (∑ i:Axis,∑ j:Axis,(A j i:ℂ) • (G j * G i))) * G k - G k * ((1/4:ℂ) • (∑ i:Axis,∑ j:Axis,(A j i:ℂ) • (G j * G i)))= _
  rw [smul_mul_assoc,mul_smul_comm, ← smul_sub]; simp_rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,smul_mul_assoc,mul_smul_comm,← smul_sub,ht,smul_sub,smul_ite,smul_zero, Finset.sum_sub_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [Finset.sum_comm (f:=fun i j=> if i=k then _ else (_:Op SpinIdx))]; simp only [sum_ite_eq',mem_univ, ↓reduceIte,← Finset.sum_sub_distrib, Finset.smul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [show A k i= - A i k from skewP ..]; change _ = (↑(A i k):ℂ) • G i; simp only [Complex.ofReal_neg,smul_smul]; rw [← sub_smul,smul_smul]; congr 1; ring

lemma main (Ω) (a b : Spin) : Cauchy.block (rotary Ω) false false a b= theta Ω.val false a b := by
  have he (i) : Cauchy.block (gammaOp i) true false=star (cliff i) := by rw [← gamma_price,← star_block,(CF.gammaAdj _).star_eq]
  have hv (i j) : (gammaOp j*gammaOp i) (Cauchy.band false a) (Cauchy.band false b) =(cliff j*star (cliff i)) a b:= by
    change Cauchy.block (gammaOp j * gammaOp i) false false a b=_; rw [product_block,he,gamma_price,zero_gamma,zero_mul,zero_add]
  change rotary Ω _ _=_; simp only [rotary,theta,Matrix.sum_apply, Matrix.smul_apply,smul_eq_mul,hv]; rfl
lemma misc (Ω) (a b : Spin) : Cauchy.block (rotary Ω) true true a b = -theta Ω.val true b a := by
  have he (i) : Cauchy.block (gammaOp i) true false=star (cliff i) := by rw [← gamma_price,← star_block,(CF.gammaAdj _).star_eq]
  have hv (i j) : (gammaOp j*gammaOp i) (Cauchy.band true a) (Cauchy.band true b)= (star (cliff j)*cliff i) a b:=by
    change Cauchy.block (gammaOp j * gammaOp i) true true a b=_; rw [product_block,he,gamma_price,zero_gamma,zero_mul,add_zero]
  change rotary Ω _ _=_; simp only [rotary,theta,Matrix.sum_apply, Matrix.smul_apply,smul_eq_mul,hv]; rw [← mul_neg, Finset.sum_comm]; congr 1
  simp only [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
  change ↑(Ω.val _ _) * ((star (cliff _) * cliff _) a b) = _; nth_rw 1 [skewP]; rw [Complex.ofReal_neg, neg_mul]; congr 2
  rw [Matrix.mul_apply]; exact Finset.sum_congr rfl (fun c _=>mul_comm (star (Hij i c a)) (Hij j c b))
lemma label_fee (Ω : Ortho.Skew) (k : Axis) (a b : Spin):
    (∑ c:Spin, theta Ω.val false a c * Hij k c b) + (∑ c:Spin,Hij k a c*theta Ω.val true b c)= ∑ i:Axis,(Ω.val i k:ℂ)* Hij i a b := by
  have h := congr_arg (fun G : Op SpinIdx=> Cauchy.block G false true a b) (lift_fee Ω k)
  change Cauchy.block (rotary Ω*gammaOp k) false true a b-Cauchy.block (gammaOp k*rotary Ω) false true a b=_ at h
  simp only [product_block,gamma_price,zero_gamma,mul_zero,zero_add,add_zero,zero_mul] at h
  rw [Matrix.mul_apply, Matrix.mul_apply] at h
  simp_rw [main,misc,mul_neg,Finset.sum_neg_distrib,sub_neg_eq_add] at h
  simp only [Cauchy.block, Matrix.submatrix_apply,Matrix.sum_apply, Matrix.smul_apply] at h -- after rewrite?
  rw [show ∑ i:Axis,(Ω.val i k:ℂ)* Hij i a b=∑ i:Axis,(↑(Ω.val i k):ℂ)*gammaOp i (Cauchy.band false a) (Cauchy.band true b) from Finset.sum_congr rfl fun i _=> congr_arg _ (show Hij i a b=gammaOp i _ _ from congr_arg (fun T:Cauchy.M2=>T a b) (gamma_price i).symm)]
  exact h
end YM.GaugeFieldConstruction.Flux.One
