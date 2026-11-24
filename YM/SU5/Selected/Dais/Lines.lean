import YM.CF.Aroma.Cyclone
import YM.SU5.FiniteGaugeData.Pannier.Veldt
/-! Complex determinant price via segment. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Dais.Parity
open Function Filter Metric Finset Fock Lat Matrix MeasureTheory
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators ContDiff InnerProductSpace ComplexOrder
attribute [local instance] opCStarAlgebra
variable {I:Type*} [Fintype I][LinearOrder I][Nonempty I]
variable {A B C:Op I}{f:ℝ→Op I}{S:Finset I}{g r t e u:ℝ}
-- if Nonempty required cfc.
lemma remedy (p:0<r): (r • (1:Op I)).PosDef:=  PosDef.smul PosDef.one p
lemma renovate (p:0<r)(h:r • (1:Op I)≤ A) : A.PosDef:= by rw [←add_sub_cancel (r • (1:Op I)) A]; exact (remedy p).add_posSemidef (le_iff.mp h)
lemma eye_line (p:0<r)(h:r • (1:Op I)≤ A): ‖A⁻¹‖ ≤ r⁻¹:=by
 let X:=r • (1:Op I); have ht:A⁻¹≤X⁻¹:= by rw [Matrix.nonsing_inv_eq_ringInverse, Matrix.nonsing_inv_eq_ringInverse]; exact CStarAlgebra.ringInverse_le_ringInverse h ((remedy (I:=I) p).isStrictlyPositive)
 have hp:= (renovate p h).inv.posSemidef; rw [show X⁻¹=r⁻¹ • (1:Op I) from ?_] at ht; swap; · apply Matrix.inv_eq_right_inv; unfold X; rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm, one_mul,smul_smul,mul_inv_cancel₀ p.ne',one_smul] -- ambiguity
 have he:= CStarAlgebra.norm_le_norm_of_nonneg_of_le hp.nonneg ht; exact he.trans_eq (by rw [norm_smul,Real.norm_of_nonneg (by positivity),norm_one,_root_.mul_one])
lemma real_slope (u:f t = A)(p:A.PosDef)(h: HasDerivAt f B t): HasDerivAt (fun t=>Real.log (f t).det.re) (A⁻¹*B).trace.re t:=by
 subst A; have hp : (0:ℂ)< (f t).det:= p.det_pos; have ht:0 < (f t).det.re:= (Complex.lt_def.mp hp).1; have hh:(f t).det.im=0:= (Complex.lt_def.mp hp).2.symm
 have he:= Aroma.TaylorA p.isUnit h; have hg:= (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t he).log ht.ne'; apply hg.congr_deriv; change ((((f t)⁻¹ * B).trace * (f t).det).re / _) = _; simp only [Complex.mul_re,hh,mul_zero,sub_zero]; exact mul_div_cancel_right₀ _ ht.ne'
lemma east_line (p:0<r)(h:r • (1:Op I)≤ A) (v:0≤ e)(u:‖B‖≤ g)(z:‖B*cutM S‖≤e):
 ‖(A⁻¹*B).trace.re‖ ≤ r⁻¹*(Fintype.card I*e+((Sᶜ:Finset I).card:ℝ)*g):=by
 rw [Real.norm_eq_abs]; apply (Complex.abs_re_le_norm _).trans; let D:= A⁻¹ * B; have hp:‖A⁻¹‖≤ r⁻¹ := eye_line p h; let T:= r⁻¹; have ht:D=A⁻¹*B:=rfl; have hX:0 ≤ T:= inv_nonneg.mpr p.le
 have he(x: I) : ‖D x x‖≤ T*e + if x∈Sᶜ then T*g else 0:=by
    split
    · apply le_trans ((norm_entry D _ _).trans ((norm_mul_le ..).trans (mul_le_mul hp u (norm_nonneg _) hX))) (le_add_of_nonneg_left (mul_nonneg hX v)) -- parser
    next w=> rw [_root_.add_zero]; simp only [mem_compl,not_not] at w; rw [show D x x=(D*cutM S) x x from ?_]; swap; · simp [cutM,Matrix.mul_diagonal,w]
             refine (norm_entry _ _ _).trans ?_; rw [ht,mul_assoc]; exact (norm_mul_le ..).trans (mul_le_mul hp z (norm_nonneg _) hX)
 change ‖∑ x, D x x‖ ≤ _; apply (norm_sum_le ..).trans; refine (sum_le_sum (fun i _=> he i)).trans_eq ?_; rw [sum_add_distrib,← Finset.sum_filter]; simp only [filter_mem_eq_inter, univ_inter, sum_const,card_univ,nsmul_eq_mul]; unfold T; ring
lemma diff_charge (p:0<r)(h:r • (1:Op I)≤ A)(h':r • (1:Op I) ≤B) (v:0≤e)(u:‖B-A‖≤g)(z:‖(B-A)*cutM S‖≤e):
 Real.log (B.det.re) - Real.log (A.det.re) ≤ r⁻¹* (Fintype.card I*e+(Sᶜ:Finset I).card*g):=by
 let f(x:ℝ):= A + x • (B-A); let D:= Set.Icc (0:ℝ) 1
 let g₀(x:ℝ):=Real.log (f x).det.re; have hx: f 1=B:=by simp [f]; -- maybe simp
 have hz:f 0=A:=by simp [f]
 let F(x:ℝ):=((f x)⁻¹*(B-A)).trace.re
 have hp(x:ℝ)(z:x∈D): r • (1:Op I) ≤ f x:= by
    let Q:=(1-x) • A+x • B; have hu:f x= Q:=by unfold f Q; module
    rw [hu]; apply (add_le_add (smul_le_smul_of_nonneg_left h (sub_nonneg.mpr z.2)) (smul_le_smul_of_nonneg_left h' z.1)).trans'; exact le_of_eq (by module) -- unfold Q maybe reduction
 have he(x:ℝ)(z:x∈D): HasDerivAt g₀ (F x) x:= by
    refine real_slope rfl (renovate p (hp x z)) ?_; exact (((hasDerivAt_id' x).smul_const (B-A)).const_add A |>.congr_deriv (by simp))
 let M:=r⁻¹ * ((Fintype.card I:ℝ)* e+(Sᶜ:Finset I).card*g); have hg(x:ℝ)(s:x∈D):‖F x‖≤M:=east_line p (hp _ s) v u z
 have hK:= (convex_Icc (𝕜:=ℝ) (0:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le (fun x hx=> (he x hx).hasDerivWithinAt) hg (show (0:ℝ)∈D from ⟨le_rfl,zero_le_one⟩) (show (1:ℝ)∈D from ⟨zero_le_one,le_rfl⟩)
 unfold g₀ at hK; rw [hx,hz] at hK; simpa [Real.norm_eq_abs] using (hK.trans' (Real.le_norm_self _))
end YM.CF.Dais.Parity
#print axioms YM.CF.Dais.Parity.diff_charge
