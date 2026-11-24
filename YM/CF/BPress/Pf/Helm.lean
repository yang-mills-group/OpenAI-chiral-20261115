import YM.CF.BPress.Pf.Abid
/-! This evaluation of positive log uses power expansion about a fixed cost-scaled point. For `Lost` nodes use directly negative series. Sign of price there even inside finite-volume excursions; no exponential of substituted absolute pressure. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Pf
open Function Filter NormedSpace Finset Fock Spin Spin.Quad Branch Spin.Pledge MeasureTheory
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {I:Type}[Fintype I][LinearOrder I][Nonempty I]{P Q A C:Op I}{c d a:ℝ}
namespace Helm
lemma bill_p (h:‖A‖<1): Real.exp (pencil A).trace.re=‖(1+A).det‖:=by rw [← Fock.factor _ h,tally_log h, Complex.norm_exp]
-- scaling for positive log powers

def helm (a:ℝ)(P:Op I):= pencil (a⁻¹ • P-1)+ Real.log a • (1:Op I)
lemma scaledN(h:0<a) (u:‖a⁻¹ • A-1‖<1) : Real.exp (helm a A).trace.re= ‖A.det‖:=by
 rw [helm,Matrix.trace_add, Complex.add_re,Real.exp_add, bill_p u,add_sub_cancel,Matrix.trace_smul, Matrix.trace_one]; rw [show a⁻¹ • A=((a⁻¹:ℝ):ℂ) • A by ext; simp [Complex.real_smul], Matrix.det_smul,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (inv_pos.mpr h).le, inv_pow]; simp only [Complex.real_smul,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.natCast_re,mul_comm (Real.log a), Real.exp_nat_mul, Real.exp_log h]; field_simp -- tune
lemma affords(h:0<c)(u:c<a)(p:c • (1:Op I) ≤ A)(t:A≤a • (1:Op I)) : ‖a⁻¹ • A-1‖≤1-c/a∧ 1-c/a<1:=by obtain ⟨x,b,y⟩:=normal_calc h u p t; rw [norm_sub_rev]; exact ⟨y,b⟩
lemma rcpt (P:Pledge)(h:0<c)(t:c<a)(v:0≤ d) : ∃ V:Pledge, ∀ {Y I D:Type}[Fintype I][LinearOrder I][Nonempty I][Fintype Y][DecidableEq Y][TopologicalSpace D]{b:Stage Y I D Empty}{A:Raw D I}, Capacity b d→ P.Costs b A→ (∀ x,c • (1:Op I) ≤ A x ∧ A x≤ a • 1) → V.Costs b (fun x=> helm a (A x)):=by
 let Q:= (P.scales ‖a⁻¹‖).plus unary; obtain ⟨V,u⟩:= Q.zoom v (k:=1-c/a) (sub_pos.mpr ((div_lt_one (h.trans t)).mpr t)) (sub_lt_self _ (div_pos h (h.trans t))); refine ⟨V.plus (unary.scales ‖Real.log a‖),?_⟩; intro X I D _ _ _ _ _ _ b A B U S; exact Costs.plus ((u B (show Q.Costs b (fun x=>a⁻¹ • A x-1) from Costs.sub (Costs.scale U _) Costs.one) fun i=> (affords h t (S i).1 (S i).2).1).2) (Costs.scale Costs.one _)

lemma stock (h: ‖A‖<1) : Summable (fun k:ℕ=> bcoef k • A^(k+1)):=by
 let f(k:ℕ):=‖A‖^(k+1); have ha:= (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg _) h); refine ha.of_norm_bounded ?_; intro i; rw [norm_smul]; exact (mul_le_of_le_one_left (norm_nonneg _) (bc_norm _)).trans (norm_pow_le ..)
lemma signTerm (x:ℕ): bcoef x=(-1:ℝ)^x*(1/(x+1)):= by -- tune token
 unfold bcoef; have hp(t:ℝ):(-t)^x=(-1:ℝ)^x*t^x:=by rw [←mul_pow,neg_one_mul]
 rw [funext hp]; rw [intervalIntegral.integral_const_mul,integral_pow]; simp
lemma BelowTerm (h: 0 ≤ A)(i:ℕ): bcoef i • (-A)^(i+1) ≤ 0:=by
 have he:(-A)^(i+1)=(-1:ℝ)^(i+1) • A^(i+1):=by rw [←smul_pow,neg_one_smul]; -- tune
 rw [he,smul_smul,signTerm];
 have hp:(-1:ℝ)^i*(1/(i+1))*(-1)^(i+1) = -(1/(i+1)):=by
    rw [pow_succ,mul_neg,mul_one,mul_neg,mul_right_comm,←mul_pow]; simp
 rw [hp,neg_smul]; exact neg_nonpos.mpr (smul_nonneg (by positivity) (CStarAlgebra.pow_nonneg h i.succ))
lemma below (h:0≤A)(e:‖A‖<1): pencil (-A)≤ -A:=by
 let F(i:ℕ):=bcoef i • (-A)^(i+1); have he: Summable F:= stock ((norm_neg _|>.le).trans_lt e); change (∑' i,F i)≤_; rw [←he.sum_add_tsum_nat_add 1,sum_range_one,show F 0= -A by simp [F,bcoef]]; exact add_le_of_nonpos_right (tsum_nonpos (fun i=>BelowTerm h _))
lemma reflect(H: ‖A‖<1)(U:UNI I): pencil (twist U A)=twist U (pencil A):=by
 unfold pencil; let T: Op I →L[ℝ] Op I:=(twist U).toAlgEquiv.toLinearEquiv.toLinearMap.toContinuousLinearMap
 change _=T _; rw [T.map_tsum (stock H)]; refine tsum_congr fun i => ?_; rw [←map_pow,map_smul]; rfl
end Helm
end YM.CF.BPress.Pf
