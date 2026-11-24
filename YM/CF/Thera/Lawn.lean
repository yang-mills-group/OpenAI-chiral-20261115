import YM.CF.Fock.Invoice
import YM.CF.Matter.Rep
import YM.Gauge.Casimir
set_option autoImplicit false
noncomputable section
namespace YM.CF.Thera
open Filter Function MeasureTheory Gauge Matrix Fock SU Finset NormedSpace
open scoped Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace
abbrev V:=SU.group.Mat
lemma check_h {n:Type*}[Fintype n][DecidableEq n](x: Matrix n n ℂ)(t:ℝ): HasDerivAt (fun t:ℝ=>Matrix.det (exp (t • x))) (Matrix.trace x * Matrix.det (exp (t • x))) t:=by
 let f(z:ℂ):=exp (z • x); let A:=f ↑t
 let H(y:Matrix n n ℂ) : exp y*exp (-y) =1:=by
   letI: NormedAlgebra ℚ (Matrix n n ℂ):=NormedAlgebra.restrictScalars ℚ ℂ _; have h:=exp_add_of_commute (Commute.refl y).neg_right; rw [add_neg_cancel] at h; exact h.symm.trans exp_zero
 have hx:IsUnit A:=live_of (H ((t:ℂ) • x))
 have he(i j:n): HasDerivAt (fun z:ℂ=>f z i j) ((A*x) i j) (↑t:ℂ):=by
   let V:Matrix n n ℂ→ₗ[ℂ]ℂ := ⟨⟨fun x=>x i j,fun a b=>rfl⟩,fun a b=>rfl⟩
   exact V.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (t:ℂ) (hasDerivAt_exp_smul_const x (t:ℂ)) -- order?
 have hi: HasDerivAt (fun z:ℂ=>Matrix.det (f z)) _ (↑t:ℂ):=det_der hx he
 have hp(r:ℝ): exp (r • x)=f r :=by unfold f; rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]; rfl
 simp_rw [hp]; rw [←mul_assoc,(live hx).2,one_mul] at hi; exact hi.comp_ofReal -- tune
lemma league {x:V}: x∈SU.group.lie ↔ star x= -x ∧ Matrix.trace x=0:=by
 rw [Gauge.mem_lie]; constructor
 · intro h; refine ⟨Gauge.generates_skew _ h,?_⟩
   have he : (fun t:ℝ=> Matrix.det (exp (t • x)))=fun t=>1:=by funext t; obtain ⟨u,e⟩:= h t; rw [←e]; exact fund_det u
   have hx:= check_h x 0; rw [he,zero_smul, exp_zero,Matrix.det_one,mul_one] at hx; exact hx.unique (hasDerivAt_const _ _)
 rintro ⟨h,H⟩ t; let A:=exp (t • x)
 letI : NormedAlgebra ℚ V := NormedAlgebra.restrictScalars ℚ ℂ _; have hv:A∈unitary V := exp_mem_unitary_of_mem_skewAdjoint (show star (t • x)= -(t • x) from by rw [star_smul,h,star_trivial,smul_neg])
 have he: Matrix.det A=1:=by
   let f(t:ℝ):=Matrix.det (exp (t • x)); have hh:=intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=f) (f':=fun _=>0) (a:=0) (b:=t) (fun i _=> by have ht:=check_h x i; rw [H,zero_mul] at ht; exact ht) (by simp); simp only [Pi.zero_apply, intervalIntegral.integral_zero,f,zero_smul,exp_zero, det_one] at hh; exact sub_eq_zero.mp hh.symm
 exact ⟨⟨⟨A,hv⟩,he⟩,rfl⟩
end YM.CF.Thera
