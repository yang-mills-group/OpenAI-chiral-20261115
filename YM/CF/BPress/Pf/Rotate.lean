import YM.CF.BPress.Pf.Wick
import YM.CF.BPress.Spin.Basement
import Mathlib.Analysis.SpecialFunctions.Exponential
/-! Path derivatives for plog, general incl singular W compression. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Pf
open Function Filter NormedSpace Finset Fock Spin Spin.Quad
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {I:Type}[Fintype I][DecidableEq I][Nonempty I]{P Q A:Op I}{v r:ℝ}
namespace Rotate
lemma d_mult {T:ℝ→Op I}{k:ℝ→Ket I}{x:Ket I}(p:HasDerivAt T P v)(u:HasDerivAt k x v): HasDerivAt (fun t=> acts (T t) (k t)) (acts P (k v)+ acts (T v) x) v:=by
 let V:Op I →L[ℝ] Ket I→L[ℝ] Ket I:= (ContinuousLinearMap.restrictScalarsL ℂ _ _ ℝ ℝ).comp (((Matrix.toEuclideanCLM (𝕜:=ℂ) (n:=I)).toAlgEquiv.toLinearEquiv.toLinearMap.toContinuousLinearMap).restrictScalars ℝ)
 exact ((V.hasFDerivAt.comp_hasDerivAt _ p).clm_apply u)
lemma d_vector {T:ℝ→Op I}(p:HasDerivAt T P v)(x:Ket I): HasDerivAt (fun t=> acts (T t) x) (acts P x) v:=by
 have ht:= d_mult p (hasDerivAt_const v x); rw [map_zero,add_zero] at ht; exact ht
lemma exp_shift {T:ℝ→Op I}(p:HasDerivAt T P v)(e:∀ w,Commute (T w) (T v)) : HasDerivAt (fun t=> exp (T t)) (P*exp (T v)) v:=by
 let V:=T v; letI : NormedAlgebra ℚ (Op I) := NormedAlgebra.restrictScalars ℚ ℂ (Op I); have ht(x):exp (T x)=exp (T x-V)*exp V:=by rw [← exp_add_of_commute ((e x).sub_left (Commute.refl (T v))),sub_add_cancel]
 simp_rw [funext ht] -- issue recursion; target derivative exp(T v) also rewrites?
 apply HasDerivAt.mul_const; let Y:=fun t=>T t-T v; have hx: HasFDerivAt exp (1: Op I→L[ℝ] Op I) (Y v):= by unfold Y; rw [sub_self]; exact hasFDerivAt_exp_zero
 exact hx.comp_hasDerivAt _ (p.sub_const _)

variable {I:Type}[Fintype I][LinearOrder I][Nonempty I]{P Q A:Op I}
lemma d_wedge {T:ℝ→Op I}(p:HasDerivAt T (P*T v) v)(S:Finset I): HasDerivAt (fun t=> wedge (T t) S) (acts (dg P) (wedge (T v) S)) v:=by
 induction S using Finset.induction_on with
 | empty=> simp_rw [wedge_empty,dg_veil]; exact hasDerivAt_const ..
 | @insert i S e ih=>
   let a(t:ℝ):= acts (T t) (basisKet i); let F(t:ℝ):= create (a t); let Y:= wedge (T v) S; let G:= dg P; let C:= create (acts P (a v))
   have ht: HasDerivAt a (acts P (a v)) v:=by rw [show acts P (a v)=acts _ (basisKet i) from Eq.symm (act_mul P (T v) _)]; exact d_vector p _
   have hm:F= (↑create.toContinuousLinearMap ∘ a):=rfl
   have hy: HasDerivAt F C v:= ((create (n:=I)).toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt v ht
   simp_rw [wedge_any _ S i e]; rw [map_smul]; refine (HasDerivAt.const_smul (parity i S) (d_mult hy ih)).congr_deriv ?_
   congr 1; rw [←act_mul (F v), ←act_add, show C+F v*dg P=dg P*F v from (eq_add_of_sub_eq (lever P (a v))).symm, act_mul]; -- tune
lemma d_quant {T:ℝ→Op I}(p:HasDerivAt T (P*T v) v)(x:Wave I): HasDerivAt (fun t=> acts (quant (T t)) x) (acts (dg P) (acts (quant (T v)) x)) v:=by
 let q(i: Finset I):= x.ofLp i; rw [show x= ∑ i:Finset I,q i • basisKet i from (basis_expand x).symm]; simp_rw [map_sum,map_smul,quant_column]; exact HasDerivAt.fun_sum fun i _=> HasDerivAt.const_smul (q i) (d_wedge p i) -- name?
lemma d_shear(T:Op I)(h:T*T=0)(x:Wave I)(v:ℝ): HasDerivAt (fun t=> acts (quant (1+t • T)) x) (acts (dg T) (acts (quant (1+v • T)) x)) v:=by
 refine d_quant ?_ x; rw [mul_add,mul_one,Algebra.mul_smul_comm,h,smul_zero, add_zero]; simpa only [one_smul] using ((hasDerivAt_id' v).smul_const T).const_add (1:Op I) -- precedence
lemma d_real (K:Wave I)(v:ℝ){P Q L A:Op I}(h:Spin.Cellar.Pass P Q L A r)(p:‖v‖≤1) : let Yx:= Spin.Cellar.Pass.slide P Q L A; let Xt:= Spin.Basement.slip P Q L A; let M:= Xt v*Trans.pinv A (Yx v); HasDerivAt (fun t=> acts (quant (Yx t)) K) (acts (dg M) (acts (quant (Yx v)) K)) v :=by
 intro Yx Xt M; apply d_quant; have he : M*Yx v=Xt v :=by unfold M; rw [mul_assoc,(h.enjoy v p).paid]; unfold Xt Spin.Basement.slip; rw [add_mul,mul_assoc,mul_assoc Q, h.ray1',h.ray0']
 rw [he]; exact Spin.Basement.slide_ray ..

lemma c_comm(P Q:Op I): Commute (coupl P) (coupl Q):=by
 unfold Commute SemiconjBy; nth_rw 1 2 [show coupl P= (2:ℂ)⁻¹ • (∑ i,∑ j,P i j • (put i * put j)) from rfl];
 simp only [sum_mul,mul_sum,Algebra.smul_mul_assoc,Algebra.mul_smul_comm]; congr 1; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; rw [mul_assoc,put_coupl j,←mul_assoc,put_coupl i, mul_assoc]
lemma c_flow {T:ℝ→Op I}(p:HasDerivAt T P v): HasDerivAt (coupl ∘ T) (coupl P) v:=by
 let V: Op I→ₗ[ℂ] FC I:=
    { toFun:=coupl
      map_add' f g:=by change _=(2:ℂ)⁻¹ • _+ (2:ℂ)⁻¹ • _; unfold coupl squareP; simp [add_smul,sum_add_distrib,smul_add]
      map_smul' c f:=by unfold coupl squareP; simp only [Matrix.smul_apply,smul_eq_mul,mul_smul,RingHom.id_apply]; change _= c • _; simp_rw [← Finset.smul_sum]; rw [smul_comm] } -- tune
 exact (V.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt _ p
lemma d_pair {T:ℝ→Op I}(p:HasDerivAt T P v): HasDerivAt (pairWave ∘ T) (acts (coupl P) (pairWave (T v))) v:=by
 have hx:= d_vector (exp_shift (c_flow p) (fun x=> c_comm _ _)) (vacuum I); change HasDerivAt _ (acts (_* exp (coupl (T v))) _) _ at hx
 simp_rw [act_mul, comp_apply,stored] at hx; exact hx
end Rotate
end YM.CF.BPress.Pf
