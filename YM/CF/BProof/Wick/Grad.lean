import YM.CF.BProof.Wick.Dyke

/-! Complex-valued derivatives in phase path (real parameter). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Wick
open Function Filter NormedSpace Fock Finset Branch Align
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
section
variable {I:Type*}[Fintype I][DecidableEq I](x:Ket I)
def actCL (I:Type*) [Fintype I][DecidableEq I]: Op I→L[ℝ](Ket I→L[ℝ]Ket I):= ( (ContinuousLinearMap.restrictScalarsL ℂ _ _ ℝ ℝ).comp (((Matrix.toEuclideanCLM (n:=I) (𝕜:=ℂ)).toAlgEquiv.toLinearEquiv.toLinearMap).toContinuousLinearMap.restrictScalars ℝ)) -- tune
variable {A:ℝ→ Op I}{p:ℝ→Ket I}{S:Op I}{r:ℝ}{x}
lemma act_der (h:HasDerivAt A S r)(e:HasDerivAt p x r) : HasDerivAt (fun i=> acts (A i) (p i)) (acts S (p r)+acts (A r) x) r:=by
 let U:=actCL I; exact (U.hasFDerivAt.comp_hasDerivAt r h).clm_apply e
lemma act_der_const (h:HasDerivAt A S r)(x: Ket I): HasDerivAt (fun i=> acts (A i) x) (acts S x) r:=by simpa only [map_zero,add_zero] using act_der h (hasDerivAt_const r x)
end
variable {I:Type*}[Fintype I][LinearOrder I] {S:ℝ→Op I}{T: Op I}{r:ℝ}
lemma wager (h:HasDerivAt S (T*S r) r) (s:Finset I) : HasDerivAt (fun i=>wedge (S i) s) (acts (dg T) (wedge (S r) s)) r:=by
 induction s using induction_on_min with
 | empty=> simp_rw [wedge_empty,dg_veil]; exact hasDerivAt_const ..
 | insert i s g ih=>
   let p(x:ℝ):= acts (S x) (basisKet i); let A(x:ℝ):=create (p x); let v:= acts T (p r); have hz: HasDerivAt A (create v) r:= by
      let X:= (create (n:=I)).toContinuousLinearMap.restrictScalars ℝ; exact X.hasFDerivAt.comp_hasDerivAt r (show HasDerivAt p v r from (show _ from (act_der_const h (basisKet i)).congr_deriv (act_mul ..))) -- tune
   have he:= act_der hz ih; simp_rw [wedge_min _ s i g]; convert he using 1; let b:= wedge (S r) s; change acts (dg T) (acts (A r) b)=acts (create v) b+acts (A r) (acts (dg T) b); rw [←act_mul, show dg T*A r=create v+A r*dg T from eq_add_of_sub_eq (lever T _),act_add,act_mul (A r)]
lemma drift_der (h: HasDerivAt S (T*S r) r) (b:Wave I): HasDerivAt (fun i=>acts (quant (S i)) b) (acts (dg T) (acts (quant (S r)) b)) r:=by rw [← basis_expand b]; simp_rw [map_sum,map_smul,quant_column]; exact HasDerivAt.fun_sum (fun i _=>(wager h i).const_smul (b.ofLp i)) -- tune
end YM.CF.BProof.Wick
