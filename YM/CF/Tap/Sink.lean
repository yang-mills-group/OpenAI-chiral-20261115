import YM.CF.Spire.Eager
import YM.CF.Pec.Sorrel
import YM.CF.Reef.Opus
import YM.CF.Ember.Can
set_option autoImplicit false
noncomputable section
namespace YM.CF.Tap
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
abbrev petal (i:Axis):Op SpinIdx:= (Complex.I/2:ℂ) • (Aop*gammaOp i)
-- actual half-slope spin basis
private def slice(x:Op (SpinIdx×Slot))(i j:Slot):Op SpinIdx:=fun a b=> x (a,i) (b,j)
def spot (x:Op SpinIdx)(i:Axis):ℂ:= ![x 0 3+x 1 2,Complex.I*(x 0 3-x 1 2),x 0 2-x 1 3,-Complex.I*(x 0 2+x 1 3)] i
-- explicit tests. improve perfor
private lemma A_matrix:Aop=Matrix.diagonal (![1,1,0,0]):=by rw [Adef]; ext i j; fin_cases i<;>fin_cases j<;>norm_num [grading,Matrix.one_apply,Matrix.diagonal_apply]
private lemma oMatrix: 1-Aop=Matrix.diagonal (![0,0,1,1]):=by rw [A_matrix]; ext i j; fin_cases i<;>fin_cases j<;>norm_num [Matrix.one_apply,Matrix.diagonal_apply]
private lemma pet_gamma (i:Axis):Aop*gammaOp i= gammaOp i*(1-Aop):=by simp only [Adef,Matrix.mul_smul,Matrix.smul_mul,mul_sub, add_mul, mul_add,mul_one,one_mul, gradingSwap]; module
lemma pet_up {s:Signed}{U:UNI SpinIdx}(h:JetS s false false U)(i:Axis): twist U (petal (s.perm i))=hush (s.flip i) (petal i):=by
 rw [petal,twist_scalar,map_mul,show twist U Aop=Aop from angleX h true,show twist U (gammaOp (s.perm i))=_ from h.cliff i]; cases h:s.flip i <;>simp [h,petal]
private lemma pet_star(i:Axis):star (petal i)=(-(Complex.I/2):ℂ) • ((1-Aop)*gammaOp i):=by
 rw [petal,star_smul,star_mul,(gammaAdj _).star_eq,Aadj, sub_mul,one_mul,pet_gamma,mul_sub,mul_one]; norm_num; module
lemma pet_down {s:Signed}{U:UNI SpinIdx}(h:JetS s false true U)(i:Axis): twist U (petal (s.perm i))= -star (hush (s.flip i) (petal i)):=by
 conv_lhs=> rw [petal,twist_scalar,map_mul,show twist U Aop=1-Aop from angleX h true,show twist U (gammaOp (s.perm i))=_ from h.cliff i]
 cases h:s.flip i <;>simp only [h,hush_true,hush_false, star_neg, pet_star,mul_neg, smul_neg,neg_smul,neg_neg]
private lemma spot_smul(P:Op SpinIdx)(i:Axis)(z:ℂ):spot (z • P) i=z*spot P i:=by fin_cases i <;> simp [spot] <;> ring
private lemma spot_add(P Q:Op SpinIdx)(i: Axis): spot (P+Q) i=spot P i+spot Q i:=by fin_cases i <;> simp [spot] <;> ring
set_option maxHeartbeats 600000 in
lemma spot_i(i j:Axis):spot (petal i) j=if i=j then 1 else 0:=by
 fin_cases i<;>fin_cases j <;> norm_num [spot,pet_star,petal,oMatrix,A_matrix,Matrix.trace,Matrix.mul_apply,SpinIdx,gammaOp,Fin.sum_univ_succ,Matrix.diagonal_apply] <;> simp only [show (3:Fin 4)=Fin.succ 2 from rfl,show (2:Fin 4)=Fin.succ 1 from rfl,show (2:Fin 3)=Fin.succ 1 from rfl, Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_zero]<;> norm_num <;> ring_nf <;> norm_num [Complex.I_sq]
set_option maxHeartbeats 800000 in
private lemma spot_p(P:Op SpinIdx):∑ i:Axis,spot P i • petal i=Aop*P*(1-Aop):=by
 rw [oMatrix]; ext i j; fin_cases i<;>fin_cases j<;> simp only [petal,A_matrix,Matrix.sum_apply,Matrix.smul_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.diagonal_apply_eq, SpinIdx, Axis,Fin.sum_univ_succ]<;> norm_num [gammaOp,spot]<;> simp only [show (3:Fin 4)=Fin.succ 2 from rfl,show (2:Fin 4)=Fin.succ 1 from rfl,show (2:Fin 3)=Fin.succ 1 from rfl, Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_zero]<;> norm_num <;> ring_nf <;> norm_num [Complex.I_sq] <;> try ring
 all_goals rfl

def spaX(x:Op (SpinIdx×Slot))(i:Axis):Op Slot:= fun k j=> spot (slice x k j) i
lemma spa_v(i:Axis)(z:Op Slot)(j:Axis):spaX (petal i⊗ₖ z) j= if i=j then z else 0:=by
 ext a b; change spot _ _ = _; rw [show slice _ a b=z a b • petal i by ext; simp [slice,mul_comm]]
 rw [spot_smul]; rw [spot_i]; by_cases hz:i=j<;> simp [hz]
lemma spa_i(i:Axis):Injective (fun z:Op Slot=> petal i⊗ₖ z):= fun x y h=> by simpa [spa_v] using congrArg (spaX · i) h
lemma spa_s(i:Axis)(F:Axis→Op Slot): spaX (∑ j:Axis, petal j ⊗ₖ F j) i=F i:=by
 let X:Op (SpinIdx×Slot) →+ Op Slot:={
    toFun:=fun x=> spaX x i
    map_add':=fun x y=>by ext a b; exact spot_add _ _ _
    map_zero':=by ext a b; change spot 0 i=0; fin_cases i<;> simp [spot] }
 change X _=_; rw [map_sum]; simp_rw [show ∀ j, X (petal j⊗ₖ F j) = _ from fun j=> spa_v j _ i]; simp
lemma spa_p(X:Op (coneA Slot)): ∑ i:Axis, petal i⊗ₖ spaX X i=bins Slot * X * (1-bins Slot):=by
 have ht:1-bins Slot=(1-Aop)⊗ₖ (1:Op Slot):=by simp only [bins,sub_eq_add_neg,Matrix.add_kronecker,Matrix.one_kronecker_one,op_kron_neg]
 ext ⟨i,x⟩ ⟨j,y⟩; rw [ht]; have he:=Matrix.ext_iff.mpr (spot_p (slice X x y)) i j
 simp only [Matrix.sum_apply,Matrix.mul_apply, Matrix.smul_apply] at he; simp only [Matrix.sum_apply,Matrix.mul_apply, Matrix.kronecker_apply,show ∀ k : SpinIdx×Slot→ℂ,(∑ p,k p)=_ from fun k=>Fintype.sum_prod_type k,spaX,bins]
 conv_lhs => arg 2; intro i; rw [mul_comm]
 simp only [Matrix.one_apply, mul_ite, ite_mul, mul_one,mul_zero, zero_mul, Finset.sum_ite_eq,mem_univ,ite_true,Finset.sum_ite_eq']
 exact he
end YM.CF.Tap
