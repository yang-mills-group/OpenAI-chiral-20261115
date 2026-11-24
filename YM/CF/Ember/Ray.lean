import YM.CF.Ember.Veil
set_option autoImplicit false
noncomputable section
namespace YM.CF.Ember
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
lemma dateA : Matrix.trace Aop=2:=by rw [Adef]; norm_num [Matrix.trace,SpinIdx, Fin.sum_univ_succ,grading]
private def S(a:Axis):Momentum:=step a
private def Z(a:Axis):=zen (S a)
private lemma s_r(a): star (S a)=S a:=by ext i; by_cases h:i=a<;>simp [S,h]
private lemma z_q(a): star (Z a)= -Z a:= zenStar (S a) (s_r a)
private lemma z_h(a): Z a*Z a= -1:=by unfold Z; rw [zenSq]; simp [prodM,S]
private lemma z_a(a:Axis)(p:Momentum): Z a * zen p+zen p*Z a=(-(2*p a)) • 1:=by
 have ht:=zenSq (S a+p); unfold Z; rw [zenP,add_mul,mul_add,mul_add,zenSq,zenSq] at ht
 have hx: prodM (S a+p) (S a+p)= prodM (S a) (S a)+prodM p p+2*p a:=by unfold prodM; simp only [Pi.add_apply,add_mul,mul_add,sum_add_distrib]; simp [S,mul_ite,ite_mul]; ring
 rw [hx] at ht; linear_combination (norm:=module) ht
private def nails(a):=Aop * Z a * Z 1 * Aop
private lemma stud(a): nails a+star (nails a)=(-(2*S 1 a)) • Aop:=by
 let X:=Z a*Z 1+Z 1*Z a
 have hp := z_a a (S 1)
 have ht: Aop*X*Aop=nails a+star (nails a):=by unfold X nails; simp only [mul_add,add_mul,star_mul,z_q,Aadj]; simp [mul_assoc]
 rw [← ht,show X=_ from hp]; simp only [Matrix.mul_smul,Matrix.smul_mul,mul_one,AOne]
private lemma n_a(a): Aop*Z a*Z 1=Z a*Z 1*Aop:=by
 change Aop*zen (S a)*zen (S 1)= _; rw [zenA,mul_assoc,zenAA]; unfold Z; rw [mul_assoc]
private lemma nos(a): nails a*star (nails a)=Aop:=by
 have ht:nails a= Aop*(Z a*Z 1):=by unfold nails; rw [n_a,mul_assoc _ Aop,AOne,← n_a,mul_assoc]
 rw [ht,star_mul,star_mul,Aadj,z_q,z_q]; simp only [neg_mul, mul_neg,neg_neg]; rw [mul_assoc, ← mul_assoc (Z a*Z 1),mul_assoc (Z a),← mul_assoc (Z 1),z_h]; simp [← mul_assoc (Z a),z_h,AOne]
private def gash(a:Axis)(x:Gaia)(z:ℝ): Op SpinIdx:= (1/2:ℂ) • ((2*(x 1:ℂ)) • Aop-(2*(z:ℂ)) • nails a)
private lemma booths(a x z): Aop * gash a x z=gash a x z∧gash a x z * Aop=gash a x z:=by
 unfold gash nails; constructor
 · simp only [mul_sub,Matrix.mul_smul,←mul_assoc,AOne]
 simp only [sub_mul,Matrix.smul_mul,mul_assoc,AOne]
private lemma n_sf (i a:Axis) (b:ℂ): (step i : Momentum) a= if i=a then 1 else 0:=by rw [Lattice.step_apply]; by_cases h:i=a<;>simp [h,Ne.symm]
private lemma stall(a:Axis)(x:Gaia)(z:ℝ): gash a x z*star (gash a x z)=(x 1^2+z^2+(if a=1 then 2*x 1*z else 0):ℂ) • Aop:=by
 let p:ℂ:=x 1; let t:ℂ:=z; have ht := stud a
 have h:Aop*nails a=nails a:=by unfold nails; rw [←mul_assoc, ←mul_assoc, ←mul_assoc,AOne];
 have u : nails a*Aop=nails a:=by unfold nails; rw [mul_assoc _ Aop Aop,AOne]
 have hp:Aop*star (nails a)=star (nails a):=by nth_rw 1 [← Aadj]; rw [← star_mul,u]
 unfold gash; simp only [star_smul,star_sub,Aadj]
 simp only [star_div₀,star_ofNat, star_one,star_mul']; simp [Matrix.mul_smul,Matrix.smul_mul,mul_sub,sub_mul, AOne, hp,u,nos] -- tune
 have hk := eq_sub_of_add_eq (a:=star (nails a)) ((add_comm _ _).trans ht)
 rw [hk]; by_cases he:a=1 <;> simp [S,he, Matrix.mul_smul] <;> module

variable {n:Type*}[Fintype n][DecidableEq n]
private lemma quakeH(T:Op n)(h:star T=T)(a:Axis)(x:Gaia)(z:ℝ):MountH T (river x) (spark a z)=(gash a x z ⊗ₖ T):=by
 let t:ℂ:=z; let p:=river x; have he:(river x) 1=(x 1:ℂ):=rfl
 unfold MountH; rw [riv_phys,show spoon (river x) (spark a z)=p+spark a (2*t) from by rw [spoon,spark_plus]]
 have hp: physical p:= riv_phys x
 unfold Lent flint; rw [op_star_kron,op_kron_mul,op_star_kron,op_kron_mul,h,star_one,mul_one,one_mul,← Matrix.add_kronecker]; congr 1
 change (Aop*Z 1)*star ((1/2:ℂ) • (Aop*zen p))+((1/2:ℂ) • (Aop*zen (p+spark a (2*t))))*star (Aop*Z 1)=_
 rw [star_smul, star_mul,star_mul,Aadj, z_q,zenStar _ hp]; simp only [star_div₀,star_ofNat, star_one]; unfold gash nails spark
 rw [zenP,zenS]; change _ + ((1/2:ℂ) • (Aop*(zen p+(2*t) • Z a)))*_=_
 simp only [Matrix.smul_mul,Matrix.mul_smul,mul_add,add_mul,neg_mul, mul_neg,smul_add, ←mul_assoc]
 have ht := z_a 1 p; have hv:= congr_arg (fun y : Op SpinIdx=> Aop*y*Aop) ht; simp only [← mul_assoc,mul_add,add_mul, Matrix.smul_mul,Matrix.mul_smul,AOne,mul_one] at hv; -- tune
 rw [show p 1=(x 1:ℂ) from he] at hv; unfold t; linear_combination (norm:=module) -(1/2:ℂ) • hv
lemma sunray(T:Op n)(h:star T=T)(a:Axis)(x:Gaia)(z:ℝ):
 oval T (river x) (spark a z)= 32*(Matrix.trace (T*T))*(x 1^2+(z:ℂ)^2+(if a=1 then 2*x 1*z else 0)) / (((‖x‖^2:ℝ):ℂ)*(((‖x‖^2+4*z*(x a)+4*z^2:ℝ)):ℂ)):=by
 unfold oval; rw [riv_phys,spark_star,show star ((z:ℂ))=z from Complex.conj_ofReal z]; rw [quakeH _ h]; rw [op_star_kron,h]
 simp only [tipH,bins,Matrix.smul_mul,Matrix.mul_smul,op_kron_mul,mul_one,one_mul,(booths a x z).1,(booths a x z).2]
 rw [stall]; rw [river,xParity]
 have hp: prodM (spoon (axes (exileE x)) (spark a z)) (spoon (axes (exileE x)) (spark a z)) = ((‖x‖^2+4*z*x a+4*z^2:ℝ):ℂ):=by
    rw [← geode_sum]; unfold prodM spoon spark
    simp only [Pi.add_apply, Pi.smul_apply,smul_eq_mul,axes,mul_add,add_mul,sum_add_distrib,Lattice.step_apply,mul_ite,ite_mul]; simp -- tune
    push_cast; ring
 simp only [hp,Matrix.trace_smul,Matrix.trace_kronecker,dateA,smul_eq_mul]; ring
end YM.CF.Ember
