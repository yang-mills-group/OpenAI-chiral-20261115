import YM.SU5.FiniteGaugeData.Trigonal.Lassi
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
/-! # Saturated exterior calculus. two Spin takers -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
noncomputable section
namespace YM.CF.Fock.Reduction.Plush
open Function Finset Module Complex
open scoped Matrix Matrix.Norms.L2Operator BigOperators
attribute [local instance] opCStarAlgebra
variable {ι:Type*}[LinearOrder ι][Fintype ι]{n:ℕ}
-- use general f vectors in FC.W. works even alias/zero.
local notation "V"=> FC ι
variable (a b:Fin n→ FC ι)
abbrev rollF(a:Fin n→ FC ι) := (List.ofFn a).prod
abbrev furlF(a:Fin n→ FC ι):=(List.ofFn a).reverse.prod
abbrev Cross(a b:Fin n→ FC ι):Prop:=∀ i j, antiB (a i) (b j)=0
abbrev Reform(a:Fin n→FC ι)(A:Op (Fin n)): Fin n→FC ι:=fun i=>∑ j:Fin n,A i j • a j
def Tile(a b:Fin n→FC ι):FC ι:= rollF (fun i=> a i*b i)
private lemma press (S: Type*) [AddCommGroup S][Module ℂ S] (f: AlternatingMap ℂ (Fin n→ℂ) S (Fin n)) (A:Op (Fin n)):let e:=Pi.basisFun ℂ (Fin n); f A=A.det • f e:=by
 intro e
 let W:= (Fin n→ℂ); let L:= LinearMap.toSpanSingleton ℂ S (f e)
 have he:f=L.compAlternatingMap e.det:=by
    refine Basis.ext_alternating e fun i h=>?_ ; let t:= Equiv.ofBijective i (Finite.injective_iff_bijective.1 h); change f (e ∘ ⇑t) = L (e.det (e ∘ ⇑t)); rw [AlternatingMap.map_perm, AlternatingMap.map_perm, Basis.det_self]; refine (congrArg (((Equiv.Perm.sign t :ℤ)) • ·) ?_).trans (map_zsmul L ..).symm; -- U.smul via coerces. Goal f e = L 1
    exact (one_smul ℂ _).symm
 rw [show f A=L (e.det A) from (congrArg (fun u: AlternatingMap ℂ W S (Fin n)=>u A) he), Basis.det_apply,show e.toMatrix A=Aᵀ from ?_, Matrix.det_transpose]; rfl
 ext i j; simp [e,Basis.toMatrix_apply]; -- tune
-- reorder witness covariance.S.Phi.
lemma Plush_roll (A:Op (Fin n))(t:Cross a a): rollF (Reform a A)= A.det • rollF a:=by
 let W:= Fin n→ℂ; let e:=Pi.basisFun ℂ (Fin n)
 let Z: (Fin n→ℂ) →ₗ[ℂ] V:= { toFun:=fun x=>∑ j,x j • a j, map_add':=fun i j=>by simp [add_smul,sum_add_distrib], map_smul':= fun i j=> by simp [mul_smul,smul_sum] }
 have h(x):Z x * Z x=0:=by
    have hh: antiB (Z x) (Z x)=0:=by change antiB (∑ j,x j • a j) (∑ j,x j • a j)=_; simp_rw [antiB_sum, antiB_sum',antiB_smul,antiB_smul',t,smul_zero,sum_const_zero]
    exact (smul_eq_zero_iff_right (by norm_num : (2:ℂ)≠0)).1 (show (2:ℂ) • (Z x * Z x)=0 from (two_smul ℂ _).trans hh)
 let L:= ExteriorAlgebra.lift ℂ ⟨Z,h⟩; let f:= L.toLinearMap.compAlternatingMap (ExteriorAlgebra.ιMulti ℂ n)
 have hp(x:Fin n→W): f x=rollF (fun j=>Z (x j)):=by
    change L ((List.ofFn (fun i=> ExteriorAlgebra.ι ℂ (x i))).prod)=_; rw [map_list_prod,List.map_ofFn]; refine congrArg (fun (a: Fin n→FC _) => rollF a) ?_; exact funext fun i=> ExteriorAlgebra.lift_ι_apply .. -- tune
 have hx(i:Fin n):Z (e i)=a i:=by unfold Z; change ∑ j:Fin n,_ =_; unfold e; simp [Pi.basisFun_apply] -- basis
 rw [show rollF (Reform a A)= f A from (hp A).symm, press V f A, hp e, funext hx] -- f target.A
private lemma churn (a:Fin n→V): List.ofFn (a ∘ Fin.revPerm)=(List.ofFn a).reverse:=by
 apply List.ext_getElem; · simp
 intro i h h'; rw [List.getElem_ofFn,List.getElem_reverse,List.getElem_ofFn]; unfold Function.comp; congr; apply Fin.ext; simp [Fin.rev]; omega -- tune
lemma Plush_furl (A:Op (Fin n))(t:Cross a a): furlF (Reform a A)=A.det • furlF a:=by
 unfold furlF; rw [←churn,←churn]; let e:= @Fin.revPerm n; let B:=A.submatrix e e; have hp: (Reform a A) ∘ e=Reform (a ∘ e) B:= by funext i; symm; exact Equiv.sum_comp e (fun j=> A (e i) j • a j)
 change rollF (Reform a A ∘ e)=_ • rollF _; rw [hp, Plush_roll (a ∘ (e: Fin n≃ Fin n)) B (fun i j=>t (e i) (e j)),show B.det=A.det from Matrix.det_submatrix_equiv_self e A] -- tune transparency
lemma Cross.flip (z:Cross a b) : Cross b a:=by intro i j; rw [antiB_comm]; exact z j i -- args
lemma Cross.act (A:Op (Fin n))(p:Cross a b): Cross (Reform a A) b:= by
 intro i j; unfold Reform; simp_rw [antiB_sum,antiB_smul,p _ _,smul_zero,sum_const_zero]
private lemma comma {Z:V}(p:∀ i,antiB Z (a i)=0)(h:∀ i,antiB Z (b i)=0): Z*Tile a b=Tile a b * Z:=by
 suffices he:Commute Z (Tile a b) from he; unfold Tile rollF; apply Commute.list_prod_right; intro A t; obtain ⟨i,rfl⟩:=List.mem_ofFn.mp t; change Z* (a i*b i)=(a i*b i)*Z
 rw [←mul_assoc,show Z*a i= -(a i*Z) from eq_neg_of_add_eq_zero_left (p i), neg_mul, mul_assoc,show Z*b i= -(b i*Z) from eq_neg_of_add_eq_zero_left (h i),mul_neg,neg_neg,mul_assoc]
lemma Sculpture (z:Cross b b)(p:Cross b a) : Tile a b= rollF a*furlF b:=by
 induction n with
 | zero=>simp [Tile,rollF,furlF]
 | succ n ih=>
    let A:= a ∘ Fin.succ; let B:= b ∘ Fin.succ; let u:=a 0; let v:=b 0
    change (List.ofFn (fun i=>a i*b i)).prod= (List.ofFn a).prod * (List.ofFn b).reverse.prod; simp only [List.ofFn_succ,List.prod_cons,List.reverse_cons,List.prod_append,List.prod_nil,mul_one]; change u*v* Tile A B=(u*rollF A)*(furlF B*v); rw [mul_assoc,comma A B (fun i=> p 0 i.succ) (fun i=> z 0 i.succ), ih A B (fun i j=> z i.succ j.succ) (fun i j=> p i.succ j.succ)]; simp only [mul_assoc]; rfl
lemma Museum (A B:Op (Fin n))(h:Cross a a)(g:Cross b b)(p:Cross a b): Tile (Reform a A) (Reform b B)= (A.det*B.det) • Tile a b:=by
 have hp(f g:Fin n→FC ι)(p:Cross f g)(A B:Op (Fin n)): Cross (Reform g B) (Reform f A):= Cross.act g (Reform f A) B (Cross.flip _ g (Cross.act f g A p))
 rw [Sculpture _ _ (hp b b g B B) (hp a b p A B),Sculpture _ _ g (Cross.flip a b p),Plush_roll a A h, Plush_furl b B g, Algebra.smul_mul_assoc,Algebra.mul_smul_comm, smul_smul]
#print axioms Museum
end YM.CF.Fock.Reduction.Plush
