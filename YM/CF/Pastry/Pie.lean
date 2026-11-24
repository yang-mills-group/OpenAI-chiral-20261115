import YM.CF.Pastry.Cape

/-! Eccentric pair polynomials evaluate on the same determinant sea. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pastry
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Function Fock Finset NormedSpace Petal Branch
attribute [local instance] opCStarAlgebra
variable {n : Type*} [LinearOrder n] [Fintype n]
abbrev LeanV (n : Type*) := Bool × n
private noncomputable abbrev alt (n : Type*) [d : DecidableEq n] (l : LinearOrder n) : LinearOrder n := { l with
  toDecidableEq := d
  compare_eq_compareOfLessAndEq := by
    haveI : LinearOrder n := l
    have h : d=l.toDecidableEq := Subsingleton.elim _ _
    rw [h]; exact l.compare_eq_compareOfLessAndEq }
instance : LinearOrder (LeanV n) := alt _ (LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective)
-- stitch / superseded
abbrev ribbon (n : Type*) [LinearOrder n] [Fintype n] := Dough (LeanV n)
def drawT (P : Op n) (i : LeanV n) := if i.1 then seekF P i.2 else hideF P i.2
lemma rind (P : Op n) (h : IsStarProjection P) (i j : LeanV n) : antiB (drawT P i) (drawT P j)=0 := by
  have he (i j:n): antiB (hideF P i) (seekF P j)=0 := by
    rw [hideF,seekF,prong_t,prong_p]; unfold antiB; rw [car]
    have ht : P*(1-P)=0 := Porth h
    have hu := act_inner P (basisKet i) (acts (1-P) (basisKet j)); rw [show star P=P from h.isSelfAdjoint,← act_mul,ht,act_zero,inner_zero_right] at hu; rw [hu,zero_smul]
  rcases i with ⟨u,i⟩; rcases j with ⟨v,j⟩; cases u <;> cases v
  · change antiB (hideF P i) (hideF P j)=0; simp only [hideF,prong,antiB_sum, antiB_sum',antiB_smul,antiB_smul',antiB,take_take,smul_zero,sum_const_zero]
  · exact he ..
  · change antiB (seekF P i) (hideF P j)=0; rw [antiB_comm, he]
  change antiB (seekF P i) (seekF P j)=0; rw [seekF,prong_p,prong_p]; exact car_create ..
def nursery (P : Op n) (h : IsStarProjection P) : Poly (LeanV n) n := ⟨drawT P,rind P h⟩
def thread (v : UNI n) (b : Bool) : UNI n := if b then v else ccU v
def closeV (v : UNI n) : UNI (LeanV n) := ⟨jump (Equiv.refl _) (fun b=>(thread v b).val), jump_unitary _ _ (fun b=>(thread v b).property)⟩
abbrev wire (u : Bool) (i : n) := put (n:=LeanV n) (u,i)
lemma thread_in (u : Bool) (v : UNI n) (i : n) : twist (quantU (n:=LeanV n) (closeV v)) (wire u i) = ∑ j:n,(thread v u).val j i • wire u j := by
  rw [wire,twist_p]; unfold prong; rw [Fintype.sum_prod_type,sum_eq_single u]; simp [closeV,jump_apply,wire]
  · intro j _ l; simp [closeV,jump_apply,l]
  simp
-- generalized dyads
abbrev twinD (f g : n→FC (LeanV n)) (A : Op n) := ∑ i, ∑ j, A i j • (f i*g j)
abbrev faceD (u v : Bool) (i : Op n) := twinD (n:=n) (wire u) (wire v) i
lemma face_fold (u v : Bool) (A : Op n) (U : UNI n) : twist (quantU (n:=LeanV n) (closeV U)) (faceD u v A)= faceD u v ((thread U u).val*A*(thread U v).valᵀ) := by
  simp only [faceD,twinD,map_sum,twist_scalar,map_mul,thread_in]
  simp_rw [sum_mul,mul_sum,Matrix.mul_apply,sum_mul,sum_smul,smul_sum,
    Algebra.mul_smul_comm,Algebra.smul_mul_assoc,smul_smul,Matrix.transpose_apply]
  let S := (thread U u).val; let T := (thread U v).val; let f := wire u (n:=n); let g := wire v (n:=n)
  let D (i j p q : n) := (A i j*(T q j*S p i)) • (f p*g q)
  change ∑ i,∑ j,∑ p,∑ q, D i j p q=_
  simp_rw [sum_comm (f:=fun i j=>∑ p,∑ q,D i j p q), sum_comm (f:=fun i p=>∑ q,D i _ p q),
    sum_comm (f:=fun j p=>∑ i,∑ q,D i j p q), sum_comm (f:=fun i q=>D i _ _ q), sum_comm (f:=fun j q=>∑ i,D i j _ q)]
  simp only [D,mul_comm,mul_assoc,mul_left_comm,S,T,f,g] -- tune
lemma face_flour (u v : Bool) (A : Op n) : Flour univ (faceD u v A) := Flour.sum _ (fun _ _=> Flour.sum _ (fun _ _=> (Flour.putPut univ (mem_univ _) (mem_univ _)).smul _))
lemma eval_faceD (u v : Bool) (V : Poly (LeanV n) n) (A : Op n) : V.eval (faceD u v A)=dyad A (fun i=>V.term (u,i)) (fun i=>V.term (v,i)) := by
  unfold faceD twinD dyad; simp_rw [map_sum,map_smul, wire,V.eval_double]
def quilt (D A B : Op n) := (2:ℂ)⁻¹ • (faceD false false D+faceD false true A-faceD true false Aᵀ+faceD true true B)
def hang (D A B : Op n) : ribbon n := ⟨quilt D A B,by
  apply Flour.smul; rw [sub_eq_add_neg]; apply Flour.add; swap; exact face_flour ..
  apply Flour.add (Flour.add (face_flour ..) (face_flour ..)); simpa using (face_flour true false Aᵀ).smul (-1)⟩
lemma mast_free (u v : Bool) (A : Op n) : mast (faceD u v A)=0 := by simp_rw [mast,faceD,twinD, crumb_sum, crumb_scale]; apply sum_eq_zero; intro i _; apply sum_eq_zero; intro k _; rw [show crumb _ ∅=0 from mast_row _ _,mul_zero]
lemma Quilt.mast (D A B : Op n) : pane (hang D A B)=0 := by
  change crumb (quilt D A B) ∅=0; have he (x y:FC (LeanV n)) : crumb (x-y) ∅=crumb x ∅-crumb y ∅ := rfl
  rw [quilt,crumb_scale,crumb_add,he,crumb_add]
  have ht (u v) (A : Op n) : crumb (faceD u v A) ∅=0 := mast_free ..
  rw [ht,ht,ht,ht]; ring
lemma stitchP (P : Op n) (h : IsStarProjection P) (D A B : Op n) : (nursery P h).cook (hang D A B)=inning (hideF P) (seekF P) D A B := by
  change (nursery P h).eval (quilt D A B)=_; simp_rw [quilt,map_smul,map_add,map_sub,map_add,eval_faceD]; rfl
lemma Uniform.run (U : UNI n) (D A B : Op n) : fold (n:=LeanV n) (closeV U) (hang D A B)=hang (Tour.Kcc U.val D) (Tour.Kcg U.val A) (Tour.Kgg U.val B) := by
  apply Subtype.ext; change twist _ (quilt D A B)=quilt _ _ _; simp_rw [quilt,twist_scalar,map_add,map_sub,map_add,face_fold]; simp only [Tour.Kcg, Tour.Kcc,Tour.Kgg,Matrix.transpose_mul,Matrix.transpose_transpose,mul_assoc, thread]; rfl -- tune
lemma sum_quilt {I : Type*} (p : Finset I) (D A B : I→Op n) : ∑ i∈p, hang (D i) (A i) (B i)=hang (∑ i∈p,D i) (∑ i∈p,A i) (∑ i∈p,B i) := by
  classical
  have hx (u v : Bool) (F : I→Op n) : ∑ i∈p, faceD u v (F i)=faceD u v (∑ i∈p,F i) := by
    unfold faceD twinD; simp_rw [Matrix.sum_apply,sum_smul]; rw [sum_comm]; apply sum_congr rfl; intro i _; rw [sum_comm]
  apply Subtype.ext; change (Dough (LeanV n)).val _=quilt _ _ _; rw [map_sum]; change ∑ i∈p, quilt _ _ _=quilt _ _ _; simp_rw [quilt]; rw [←smul_sum,sum_add_distrib,sum_sub_distrib,sum_add_distrib,hx,hx,hx,hx,Matrix.transpose_sum] -- tune locus
lemma fold_hollow (x : ℂ) (U : UNI (LeanV n)) : Pastry.fold (n:=LeanV n) U (hollow x)= hollow x := by
  apply Subtype.ext; change twist (quantU U) (x • (1:FC (LeanV n)))=x • 1; rw [twist_scalar,map_one]
end YM.CF.Pastry
