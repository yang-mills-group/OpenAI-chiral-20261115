import YM.CF.Thera.Lawn
import YM.CF.Matter.Mass
/-! B-gate eq:B-MAG spin-2 magnetic choice.
Construct the background triple of Lie parameters once before any choices (not a fitted
   frame of a random gauge realization). And identify the stabilizer exactly. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress
namespace Mag
open SU Function Finset Matrix Complex
open scoped Topology Matrix Matrix.Norms.Frobenius BigOperators
private def r : ℂ := ↑(Real.sqrt 6/2)
private lemma r_sq : r^2=3/2:= by unfold r; norm_cast; rw [div_pow,Real.sq_sqrt (by norm_num)]; norm_num
private lemma star_r : star r=r:=conj_ofReal _
private lemma r_ne : r≠0:=by unfold r; exact_mod_cast (show (Real.sqrt 6/2:ℝ)≠0 by positivity)
-- -iL_z; -iL_x; -iL_y
private def zeta (i : Fin 5) : ℂ := -I*(2-↑(i.val))
def X := diagonal zeta
def Y : Op (Fin 5) := !![0,-I,0,0,0; -I,0,-I*r,0,0; 0,-I*r,0,-I*r,0; 0,0,-I*r,0,-I; 0,0,0,-I,0]
def Z : Op (Fin 5) := !![0,-1,0,0,0; 1,0,-r,0,0; 0,r,0,-r,0; 0,0,r,0,-1; 0,0,0,1,0]
private lemma starX : star X= -X:=by ext i j : 1; by_cases p:i=j <;> simp [X,zeta, p, Ne.symm]
private lemma trX : trace X=0:=by rw [X,trace_diagonal]; simp [zeta,Fin.sum_univ_succ]; ring
private lemma starY : star Y= -Y:=by ext i j : 1; fin_cases i <;> fin_cases j <;> simp [Y,star_r,show star I= -I from conj_I]
private lemma trY : trace Y=0:=by simp [Y,Matrix.trace,Fin.sum_univ_succ]
lemma xy : X*Y-Y*X=Z:=by
  ext i j : 1; rw [Matrix.sub_apply,X, diagonal_mul,mul_diagonal]; fin_cases i <;> fin_cases j <;> norm_num [zeta,Y,Z,Fin.val_last] <;> ring_nf <;> norm_num [sq]
lemma zx : Z*X-X*Z=Y := by ext i j : 1; rw [Matrix.sub_apply,X,mul_diagonal,diagonal_mul]; fin_cases i <;> fin_cases j <;> norm_num [zeta,Y,Z,r_ne] <;> ring
lemma yz : Y*Z-Z*Y=X := by
  ext i j : 1; fin_cases i <;> fin_cases j <;> norm_num [Y,Z,X,zeta,mul_apply,Fin.sum_univ_succ,Fin.val_last] <;> ring_nf <;> rw [r_sq] <;> ring
lemma lieX : X∈group.lie:= Thera.league.mpr ⟨starX,trX⟩
lemma lieY : Y∈group.lie:= Thera.league.mpr ⟨starY,trY⟩
lemma lieZ : Z∈group.lie:= xy ▸ group.bracket_mem lieX lieY
lemma commutant (A : Op (Fin 5)) (p : X*A=A*X) (h : Y*A=A*Y) : A=A 0 0 • 1 := by
  have hx : Injective zeta:= by
    intro i j e; unfold zeta at e; have hh:= sub_right_inj.mp (mul_left_cancel₀ (neg_ne_zero.mpr I_ne_zero) e); exact Fin.ext (Nat.cast_injective (R:=ℂ) hh)
  have off (i j : Fin 5) (e : i≠j) : A i j=0:=by
    have he := Matrix.ext_iff.mpr p i j; rw [X, diagonal_mul,mul_diagonal,mul_comm (A i j)] at he
    exact (mul_eq_zero.mp ((sub_mul ..).trans (sub_eq_zero_of_eq he))).resolve_left (sub_ne_zero.mpr (hx.ne e))
  let f := fun i=> A i i; have he: A=diagonal f:=by ext i j : 1; by_cases h:i=j <;> simp [f,h,off]
  have across (i : Fin 4) : f i.castSucc=f i.succ:=by
    rw [he] at h; have t:=Matrix.ext_iff.mpr h i.castSucc i.succ; rw [diagonal_mul,mul_diagonal,mul_comm (f i.castSucc)] at t; have hu:Y i.castSucc i.succ≠0:=by fin_cases i <;> simp [Y,r_ne]
    exact (mul_left_cancel₀ hu t).symm
  nth_rw 1 [he]; ext i j : 1; by_cases p:i=j
  · subst j; simp only [diagonal_apply_eq, Matrix.smul_apply,smul_eq_mul,one_apply_eq, mul_one]; change f i=f 0
    induction i using Fin.induction with | zero=> rfl| succ i ih=> exact (across i).symm.trans ih
  simp [p]
lemma trace_commutant {A : Op (Fin 5)} (p : X*A=A*X) (h : Y*A=A*Y) (ht : trace A=0) : A=0:= by
  rw [commutant A p h] at ht; simp at ht; rw [commutant A p h,ht,zero_smul]

def center (i : Fin 5) := SU.central ^ (i:ℕ)
private lemma powers (i : ℕ) : group.mat (SU.central^i)=z^i • (1:group.Mat) := by
  have h:group.mat SU.central=z • (1:group.Mat):=by
    change diagonal (fun _:F=>z)=z • (1:Op F); ext i j : 1; by_cases p:i=j <;> simp [p]
  induction i with|zero=> simp|succ i ih=> rw [pow_succ,group.mat_mul,ih,h,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,mul_one,smul_smul,pow_succ]
lemma mat_center (i : Fin 5) : group.mat (center i)=z^(i:ℕ) • (1:group.Mat):= powers _
lemma center_injective : Injective center:=by
  intro i j h; have he:=congrArg (fun x=>group.mat x 0 0) h; change group.mat (center i) 0 0= group.mat (center j) 0 0 at he; rw [mat_center,mat_center] at he; exact Fin.ext (z_prim.pow_inj i.isLt j.isLt (by simpa using he))
@[simp] lemma center_zero : center 0=1:=by simp [center]
lemma center_comm (i : Fin 5) (A : E) : center i*A=A* center i:= group.mat_injective (by rw [group.mat_mul,group.mat_mul,mat_center,Algebra.smul_mul_assoc,Algebra.mul_smul_comm, mul_one,one_mul])
lemma center_cases {A : E} (c : ℂ) (t : group.mat A=c • 1) : ∃ i, A=center i:=by
  have he: (group.mat A).det=1:= fund_det _; rw [t,det_smul,det_one] at he
  obtain ⟨i,p,h⟩:= z_prim.eq_pow_of_pow_eq_one (ξ:=c) (show c^5=1 from by rw [Fintype.card_fin,mul_one] at he; exact he); refine ⟨⟨i,p⟩,group.mat_injective ?_⟩; rw [mat_center,t,h] -- tune
lemma center_test (A : E) : ( X * fund A=fund A * X ∧ Y*fund A=fund A * Y ) ↔ ∃ i, A=center i:= by
  constructor
  · rintro ⟨p,h⟩; exact center_cases _ (commutant _ p h)
  rintro ⟨i,rfl⟩; rw [show fund (center i)=z^(i:ℕ) • (1:Op F) from mat_center i]; simp

-- matrices & Lie coordinates. Plane triple in tangential order e<e'.
def generator : Fin 3 → group.Color := ![group.projectColor X,group.projectColor Y,group.projectColor Z]
@[simp] lemma generator_eq (i : Fin 3) : group.colorMat (generator i)=![X,Y,Z] i := by fin_cases i<;> first | exact group.colorMat_project_self lieX | exact group.colorMat_project_self lieY | exact group.colorMat_project_self lieZ
end Mag
end YM.CF.BPress
