import YM.CF.Thera.Lawn
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
Angular mark datum eq:B-MAG. Explicit spin-2 matrices in the fundamental (not separately
assigned to flavors). Fiber computed in SU(5). Use FiniteGaugeData Lie coordinates (`Color`).
-/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.CF.BProof.Mag
open Function Set Complex NormedSpace
open scoped Matrix Matrix.Norms.Frobenius BigOperators Topology ComplexOrder
abbrev GMat := Matrix (Fin 5) (Fin 5) ℂ
abbrev Lie := SU.group.Color

-- conventions X=-iJ for Jx=(J++J-)/2,Jy=(J+-J-)/2i,Jz=diag(2..-2)
private def t : ℂ := (Real.sqrt 6:ℝ)/2
def Jx : GMat := !![ 0,1,0,0,0; 1,0,t,0,0; 0,t,0,t,0; 0,0,t,0,1; 0,0,0,1,0]
def Ky : GMat := !![ 0,1,0,0,0; -1,0,t,0,0; 0,-t,0,t,0; 0,0,-t,0,1; 0,0,0,-1,0]
def diag : Fin 5 → ℂ := ![2,1,0,-1,-2]
def Jz : GMat := Matrix.diagonal diag
def x : GMat := (-I) • Jx
def y : GMat := -Ky
def z : GMat := (-I) • Jz

private lemma star_t : star t=t := by simp [t,star_def]
private lemma star_x : star x= -x := by
 have h : star Jx=Jx:=by
   ext i j : 1; fin_cases i <;> fin_cases j <;>
     simp [Matrix.star_eq_conjTranspose, t,Jx]
 rw [x,star_smul,h,star_neg,star_def,conj_I,neg_neg,neg_smul,neg_neg]
private lemma star_y : star y= -y:=by
 ext i j : 1; fin_cases i <;> fin_cases j <;>
   simp [y,Matrix.star_eq_conjTranspose,t,Ky]
private lemma star_z : star z= -z:=by
 ext i j : 1; fin_cases i <;> fin_cases j <;>
   norm_num [z,Jz,diag,Matrix.diagonal_apply,star_def]

private lemma tr_xy : Matrix.trace x=0 ∧ Matrix.trace y=0 ∧ Matrix.trace z=0 := by
 norm_num [Matrix.trace,x,Jx,z,Jz,y,Ky,diag,Fin.sum_univ_succ]

lemma lie_x : x∈SU.group.lie := Thera.league.mpr ⟨star_x,tr_xy.1⟩
lemma lie_y : y∈SU.group.lie := Thera.league.mpr ⟨star_y,tr_xy.2.1⟩
lemma lie_z : z∈SU.group.lie := Thera.league.mpr ⟨star_z,tr_xy.2.2⟩

private lemma t_ne : t ≠ 0 := by unfold t; norm_cast; positivity
private lemma t_sq : t*t=(6:ℂ)/4 := by simpa [t] using congrArg (fun x : ℝ => (x : ℂ)) (show (Real.sqrt 6 /2)*(Real.sqrt 6 /2)=(6:ℝ)/4 by nlinarith [Real.sq_sqrt (show (6:ℝ)≥0 by norm_num)])
set_option maxHeartbeats 1000000 in
lemma cyclic : x*y-y*x=z ∧ y*z-z*y=x ∧ z*x-x*z=y := by
 have hv := t_sq
 refine ⟨?_,?_,?_⟩ <;> (ext i j : 1; fin_cases i <;> fin_cases j <;>
   simp [x,y,z,Jx,Ky,Jz,diag,Matrix.mul_apply, Matrix.diagonal_apply,Matrix.vecMul_diagonal] <;> ring_nf <;> simp [pow_two,t_sq] <;> ring)


def X : Fin 3 → Lie := ![SU.group.projectColor x,SU.group.projectColor y,SU.group.projectColor z]
-- triple of commutator coordinates (01,02,12 in axes 0,1,2 in tangential coordinates)
def magnetic : Fin 3 → Lie := ![X 2, -(X 1), X 0]
lemma triple : magnetic = ![SU.group.ad (X 0) (X 1),SU.group.ad (X 0) (X 2),SU.group.ad (X 1) (X 2)] := by
 funext i; apply SU.group.colorMat_injective; fin_cases i <;>
 simp [X,magnetic,SU.group.colorMat_project_self lie_x,SU.group.colorMat_project_self lie_y,SU.group.colorMat_project_self lie_z]
 · exact cyclic.1.symm
 · nth_rw 1 [← cyclic.2.2]; exact neg_sub .. 
 exact cyclic.2.1.symm

set_option maxHeartbeats 600000 in
theorem commutant (u : GMat) (hx : u*x=x*u) (hz : u*z=z*u) : ∃ w : ℂ, u=w • (1:GMat) := by
 have cancel (v w : GMat) (h : (-I) • v=(-I) • w) : v=w := ((smul_right_injective _ (by simp : -I≠0)) h)
 have he := cancel _ _ (by simpa [x] using hx : (-I) • (u*Jx)=(-I) • (Jx*u)) -- tune
 have hp := cancel _ _ (by simpa [z] using hz : (-I) • (u*Jz)=(-I) • (Jz*u))
 have hd (i j : Fin 5) (h : i≠j) : u i j=0 := by
   have h0 := congrArg (fun q : GMat => q i j) hp
   simp only [Jz,Matrix.mul_diagonal,Matrix.diagonal_mul] at h0
   by_contra h1; have hi : diag i = diag j := mul_left_cancel₀ h1 (h0.trans (mul_comm ..)).symm
   fin_cases i <;> fin_cases j <;> (first|exact h rfl|norm_num [diag] at hi)
 have hp (i : Fin 4) : u i.castSucc i.castSucc=u i.succ i.succ := by
   have hm : u = Matrix.diagonal u.diag := Matrix.ext fun j k => by
     by_cases h : j=k <;> simp [Matrix.diagonal_apply,h,hd]
   have hu := he; rw [hm] at hu
   have h0:=congrArg (fun A : GMat => A i.castSucc i.succ) hu
   simp only [Matrix.mul_diagonal,Matrix.diagonal_mul, Matrix.diag_apply] at h0
   exact mul_right_cancel₀ (by fin_cases i <;> simp [Jx,t_ne] : Jx i.castSucc i.succ≠0) (h0.trans (mul_comm ..))
 have h(i:Fin 5) : u i i=u 0 0:= by
   have h0 : u 0 0 = u 1 1 := hp 0; have h1 : u 1 1 = u 2 2 := hp 1; have h2 : u 2 2 = u 3 3 := hp 2; have h3 : u 3 3 = u 4 4 := hp 3; fin_cases i
   · rfl
   · exact h0.symm
   · exact (h0.trans h1).symm
   · exact ((h0.trans h1).trans h2).symm
   · exact (((h0.trans h1).trans h2).trans h3).symm
 refine ⟨u 0 0,Matrix.ext fun i j => ?_⟩
 by_cases g:i=j
 · subst j; simpa using h i
 simp [hd i j g,Matrix.one_apply,g]
end YM.CF.BProof.Mag
