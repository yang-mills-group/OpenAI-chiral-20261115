import GaugeFieldConstruction.Juples
import YM.Work.A13

/-!
# Local translation/rotation arguments and Oriented convention (real).
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Stage
open Matrix Function Set Filter
open Flux One
open YM.Work.A13 (hasDerivAt_move plane_givens oneParameter_zero)
open scoped Matrix Matrix.Norms.Frobenius BigOperators Topology ContDiff

abbrev Rotors := Ortho.Skew

lemma northR (u : Rotors) (i j : Axis) : HasDerivAt (fun t : ℝ=> (Ortho.oneParameter u t).val i j) (u.val i j) 0 := by
  have hp := YM.Work.A13.hasDerivAt_coord u (basis j) i 0
  rw [oneParameter_zero, Ortho.move_one] at hp; simpa only [ Ortho.move,M4.move_basis] using hp

-- skew operations

def tick (a b : Rotors) : Rotors:=⟨a.val * b.val-b.val*a.val, by
    change star (a.val * b.val-b.val * a.val) = -_
    simp only [star_sub, star_mul,show star a.val= -a.val from a.property,show star b.val= -b.val from b.property] -- adjust
    simp⟩

def dir (a : E4) : Dollars:= fun i _=> a i
lemma dirC (a : E4) (x : E4) : Cadre (dir a) x where
  health i:= contDiff_const
  skew i j x:= by unfold dir; simp [YM.Maxwell.grad, YM.Analysis.D, dir]
  scale:= ⟨1,Or.inl rfl,by intro i j; simp [dir]⟩
lemma dirT (a : E4): Toll (dir a) (0:Rotors).val:= by intro i j x; unfold dir; simp [YM.Maxwell.grad,YM.Analysis.D, dir]

def soar (Ω : Rotors) (x : E4) : Dollars := fun b z=> M4.move Ω.val (z-x) b
abbrev ell (A:M4) (b:Axis) : E4→L[ℝ]ℝ := (EuclideanSpace.proj b:E4→L[ℝ]ℝ).comp (Matrix.toEuclideanLin A).toContinuousLinearMap
lemma soarT (Ω x): Toll (soar Ω x) Ω.val := by
  intro i j z; change YM.Analysis.D (basis i) (ell Ω.val j ∘ fun y=>y-x) z =_
  have ht: HasFDerivAt ((·-x) : E4→E4) (ContinuousLinearMap.id ℝ E4) z:=(hasFDerivAt_id z).sub_const _
  rw [YM.Analysis.D, fderiv_comp z (ell Ω.val j).differentiableAt ht.differentiableAt,ht.fderiv,(ell Ω.val j).fderiv]; exact M4.move_basis ..
lemma soarC (Ω x): Cadre (soar Ω x) x where
  health i:=(ell Ω.val i).contDiff.comp (contDiff_id.sub contDiff_const)
  skew a b z := by rw [soarT Ω x a b z,soarT Ω x b a z]; exact skewP ..
  scale:=⟨2,Or.inr rfl,fun i z=> by
    unfold soar reach; rw [add_sub_cancel_left]; exact (ell Ω.val i).map_smul _ _⟩
lemma still (Ω x k):soar Ω x k x=0 := by unfold soar; rw [sub_self]; exact map_zero (ell Ω.val k)

lemma parameter_add (u : Rotors) (a b : ℝ) : Ortho.oneParameter u (a+b)= Ortho.oneParameter u a * Ortho.oneParameter u b := by
  apply Subtype.ext; change NormedSpace.exp _=NormedSpace.exp _*NormedSpace.exp _
  haveI : NormedAlgebra ℚ M4 := .restrictScalars ℚ ℝ _
  rw [add_smul]; apply NormedSpace.exp_add_of_commute; -- local instance rational
  exact ((Commute.refl u.val).smul_right b).smul_left a

@[simp] lemma param_inv (u : Rotors) (t : ℝ) : (Ortho.oneParameter u t)⁻¹=Ortho.oneParameter u (-t) := by
  have E : Ortho.oneParameter u t * Ortho.oneParameter u (-t)=1 := by rw [← parameter_add]; simp [oneParameter_zero]
  exact inv_eq_of_mul_eq_one_right E

-- Rotation group here only proper taught by generated exponential subgroup. Identify det.
def orbit : Subgroup Ortho := Subgroup.closure {x| ∃ B t, x=Ortho.oneParameter B t}
lemma paid (u : Rotors) (t) : Ortho.oneParameter u t∈ orbit := Subgroup.subset_closure ⟨u,t,rfl⟩

-- parity of Signed determinant. comparison using SignBit
lemma parity (s : Signed): s.ortho.val.det=pay (signBit s) (1:ℝ) := by
  -- split motions
  have h (s r : Signed) : (s*r).ortho=s.ortho*r.ortho := Signed.inclusionO.map_mul s r
  have hm (s r : Signed) (u:s.ortho.val.det=pay (signBit s) (1:ℝ)) (v:r.ortho.val.det=pay (signBit r) (1:ℝ)) : (s*r).ortho.val.det=pay (signBit (s*r)) (1:ℝ) := by
    rw [h]; change (s.ortho.val*r.ortho.val).det=_; rw [det_mul,u,v,signBit_mul]; cases signBit s <;> cases signBit r <;> simp
  have hp : (1:Signed).ortho.val.det=pay (signBit 1) (1:ℝ) := by rw [show Signed.ortho 1=1 from Signed.inclusionO.map_one]; simp
  apply signed_induction (P:=fun s=>s.ortho.val.det=pay (signBit s) (1:ℝ)) _ _ hm
  · intro p; induction p using Equiv.Perm.swap_induction_on with
    | one=> exact hp -- defeq
    | swap_mul g i j v ih=>
      rw [unsigned_mul]; apply hm _ _ _ ih
      rw [signBit_swap i j v]
      change Matrix.det (Signed.matrix _)=-1
      rw [show Signed.matrix (unsigned (Equiv.swap i j))=(1:M4).submatrix (Equiv.swap i j) id by
        ext x y; by_cases h : (Equiv.swap i j) y=x <;> have ht : y=(Equiv.swap i j) x ↔ (Equiv.swap i j) y=x:=Equiv.swap_apply_eq_iff.symm <;> have hg : (Equiv.swap i j) x=y ↔ y=(Equiv.swap i j) x := eq_comm <;> simp [Signed.matrix_at, unsigned,h, Matrix.one_apply, ht, hg]]
      simp [Matrix.det_permute,v]
  intro i; rw [signBit_mirror]; change Matrix.det (Signed.matrix _) = -1
  rw [show Signed.matrix (Signed.mirror i)=Matrix.diagonal (fun a=>if a=i then (-1:ℝ) else 1) by ext j k; by_cases p:j=k <;> simp [p,Signed.matrix_at, Signed.mirror,Matrix.diagonal_apply,eq_comm]]
  rw [Matrix.det_diagonal]; simp
end YM.GaugeFieldConstruction.Stage
