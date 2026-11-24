import YM.CF.BProof.Magnetic

/-! Fiber of the face rule. Use these center labels separately on the two faces of every N strip. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mag
open SU Complex Function
open scoped Matrix Topology Matrix.Norms.Frobenius
local notation "π" => Real.pi
local notation "M" => SU.group.mat

def eta : ℂ := Complex.exp (2 * π * I / (↑(5:ℕ):ℂ))
theorem eta_root : IsPrimitiveRoot eta 5 := Complex.isPrimitiveRoot_exp _ (by decide)
lemma phase_five (i : Fin 5) : (eta^i.val)^5=1 := by rw [←pow_mul,Nat.mul_comm,pow_mul,eta_root.pow_eq_one,one_pow]
lemma norm_five (w : ℂ) (h : w^5=1) : ‖w‖=1 := by
 apply pow_left_inj₀ (norm_nonneg w) zero_le_one (by decide : 5 ≠ 0) |>.1
 rw [← norm_pow,h,norm_one,one_pow]

def mkCenter (w : ℂ) (h : w^5=1) : E := by
 let T : GMat:=w • 1
 have ht : T ∈ unitary GMat := Matrix.mem_unitaryGroup_iff.mpr (by
   have hw := norm_five w h
   unfold T; rw [star_smul,star_one,Algebra.mul_smul_comm,Algebra.smul_mul_assoc,mul_one,smul_smul,mul_comm,Complex.star_def,Complex.mul_conj,normSq_eq_norm_sq,hw,one_pow,Complex.ofReal_one,one_smul])
 have he : T.det=1 := by simp [T,h]
 exact ⟨⟨T,ht⟩,he⟩

def center (i : Fin 5) := mkCenter _ (phase_five i)
@[simp] lemma mat_center (i : Fin 5) : M (center i)= eta^i.val • (1:SU.group.Mat) := rfl
@[simp] lemma center_zero : center 0=1 := by apply SU.group.mat_injective; rw [mat_center]; simp
lemma center_inj : Injective center := by
 intro i j h; apply Fin.ext; apply eta_root.pow_inj i.isLt j.isLt; simpa [mat_center] using congrArg (fun z=> M z 0 0) h
lemma center_comm (i : Fin 5) (u : E) : center i * u=u*center i := by apply SU.group.mat_injective; simp

lemma adjoint_center (u : E) : (∀ i, SU.group.adjoint u (magnetic i)=magnetic i) ↔ ∃ i, u=center i := by
 constructor
 · intro h
   have he(i) := congrArg SU.group.colorMat (h i); simp only [Gauge.mat_adjoint,Gauge.conjugate] at he
   have hh(i) : M u * SU.group.colorMat (magnetic i) = SU.group.colorMat (magnetic i)* M u := by
     nth_rw 2 [← he i]; rw [mul_assoc, Gauge.mat_star_mul,mul_one]
   obtain ⟨w,hw⟩:=commutant (M u) (by have h := hh 2; simp [magnetic,X,SU.group.colorMat_project_self lie_x] at h; exact h) (by have h := hh 0; simp [magnetic,X,SU.group.colorMat_project_self lie_z] at h; exact h)
   have hz : Matrix.det (M u)=1:=fund_det u
   change SU.group.mat u = w • (1:SU.group.Mat) at hw
   rw [hw,Matrix.det_smul] at hz; rw [Matrix.det_one,mul_one,Fintype.card_fin] at hz; change w^5=1 at hz
   obtain ⟨i,hi,h⟩:=eta_root.eq_pow_of_pow_eq_one hz
   refine ⟨⟨i,hi⟩, SU.group.mat_injective ?_⟩; rw [hw,mat_center]; exact congrArg (fun w : ℂ => w • (1:SU.group.Mat)) h.symm
 rintro ⟨i,rfl⟩ j
 apply SU.group.colorMat_injective
 rw [Gauge.mat_adjoint,Gauge.conjugate]
 let x := center i; let A:=SU.group.colorMat (magnetic j)
 rw [show M x*A=A*M x by simp [x],mul_assoc,Gauge.mat_mul_star,mul_one] -- tune abbrev
end YM.CF.BProof.Mag
