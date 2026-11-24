import Zephyr.Chern.Reach
import Zephyr.Chern.Fits
set_option autoImplicit false
noncomputable section
namespace Zephyr.Chern

open YM YM.Lattice Filter YM.CF


open scoped Kronecker

def lock (i:SU.Slot):ℂ:= -2 * wgt i
def cab:Op SU.Slot:=Matrix.diagonal lock
lemma cab_diag : (1:Op SpinIdx) ⊗ₖ cab=Matrix.diagonal (fun i=>lock i.2):=by
  ext ⟨x,v⟩ ⟨y,w⟩
  by_cases h:v=w <;> simp [cab,h, Matrix.one_apply, Matrix.diagonal_apply]

lemma gain_flux (y z:Cover): gain y z = -(flux y z:ℝ):=by
  rw [gain,gainR,bow,flux]; push_cast;ring
lemma phase_lock(y z:Cover)(i:SU.Slot):
    lock i * gain y z= wgt i * (2*flux y z:ℝ):=by
  rw [gain_flux,lock]
  push_cast;ring

variable {κ:Type*}{s:ℕ}{L:Filter κ} [L.NeBot] {X:Cross s L} {p:Stack}

lemma Cross.Relax.lump (h:X.Relax p)(k:Fin 3)
    {f:Cover→Cover→Op IS}(e:∀ y z i j, f y z i j=Cross.forge p y z i j k):Fits (p k) f:=by
  intro x i j
  apply (Equiv.subLeft x).hasSum_iff.mp
  change HasSum (fun z=>f (x-z) (x-(x-z)) i j) _
  simp_rw [sub_sub_cancel,e]
  exact h.hasSum ..

set_option maxHeartbeats 800000 in
theorem Cross.Relax.toGains (h:X.Relax p):
    Gains (p 0) (p 1) (p 2) ((1:Op SpinIdx) ⊗ₖ cab) := by
  rw [cab_diag]
  constructor
  · apply h.lump 0
    intro y z i j
    simp [Cross.forge,splice,tip,braidE,pulseJet,ringlet,Matrix.mul_apply]
  · apply h.lump 1
    intro y z i j
    rw [Matrix.add_apply,Matrix.add_apply, Matrix.diagonal_mul]
    simp [Cross.forge,splice,tip,braidE,pulseJet,ringlet,Matrix.mul_apply,Finset.mul_sum,←Finset.sum_add_distrib,
      lock,gain_flux]
    apply Finset.sum_congr rfl
    intro _ _; ring
  apply h.lump 2
  intro y z i j
  rw [Matrix.add_apply,Matrix.add_apply,Matrix.add_apply,Matrix.add_apply,Matrix.diagonal_mul,
    Matrix.smul_apply, Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul]
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Cross.forge,splice,tip,braidE,pulseJet,ringlet, Matrix.mul_apply,
    mul_add (lock _),Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro _ _
  simp [lock,gain_flux]
  ring
