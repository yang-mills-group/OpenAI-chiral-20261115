import Zephyr.Chern.Beat
import Zephyr.Chern.Shade
set_option autoImplicit false
noncomputable section
namespace Zephyr.Chern

open YM YM.Lattice YM.CF Matrix Silk


open scoped Kronecker

variable {I:Type*} [Fintype I] [DecidableEq I]
private def st (t:Brill) (u:Streams) (a:Axis) := slide t (dropD a u)

lemma flash_first (t:Brill) (z:Op I) (u:Streams) :
    let v:=fun a=>slide t (dropD a u)
    flash t (firstTwist (snow I u) (icolor z))=
      ((2:ℂ)⁻¹*2⁻¹) • ((leavesC (v 0) (v 1)+leavesC (v 2) (v 3)) ⊗ₖ z) := by
  have sub (a b:Op SpinIdx) (y:Op I) : (a-b)⊗ₖy=a⊗ₖy-b⊗ₖy := by
    ext ⟨e,i⟩ ⟨f,j⟩; exact sub_mul .. -- theorem signature?
  dsimp only [firstTwist,crossB,bow,leavesC]
  simp only [map_mul,map_add,map_sub,Δsnow,map_smul,shadeF,colorF,
    add_kronecker,sub,
    mul_add,mul_sub,Matrix.smul_mul,Matrix.mul_smul,smul_smul,
    ←mul_kronecker_mul,one_mul,mul_one,smul_add,smul_sub]

lemma tr5_here (t:Brill) (u:Streams) :
    tr5 (slide t u) (st t u 0) (st t u 1) (st t u 2) (st t u 3)=
      -4* E t (jac u) := by
  rw [jac,AlgHom.map_det]
  exact volume ((E t).mapMatrix (frameM u))

theorem frozen_trace (z: Op I)(u:Streams) :
    (mirror (snow I u)*
      (firstTwist (snow I u) (icolor z)*firstTwist (snow I u) (icolor z))).trace =
        ((2:ℂ) * (z*z).trace) • jac u := by
  apply E_ext; intro t
  rw [flash_trace,frozen,map_mul,map_mul,map_neg,shadeF,flash_first, map_smul, smul_eq_mul]
  rw [Matrix.mul_smul,Matrix.smul_mul,neg_mul,Matrix.mul_smul,Matrix.mul_smul,trace_neg,trace_smul,trace_smul,
    ←mul_kronecker_mul,←mul_kronecker_mul,one_mul,
    trace_kronecker,beats]
  have h:=tr5_here t u
  unfold st at h
  rw [h,smul_eq_mul,smul_eq_mul];ring

/-- trace of the origin coefficient of the second jet. Includes trace on
color; `z` is the twist tensor's color factor. NB jets are ordinary Taylor
coefficients, not derivatives. -/
theorem Jet.receipt {u:Streams}{r s} {z:Op I}
    (h:Jet (snow I u) r s (icolor z)) :
    (seam 0 s).trace=(-6) * (z*z).trace * τ (jac u) := by
  rw [←gross_co,h.response (fun _=>icolor_constant ..) (Δ_mingle _ _),
    gross_curly,gross_def,frozen_trace,map_smul,smul_eq_mul]
  ring
