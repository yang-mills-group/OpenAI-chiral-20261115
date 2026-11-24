import YM.SU5.FiniteGaugeData.Drachma.TauM
import Mathlib.Analysis.Matrix.Order
set_option autoImplicit false
set_option synthInstance.maxSize 18000
noncomputable section
namespace YM.SU5.FiniteGaugeData.Drachma
open Function Finset Matrix
open scoped Topology BigOperators InnerProductSpace Matrix Kronecker Classical MatrixOrder Matrix.Norms.L2Operator
variable {x y:Type}[Fintype x][DecidableEq x][Fintype y]
lemma recoil(A T : sp x)(h:A.PosDef)(p: T.PosSemidef) : A.det≤ (A+T).det:=by
 have he:= h.isUnit; obtain ⟨Y,hY⟩:= CStarAlgebra.nonneg_iff_eq_star_mul_self.mp p.nonneg
 let W:=A+star Y*Y; rw [hY] -- tune eq direction
 let Q:=1+ Y*A⁻¹*star Y
 have hh : (Y*A⁻¹*star Y).PosSemidef:=h.posSemidef.inv.mul_mul_conjTranspose_same Y
 have hx: Q.PosDef:= PosDef.one.add_posSemidef hh
 have hf : W.det=A.det*Q.det:=calc
    _ = (A*(1+A⁻¹*star Y*Y)).det:=by
          congr 1; rw [mul_add, mul_one, ←Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp he),one_mul]; -- tune
    _ = A.det*(1+A⁻¹*star Y*Y).det:= det_mul ..
    _ = A.det*Q.det:=by rw [det_one_add_mul_comm, ← Matrix.mul_assoc Y]
 let Z := hx.1
 have hy(i:x):1 ≤ Z.eigenvalues i:=by
    let J:= Z.eigenvectorUnitary.val; let v:= J.col i; have he: Q*ᵥ v= Z.eigenvalues i • v:= Z.mulVec_eigenvectorBasis i
    have hb: dotProduct v v=1:=by
       have hv:star J * J=1:= Unitary.coe_star_mul_self ..; have hw:=congr_fun (congr_fun hv i) i; simp only [Matrix.mul_apply,Matrix.one_apply_eq,star_eq_conjTranspose, Matrix.conjTranspose_apply,star_trivial] at hw; exact hw
    have hu : 0≤ (star v) ⬝ᵥ ((Q-1) *ᵥ v):=((by unfold Q; rw [add_sub_cancel_left]; exact hh) : (Q-1).PosSemidef).dotProduct_mulVec_nonneg v
    rw [star_trivial,sub_mulVec,he,one_mulVec,dotProduct_sub,dotProduct_smul,hb,smul_eq_mul,mul_one] at hu; exact sub_nonneg.mp hu
 change A.det ≤ W.det; rw [hf]; apply le_mul_of_one_le_right h.det_pos.le; rw [Z.det_eq_prod_eigenvalues]; exact one_le_prod fun i _=>hy i -- tune
lemma recoil_le(A T:sp x) (he:A.PosSemidef) (hT:A ≤ T):A.det≤ T.det:=by
 by_cases h:A.det=0; · rw [h]; exact (Matrix.nonneg_iff_posSemidef.mp (le_trans he.nonneg hT)).det_nonneg
 simpa using recoil A (T-A) (he.posDef_iff_det_ne_zero.mpr h) (Matrix.le_iff.mp hT)
omit [DecidableEq x] in
lemma rail{A T:sp x}(he:A.IsSymm)(hT:T.IsSymm)(hp:∀ i:coin x,dotProduct i (A*ᵥ i) ≤ dotProduct i (T*ᵥ i)): (T-A).PosSemidef:=by
 apply PosSemidef.of_dotProduct_mulVec_nonneg (Matrix.isHermitian_iff_isSymm.mpr (hT.sub he)); intro x; rw [star_trivial,sub_mulVec,dotProduct_sub]; exact sub_nonneg.mpr (hp x)
lemma prosper{A T:sp x}(he:A.PosSemidef)(hT:T.IsSymm)(hp:∀ i:coin x,dotProduct i (A*ᵥ i) ≤ dotProduct i (T*ᵥ i)): A.det ≤ T.det:= recoil_le _ _ he (Matrix.le_iff.mpr (rail (Matrix.isHermitian_iff_isSymm.mp he.1) hT hp))
end YM.SU5.FiniteGaugeData.Drachma
