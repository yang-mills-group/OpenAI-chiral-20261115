import YM.CF.BProof.Single.Tile
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Compress *either* chirality of free symbol, uniform positive charge over Mate. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Fig
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Spin Stint
open Fir Laurent Rush Bloch Next.Free BZ
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {s N:Side}{j:ℕ}
abbrev spHalf (t: Bool) := if t then plusHalf else plusHalfᶜ
abbrev pill (t:Bool):Op SpinIdx := cutM (spHalf t)
@[simp] lemma pill_plus : pill true=Aop:= raising.trans Adef.symm
@[simp] lemma pill_minus : pill false=1-Aop:=by rw [←pill_plus]; exact dim_cut plusHalf -- tune
lemma base_zone {p:Momentum}(h:p∈baseCube): p∈realCube zone:= base_subset_realCube zone_pos h
lemma lowFull (M:Male)(p:Jill.Bin)(h:tmap p∈baseCube)(t:Bool) : let Q:=bar j M.val (tmap p); pill t*(if t then Q else 1-Q)*pill t= Jill.disk j M p • pill t := by
 intro Q; let y:=tmap p; let d:=shell j M.val y; have hp:d=(Jill.disk j M p:ℂ) := Jill.express j p M.val (base_zone h) M.property
 let F:= Fir.zen (mixL j M.val y)
 have he: (1-Aop)*Aop=0:=by rw [sub_mul,one_mul,AOne,sub_self]
 have hk := bar_side (N:=M.val) j (base_zone h)
 cases t
 · change pill false*(1-_)*_= _; rw [pill_minus,←Complex.coe_smul,←hp]; change (1-Aop)*(1-Q)*(1-Aop)=d • (1-Aop); rw [show (1-Aop)*(1-Q)=d • ((1-Aop)*(1+F)) from hk.2,Algebra.smul_mul_assoc]; congr 1; rw [mul_add,mul_one,add_mul,show (1-Aop)*(1-Aop)=1-Aop from by rw [mul_sub,mul_one,he,sub_zero],show (1-Aop)*F=F*Aop from zenAA _, mul_assoc,show Aop*(1-Aop)=0 from by rw [mul_sub,mul_one,AOne,sub_self],mul_zero,add_zero]
 change pill true * Q * _ = _; rw [pill_plus,← Complex.coe_smul,←hp]; rw [show Aop*Q=d • (Aop * (1+F)) from hk.1,Algebra.smul_mul_assoc]; congr 1; rw [mul_add,mul_one,add_mul,AOne,show Aop*F=F*(1-Aop) from zenA _,mul_assoc,he,mul_zero,add_zero]
lemma ads (k: Site N) (i:Axis): ‖phase (pm k i)-1‖≤‖pm k‖:=by unfold phase; rw [mul_comm]; exact Real.norm_exp_I_mul_ofReal_sub_one_le.trans (norm_le_pi_norm ..)
lemma feed (h:1≤j): ∃ c C:ℝ, 0<c∧0<C∧∀ {N:Side}(k:Site N) (M:Male), (∀ i:Axis,c * ‖phase (pm k i)-1‖^2 ≤ Jill.disk j M (pm k)) ∧ Jill.disk j M (pm k) ≤ C * ‖pm k‖^2 ∧ c*‖pm k‖^2 ≤ Jill.disk j M (pm k):=by
 obtain ⟨c,C,h,hc,Q⟩:= Jill.zip h; refine ⟨c,C,h,hc,?_⟩; intro N k M; have ht:= Q M (pm k) ((pi_norm_le_iff_of_nonneg Real.pi_pos.le).2 (fun i=> abs_le.mpr ⟨(pm_zone k i).1.le,(pm_zone k i).2⟩)); exact ⟨fun i=>le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (ads k i) _) h.le) ht.1,ht.2,ht.1⟩
end YM.CF.BProof.Fig
