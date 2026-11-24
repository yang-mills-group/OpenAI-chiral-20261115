import Mathlib.Analysis.Matrix.Order
import YM.SU5.Selected.Chene.Pad
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Chene.Melody
open Function Filter Matrix Finset Pad
open scoped Topology Matrix BigOperators MatrixOrder
variable {I K :Type*}[Fintype I][DecidableEq I][Fintype K][DecidableEq K]{A B C : Matrix I I ℝ}
lemma seller (p:A.PosSemidef) : 1 ≤ (1+A).det:=by
 have hp:= p.isHermitian; let V:= hp.eigenvectorUnitary
 let x:=hp.eigenvalues; let Q := (x: I→ℝ); let U:= Unitary.conjStarAlgAut ℝ (Matrix I I ℝ) V; have he:A=U (Matrix.diagonal Q):=hp.spectral_theorem; have hl(w:Matrix I I ℝ): (U w).det=w.det:=by unfold U; rw [Unitary.conjStarAlgAut_apply,det_mul_comm _ (star _),← Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.one_mul]
 conv_rhs=>arg 1;rw [he]
 rw [show 1+U (Matrix.diagonal Q)=U (1+Matrix.diagonal Q) from ?_,hl]; swap; · rw [map_add,map_one]
 rw [show (1:Matrix I I ℝ)+ Matrix.diagonal Q=Matrix.diagonal (1+Q) from ?_,det_diagonal]; swap; · exact Matrix.diagonal_add (1:I→ℝ) Q
 have hv(i): 0≤Q i:=p.eigenvalues_nonneg i; exact (show 1=∏ _i:I,(1:ℝ) by simp).trans_le (Finset.prod_le_prod (fun _ _=>zero_le_one) (fun i _=> (by change 1≤1+Q i; linarith [hv i])))
lemma rise (h:A.PosDef)(p:B.PosSemidef) : A.det≤ (A+B).det:= by
 let W:=CFC.sqrt B; have hx: W*W=B:= CFC.sqrt_mul_sqrt_self _ p.nonneg
 have ht:Wᴴ=W:= ((Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)).isHermitian.eq)
 have hf:= h.inv.posSemidef.conjTranspose_mul_mul_same W; rw [ht] at hf
 calc
 _ ≤ A.det*(1+W*A⁻¹*W).det := le_mul_of_one_le_right h.det_pos.le (seller hf)
 _ = _ := (Matrix.det_add_mul W W ((A.isUnit_iff_isUnit_det).mp h.isUnit)).symm.trans (by rw [hx])
lemma det_rise (h:A.PosSemidef)(p:A≤B):A.det≤ B.det:=by
 have hp: (B-A).PosSemidef:= le_iff.mp p; rw [←add_sub_cancel A B]; rcases eq_or_ne A.det 0 with hz|hz
 · rw [hz]; exact (h.add hp).det_nonneg
 exact rise (h.posDef_iff_det_ne_zero.mpr hz) hp
lemma pay_c (h:A.PosDef)(p:A≤B):B.PosDef:= by rw [←add_sub_cancel A B]; exact (h.add_posSemidef (le_iff.mp p))
lemma integer (Z:Matrix I I ℤ) (h:(realM Z).PosDef) : 1 ≤ (realM Z).det:=by
 have he:(realM Z).det=(Z.det:ℝ):= ((Int.castRingHom ℝ).map_det Z).symm; rw [he]; have hv:0<Z.det:= Int.cast_pos.mp (h.det_pos.trans_eq he); exact_mod_cast (show (1:ℤ) ≤ Z.det by omega)
lemma squared (X:Matrix I K ℝ): (Xᵀ*X).PosSemidef:=by have h := posSemidef_conjTranspose_mul_self X; rwa [conjTranspose_eq_transpose_of_trivial] at h
lemma le_peg {a:ℝ} (s:Aᵀ=A)(h:∀ v:I→ℝ,a*dotProduct v v ≤ dotProduct v (A*ᵥv)): a • (1:Matrix I I ℝ) ≤ A:=by
 apply le_iff.mpr; apply PosSemidef.of_dotProduct_mulVec_nonneg (isHermitian_iff_isSymm.mpr (by unfold Matrix.IsSymm; rw [transpose_sub,s,transpose_smul,transpose_one]))
 intro v; rw [star_trivial, Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_sub,dotProduct_smul]; exact sub_nonneg.mpr (h v)
-- sensitivity in det costs (X regular ≥ aI)
lemma le_bite (a r :ℝ)(d0:0<a)(h:A.PosDef)(p:a • (1:Matrix I I ℝ) ≤ A)(t:B ≤ A+r • (1:Matrix I I ℝ))(u:0≤r)(ht:B.PosSemidef) : B.det ≤ Real.exp ((Fintype.card I:ℝ)*r/a)*A.det:=by
 let V:=(1+r/a) • A
 have he:B ≤ V:=t.trans (by
    have ht := (le_iff.mp p).smul (div_nonneg u d0.le); unfold V; apply le_iff.mpr; convert ht using 1; rw [smul_sub,smul_smul,div_mul_cancel₀ _ d0.ne',add_smul,one_smul]; abel)
 refine (det_rise ht he).trans ?_; unfold V; rw [det_smul]; apply mul_le_mul_of_nonneg_right _ h.det_pos.le; rw [mul_div_assoc,Real.exp_nat_mul]; apply pow_le_pow_left₀ (by positivity); rw [add_comm]; exact Real.add_one_le_exp _
end YM.Chene.Melody
#print axioms YM.Chene.Melody.det_rise
