import YM.SU5.Gleam.Quiver
import YM.Progress.STATIONARY_SCENES.Probe
/-!
# Full principal minors charge narrow-minor determinants. Important: we need precise through
volume, so don't split operator difference over kept/neglected regions *everywhere*.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option quotPrecheck false
noncomputable section
namespace YM.Fineness
open Function Matrix Finset Lattice Wilson RG Exterior Precision Tree
open scoped Matrix BigOperators Classical
variable {I J K L : Type*}[Fintype I][Fintype J][Fintype K][DecidableEq I][DecidableEq J][DecidableEq K]{u:ℝ}
private lemma fischer (X:Sheet (I⊕J))(A:Sheet I)(B:Sheet J)(H:X.PosDef)(f:A=X.submatrix Sum.inl Sum.inl)(v:B=X.submatrix Sum.inr Sum.inr) : X.det ≤ A.det* B.det :=by
 let D:= X.submatrix Sum.inl Sum.inr
 have h:A.PosDef:=f.symm ▸ H.submatrix Sum.inl_injective; let t:B.PosDef:=v.symm ▸ H.submatrix Sum.inr_injective
 have hx:X= fromBlocks A D Dᴴ B:=by
    rw [f,v]; ext (i|i) (j|j)
    · rfl
    · rfl
    · change X _ _=star (X (.inl _) (.inr _)); rw [star_trivial]; exact Eq.symm (congrFun (congrFun ((q_iff X).1 H).1 (.inr i)) (.inl j))
    rfl
 letI:= h.isUnit.invertible
 let Y:= B-Dᴴ * A⁻¹ * D; have hP:Y.PosSemidef:= (Matrix.PosDef.fromBlocks₁₁ D B h).1 (hx ▸ H.posSemidef)
 have he:X.det=A.det*Y.det:=by rw [hx,det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
 have hv:Y.det≠0:= fun t=>by have h:=H.det_pos; rw [he,t,mul_zero] at h; exact lt_irrefl _ h
 have hp:Y.det≤B.det:=(harvested (hP.posDef_iff_det_ne_zero.mpr hv) ((q_iff B).1 t).1 (fun x=>?_)).2
 · rw [he]; exact mul_le_mul_of_nonneg_left hp h.det_pos.le
 rw [show Y=B-(Dᵀ * A⁻¹ * D) from congrArg (fun L=> B-L*A⁻¹*D) (conjTranspose_eq_transpose_of_trivial _)]
 unfold qpay; rw [Matrix.sub_mulVec,dotProduct_sub]; exact sub_le_self _ (show 0 ≤ qpay (Dᵀ * _ * D) x from by rw [qgain]; exact cost_zero _ h.inv _)
 -- refine have tactic order?
-- restrict given equiv
private lemma courtyard (X:Sheet K)(H:X.PosDef)(e:I ⊕ J ≃ K)(C:ℝ)(p:∀ i,X i i ≤ C)(A:Sheet I)(h:A=X.submatrix (fun i=> e (Sum.inl i)) (fun i=> e (Sum.inl i))) : A.PosDef ∧ Real.log X.det ≤ Real.log A.det + C*(Fintype.card J):=by
 let Z:= X.submatrix e e;
 let Hp : Z.PosDef := H.submatrix e.injective; let B:= Z.submatrix Sum.inr Sum.inr; have pA:A.PosDef:= h.symm ▸ Hp.submatrix Sum.inl_injective; have pB:B.PosDef:= Hp.submatrix Sum.inr_injective
 refine ⟨pA,?_⟩; apply le_trans (b:=Real.log (A.det*B.det)); · exact Real.log_le_log H.det_pos ((det_submatrix_equiv_self e X).symm.trans_le (fischer Z A B Hp h rfl))
 rw [Real.log_mul pA.det_pos.ne' pB.det_pos.ne']; apply add_le_add_right; refine (volume_ceiling pB).trans ((sum_le_sum (f:=fun i=>B i i) (g:=fun _=> C) (fun i _=> p _)).trans_eq ?_); rw [sum_const,nsmul_eq_mul,mul_comm,card_univ]

variable {c n : Side}{r: Ratio c n}{η M:ℝ}
namespace Stair
variable {a b:Finset I} (t:a⊆ b)
include t
private def lodge (x : a⊕ ↥(b\a)) : b:= Sum.elim (fun q:a=> ⟨q.val,t q.property⟩) (fun q:↥(b\a)=>⟨q.val,(mem_sdiff.mp q.property).1⟩) x
noncomputable def joinE : a⊕ ↥(b\a)≃ b := Equiv.ofBijective (lodge t) (by
 constructor
 · rintro (x|x) (y|y) p
   · exact congrArg Sum.inl (Subtype.ext (congrArg (α:=↥b) Subtype.val p)) -- defeq tune
   · exact ((mem_sdiff.mp y.property).2 ((show x.val=y.val from congrArg Subtype.val p) ▸ x.property)).elim
   · exact ((mem_sdiff.mp x.property).2 ((show x.val=y.val from congrArg Subtype.val p).symm ▸ y.property)).elim
   exact congrArg Sum.inr (Subtype.ext (congrArg (α:=↥b) Subtype.val p))
 rintro ⟨x,w⟩; by_cases p:x∈a; exact ⟨.inl ⟨x,p⟩,rfl⟩; exact ⟨.inr ⟨x, mem_sdiff.mpr ⟨w,p⟩⟩,rfl⟩)
end Stair
section determinant
variable {T:Forest r} {a b:Finset T.Free}
def coinVec (T:Forest r)(a:Finset T.Free) (A:Sheet (Body 1 n)) : Sheet a := (seatsF T a)ᵀ * A * seatsF T a
lemma coinVec_uses (T:Forest r)(a:Finset T.Free)(A:Sheet (Body 1 n))(x y:a) : coinVec T a A x y=A (turnBond n x.val.val) (turnBond n y.val.val):=by
 simp [coinVec,seatsF,branchesZ,Matrix.mul_apply,ite_mul,mul_ite]
open Progress.StationaryScenes.Green
lemma stairEstimate (Z:Bed) (p:0≤η)(w:Z.metric.strip η M) : ∀ i:Body 1 n,(Precision.K (Z.metric.acts n)) i i≤ kinetic η M:=by
 intro i
 let f(x y:Body 1 n):= (wt η x.1 y.1)*|(Precision.K (Z.metric.acts n)) x y|
 have ht : 0≤η:=p
 have hp:= (single_le_sum (s:=univ) (f:=f i) (fun j _=> mul_nonneg (wt_pos ..).le (abs_nonneg _)) (mem_univ i)).trans (kinetic_price n Z w p i); simp [f,wt] at hp; exact (le_abs_self _).trans hp
lemma looks (Z:Bed)(hz:(Z.metric.acts n).PosDef)(hK:∀ i, (Precision.K (Z.metric.acts n)) i i≤ u)(q:Buttress T b)(p:a⊆b): let A:=Z.metric.acts n; let H:=coinVec T a (Precision.K A); H.PosDef ∧ Real.log (leasePart A) ≤ Real.log H.det + u*(b.card-a.card:ℕ) :=by
 intro A H; let C:=coinVec T b (Precision.K A); let e:= Stair.joinE p; have he : H=C.submatrix (fun i=>e (.inl i)) (fun i=> e (.inl i)):=by ext i j; unfold C H; rw [submatrix_apply,coinVec_uses,coinVec_uses]; rfl
 obtain ⟨s,f⟩:= q.precision hz
 obtain ⟨hr,hw⟩:= courtyard C s e u (fun i=> by unfold C; rw [coinVec_uses]; exact hK _) _ he
 rw [Fintype.card_coe, Finset.card_sdiff_of_subset p] at hw; exact ⟨hr,(Real.log_le_log (lattice_pos hz) f).trans hw⟩
end determinant
end YM.Fineness
#print axioms YM.Fineness.looks
