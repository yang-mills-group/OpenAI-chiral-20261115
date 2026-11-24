import YM.SU5.Selected.Chene.Token
/-! Gaussian matrix prelim. parity colors. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Hill.Calculus
open Function Filter Finset Lattice Tree Wilson RG Pressure Exterior Work.F03 Precision MeasureTheory Chene Trunk FreeResolvent Matrix Chene.Tail Melody SectorNext.Vacuum.FlatTree
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius MatrixOrder Matrix InnerProductSpace Kronecker
section
variable {I J K:Type*}[Fintype I][DecidableEq I][Fintype J][DecidableEq J][Fintype K][DecidableEq K]
variable (M: Matrix I I ℝ)(W:Matrix I J ℝ)(u:J→I)(p:u.Injective)
lemma shelf_identity : (M.submatrix u u)=(Pad.walk u)*M*(Pad.walk u)ᵀ:=(Pad.pulse_min ..).symm
abbrev expand (u:J→I)(v:J→ℝ):= (Pad.walk u)ᵀ*ᵥ v
lemma expansion (v w:J→ℝ) : v ⬝ᵥ (M.submatrix u u *ᵥ w)= expand u v ⬝ᵥ (M*ᵥexpand u w):=by
 unfold expand; rw [shelf_identity,←mulVec_mulVec,←mulVec_mulVec,dotProduct_mulVec]; simp only [mulVec_transpose]
lemma displaced {i:I}(v:J→ℝ)(p:∀ j,u j≠i) : expand u v i=0:=sum_eq_zero fun j _=>by simp [Pad.walk,submatrix,Matrix.one_apply,p]
include p
lemma reception (j:J)(v:J→ℝ): expand u v (u j)=v j:=by
 have h(v₀:I→ℝ)(w:J): v₀ (u w)= (Pad.walk u*ᵥ v₀) w:=congrFun (Matrix.one_mulVec v₀).symm (u w)
 rw [h (expand u v) j,expand, mulVec_mulVec,Pad.pulse_cost u p,one_mulVec]
omit p
-- extend on color
abbrev page (v:I×K→ℝ)(i:K) : I→ℝ := fun j=> v (j,i)
abbrev story (A:Matrix I J ℝ)(K:Type*)[Fintype K][DecidableEq K] := A ⊗ₖ (1:Matrix K K ℝ)
lemma dotted (v w:I×K→ℝ): dotProduct v w= ∑ i:K, page v i ⬝ᵥ page w i:=by unfold dotProduct page; rw [Fintype.sum_prod_type,sum_comm]
lemma profiled (v:J×K→ℝ) (i:K) : page (story W K *ᵥ v) i=W*ᵥ page v i:=by funext j; unfold page mulVec dotProduct; rw [Fintype.sum_prod_type]; simp [story, kroneckerMap_apply,Matrix.one_apply,mul_ite,ite_mul]
lemma symmetry (p:Mᵀ=M) : (story M K)ᵀ= story M K:=by ext i j; change _=_; simp only [story,transpose_apply, kroneckerMap_apply]; rw [show M j.1 i.1=M i.1 j.1 from Matrix.ext_iff.mpr p _ _]; simp [Matrix.one_apply,eq_comm] -- tune
abbrev vouch(u:J→I)(K:Type*) (i:J×K):=(u i.1,i.2)
lemma story_cut : (story M K).submatrix (vouch u K) (vouch u K)=story (M.submatrix u u) K:=rfl
lemma inherit (p:M.PosSemidef)(K:Type*)[Fintype K][DecidableEq K]: (story M K).PosSemidef:= PosSemidef.of_dotProduct_mulVec_nonneg (isHermitian_iff_isSymm.mpr (symmetry M (isHermitian_iff_isSymm.mp p.isHermitian))) fun x=>by
 rw [star_trivial,dotted]; simp_rw [profiled]; refine sum_nonneg fun i _=>?_ ; simpa only [star_trivial] using p.dotProduct_mulVec_nonneg (page x i)
lemma inherit_d (p:M.PosDef)(K:Type*)[Fintype K][DecidableEq K]: (story M K).PosDef:= by
 apply (inherit M p.posSemidef K).posDef_iff_det_ne_zero.mpr; unfold story; rw [Matrix.det_kronecker,det_one]; exact (by have h:= p.det_pos; positivity)
end
variable {G:Gauge}{n:Side}(H:Bed){I:Type*}[Fintype I][DecidableEq I]
abbrev EdgeT (n:Side):= Edge (Site n)
-- π ext coordinates
abbrev Pens (G:Gauge)(I:Type*):= I×G.ColorIndex
abbrev Scene (G:Gauge)(I:Type*):= Pens G I→ℝ
lemma pos_all (u:ℝ)(p:0<u)(g:Gap (H.metric.acts n) u)(s:(H.metric.acts n)ᵀ=H.metric.acts n): (canopy n H).PosSemidef:=by
 unfold canopy; rw [←flat_t]; let X:= curl ℝ n; let M:= H.metric.acts n
 have hp:= (pos_by_gap s p g).posSemidef.submatrix (petals n) -- cop
 have hx:= hp.conjTranspose_mul_mul_same X; rw [conjTranspose_eq_transpose_of_trivial] at hx; exact hx.add (squared _)
open Next.Rank.Axial
abbrev cred (f : I→ Edge (Site n))(G:Gauge)(H:Bed) : Matrix (Pens G I) (Pens G I) ℝ:= story ((canopy n H).submatrix f f) G.ColorIndex
lemma above_pin (h:1<n.val)(u:ℝ)(p:0<u)(g:Gap (H.metric.acts n) u)(s:(H.metric.acts n)ᵀ=H.metric.acts n)(T:Forest (Next.Rank.Axial.whole n)) : (Pad.principal (canopy n H) T.trunks).PosDef:=by
 apply ((pos_all H u p g s).submatrix (Subtype.val: T.Free→ _)).posDef_iff_det_ne_zero.mpr; exact (pow_pos (lt_min p zero_lt_one) _ |>.trans_le (grain h H _ T.trunks (legal _ T) (lt_min p zero_lt_one) (min_le_right ..) (g.mono (min_le_left ..)) s)).ne' -- tune
lemma cred_det (s:(H.metric.acts n)ᵀ=H.metric.acts n)(T:Forest (Next.Rank.Axial.whole n)) : (cred (Subtype.val : T.Free→ _) G H).det= (Trunk.Chene n H (axle n).trunks)^(Fintype.card G.ColorIndex):=by
 unfold cred story; rw [Matrix.det_kronecker,det_one,one_pow,mul_one]; exact congrArg (·^Fintype.card G.ColorIndex) ((legal n T).signed (canopy n H) (Pad.pinned (pin ℝ n) _ (pasture_symm _ s)) (by rw [canopy,Matrix.add_mul,Matrix.mul_assoc (pin ℝ n)ᵀ,pin_angle, pasture_g, Matrix.mul_zero,add_zero]) (legal n (axle n)))
end YM.Hill.Calculus
#print axioms YM.Hill.Calculus.above_pin
