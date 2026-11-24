import YM.CF.BProof.Wick.Banner
import YM.CF.BProof.Wick.Cliff
import YM.CF.BProof.Wick.Diver

/-! Exact real-part log at endpoint, canonical sign conventions paid separately. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Wick
open Function Filter NormedSpace Fock Finset Branch Align
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type*}[Fintype I][LinearOrder I] [Nonempty I] {A P Q C:Op I} {c r:ℝ} {x:Wave I}
def overlap (C:Op I)(x:Wave I):= inner ℂ (pairWave C) x
def feeB (A:Op I):= (pencil (A-1)).trace.re
def tickCost (A C:Op I):= (pencil (-widthP A C)).trace.re/4
lemma earning {A: Op I}(h:‖A-1‖<1): Real.log ‖A.det‖=feeB A:=by simpa only [feeB,add_sub_cancel] using logNorm h
namespace Shelf
variable (s:Shelf A C c)
include s
lemma bolts : tickCost A C=netsal A C:=by
 let T:=-widthP A C; have ht: ‖T‖<1:=by unfold T; rw [norm_neg]; exact s.widthN.trans_lt s.small
 change _=(invoice _).re/_; have he:shrinkV A C=1-widthP A C:=s.middle; rw [he, show 1-widthP A C-1=T from (by unfold T; abel), tally_log ht]; rfl
lemma money : Real.exp (tickCost A C)= ‖filled A C‖:= by rw [s.bolts]; refine to_sal s.proj s.sym ?_; rw [show shrinkV A C=1-widthP A C from s.middle, show 1-widthP A C-1 = -widthP A C from by abel,norm_neg]; exact s.widthN.trans_lt s.small
lemma charged (t:Task A x) : ‖overlap C x‖=‖x‖*Real.exp (tickCost A C):=by
 rw [s.money]; obtain ⟨c,u,v,g,e⟩:= t.rebase; rw [filled,Sea.scalar s.proj v,norm_smul,v.2,mul_one,e,norm_smul,v.2,mul_one]; unfold overlap; rw [inner_smul_right,norm_mul, norm_inner_symm]
lemma bills (t:Task A x) : overlap C x ≠ 0:= norm_pos_iff.mp (by rw [s.charged t]; exact mul_pos (norm_pos_iff.mpr t.nonzero) (Real.exp_pos _))
end Shelf
lemma hutch_bound (h:IsStarProjection P)(g:IsStarProjection A)(u:c • P ≤ P*A*P)(k:c≤1)(p:0<c): ‖hutch A P-1‖ ≤ 1-c ∧ ‖hutch A P -1‖<1:=by
 let E:= hutch A P; have hp:=hutch_earn h u k; have he:E≤1:= by
    have ht:= star_left_conjugate_le_conjugate (sub_nonneg.mp g.one_sub.nonneg) P; rw [h.isSelfAdjoint,mul_one,h.isIdempotentElem] at ht; exact (add_le_add (show P*A*P≤P from ht) (le_refl (1-P))).trans_eq (add_sub_cancel ..) -- order
 have hx: ‖E-1‖≤1-c:=by rw [norm_sub_rev]; exact betweenNorm (sub_nonneg.mpr k) (sub_nonneg.mpr he) (by rw [sub_smul,one_smul]; exact sub_le_sub_left hp _)
 exact ⟨hx,hx.trans_lt (sub_lt_self 1 p)⟩
lemma logWay {P S:Op I}(t: Task P x)(h:Fit P S): Real.log ‖acts (quant S) x‖=Real.log ‖x‖+Real.log ‖(entered P S).det‖/2:=by
 have he:= t.quantS h; have hp: Matrix.det (entered P S)≠0:= isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).1 h.active); have hz := congrArg Real.log (t.town h); rw [Real.log_mul (by exact pow_ne_zero _ (norm_ne_zero_iff.mpr t.nonzero)) (norm_ne_zero_iff.mpr hp),Real.log_pow,Real.log_pow] at hz; push_cast at hz; linarith
set_option maxHeartbeats 200000 in
lemma lines (b:Board A P Q c)(t: Task A x)(u: Align.Twig C P)(s:Shelf (floorH A P Q 0) C r) :
    Real.log ‖overlap C (acts (quant (house A P Q 0)) x)‖= Real.log ‖x‖+
              (feeB (hutch A P)+feeB (hutch (1-wedgeQ A P) Q))/2+tickCost (entryP A P Q) C :=by
 let S:=house A P Q 0; let y:=acts (quant S) x; let P':=entryP A P Q; have he:= t.quantS b.fit0;
 let G:= hutch A P; let H:= hutch (1-wedgeQ A P) Q; let T:=overlap C y; have hx : ‖G.det‖≠0:= by have hi:=b.child.active; rw [b.roof] at hi; exact norm_ne_zero_iff.mpr (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det G).1 hi))
 have hy: ‖H.det‖≠0:= norm_ne_zero_iff.mpr (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det H).1 (active b.nice (hutch_earn (A:=1-wedgeQ A P) b.q b.loftHole b.bare))))
 rw [s.charged he]; set Z := tickCost (floorH A P Q 0) C with hz; have hv: ‖y‖≠0:=norm_ne_zero_iff.mpr he.nonzero; rw [Real.log_mul (x:=‖y‖) hv (Real.exp_pos Z).ne', logWay t (S:=S) b.fit0, show Matrix.det (entered A S)=G.det * H.det from detRoom b,norm_mul,Real.log_exp,Real.log_mul hx hy]; unfold G H; rw [hz]

 have hf: widthP (floorH A P Q 0) C=widthP P' C:=by
    have h1:offCut (floorH A P Q 0) C=offCut P' C:=by rw [←b.PiHe]; exact Shoot (A:=P) (P:=entryP A P Q) b.p u (swapOrth b.p b.PiHp b.offPiH) b.PiHp
    unfold widthP; rw [h1]
 have heq:tickCost (floorH A P Q 0) C=tickCost P' C:= by rw [tickCost,tickCost,hf]
 rw [heq,earning (hutch_bound b.p b.a b.holes b.bare b.nice).2, earning (hutch_bound b.q b.leaves.one_sub b.loftHole b.bare b.nice).2]
end YM.CF.BProof.Wick
