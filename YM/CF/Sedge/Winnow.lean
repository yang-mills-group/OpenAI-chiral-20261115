import YM.CF.Sedge.Fleet
/-! Pair-wave projection when high/low are separate. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Finset NormedSpace Filter Function
attribute [local instance] opCStarAlgebra
variable {n m: Type*} [LinearOrder n][LinearOrder m][Fintype n][Fintype m]
variable (f:m↪n)(s:Finset n)(e:Deck f s)
include e
lemma tallL (C:Op n)(g:Cᵀ= -C)(h:Commute (cutM (lows f)) C): pailL f s (pairWave C)=pf C s • pairWave (summit f C):=by
  let V:=pairWave C; let S:=pailL f s; let B:=cutM (lows f)
  have ht : (summit f C)ᵀ= -summit f C:= Matrix.ext fun i j=> Matrix.ext_iff.mpr g (f i) (f j)
  have he(i:m): acts (takeF i) (S V)=acts (coupleRow (summit f C) i) (S V):=by
    rw [← (rootsL _ _ e), pull g]; unfold coupleRow; rw [act_sum,map_sum, act_sum]; simp_rw [act_smul, map_smul]; rw [←sum_subset (subset_univ (lows f))]; swap
    · intro j _ hj; have H:= Matrix.ext_iff.mpr h.eq (f i) j; rw [cutM,Matrix.diagonal_mul, Matrix.mul_diagonal,if_pos (coil_hit ..),if_neg hj,mul_zero,one_mul] at H; rw [H,zero_smul]
    unfold lows; rw [sum_map]; exact sum_congr rfl fun j _=>congrArg (fun x:Wave m=> C _ _ • x) (petals _ _ e _ _)
  have hx : (S V).ofLp ∅=pf C s:=by rw [←basis_inner,pails _ _ e,hoops,knot_empty,basis_inner]; rfl
  exact (pair_only ht he).trans (congrArg (· • _) hx)
lemma crane (C:Op n)(g:Cᵀ= -C)(h:Commute (cutM (lows f)) C){P:Op m}(p:IsStarProjection P):
 filled (addS f s P) C=pf C s • hoist f s (filled P (summit f C)):=by
  obtain ⟨U,t,hz⟩:=spot_projection P p; let v:=wedge U.val t
  have he:Sea P v:= by rw [hz]; constructor; rw [act_twistLine, inner_self_eq_norm_sq_to_K, show ‖v‖=1 from wedge_norm U t]; simp [v,wedge_norm]; exact wedge_norm .. -- tune
  let w:=hoist f s v; have hf:=stageUp f s e p he
  unfold filled; rw [Sea.scalar (projectorD _ _ p e) hf,Sea.scalar p he,←pails _ _ e,tallL _ _ e _ g h, inner_smul_right,map_smul,smul_smul]
end YM.CF.Fock
