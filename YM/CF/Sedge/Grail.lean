import YM.CF.Sedge.Fleet
/-! Exact high-bra projection of unipotent and propagation of external excitation operators. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Finset NormedSpace Filter Function
attribute [local instance] opCStarAlgebra
variable {m n:Type*}[LinearOrder m][LinearOrder n][Fintype m][Fintype n]
variable (f:m↪n)(s:Finset n)(D:Deck f s)
variable {P:Op m}(h:IsStarProjection P){K:Op n}(p:addS f s P*K=0)(k:K*addS f s P=K)
include D in
lemma pane (x:Ket n)(A:Op m): trailK f (acts (addS f s A) x)=acts A (trailK f x):=by
  rw [addS,act_add,map_add,economy,trails];
  have he:trailK f (acts (cutM s) x)=0:=by apply PiLp.ext; intro i; rw [seamK,cut_apply]; rw [if_neg (residueD _ _ D _)]; rfl
  rw [he,zero_add]
include D h p k
lemma halo : summit f K * P=summit f K:=by
  apply op_columns; intro i; rw [act_mul,summit_rule,←origin _ _ D,←act_mul,k,summit_rule]
lemma hoc : P*summit f K=0:=by
  apply op_columns; intro i; rw [act_mul,summit_rule, ←pane _ _ D,←act_mul,p,act_zero,map_zero,act_zero]
lemma wicker(x:Wave n): pailL f s (acts (dg K) x)=acts (dg (summit f K)) (pailL f s x):=by
  let Q:=addS f s P; have hQ:=projectorD f s h D; let T:= dg (summit f K)
  have he: dg K=∑ i:n, create (acts K (basisKet i))* remove (acts Q (basisKet i)):= by
    rw [←prizeUV,show star Q=Q from hQ.isSelfAdjoint,k]
  have ht:dg (summit f K)=∑ i : m,create (acts (summit f K) (basisKet i))* remove (acts P (basisKet i)):=by
    rw [←prizeUV,h.isSelfAdjoint, halo f s D h p k]
  rw [he,ht,act_sum,map_sum,act_sum]
  have hy (i:n): Q*(Q)=Q:=hQ.isIdempotentElem
  simp_rw [act_mul]
  let U (i:n):=create (trailK f (acts K (basisKet i)))
  have hx(i:n)(y:Wave n):pailL f s (acts (create (acts K (basisKet i))) y)=acts (U i) (pailL f s y):= by
    apply planter _ _ D P; rw [←act_mul,p,act_zero]
  have hm(i:n): pailL f s (acts (remove (acts Q (basisKet i))) x)=acts (remove (acts P (trailK f (basisKet i)))) (pailL f s x):=by
    rw [←pane _ _ D]; apply rattan _ _ D P _ ?_; rw [←act_mul,hQ.isIdempotentElem.eq] -- tune
  simp_rw [hx,hm]; rw [←sum_subset (subset_univ (lows f))]; swap
  · intro i _ g; have he':trailK f (basisKet i)=0:=by
      apply PiLp.ext; intro j; rw [seamK, basis_apply,if_neg (show f j≠i from fun l=>g (l ▸ coil_hit _ _))]; rfl
    rw [he',map_zero,show remove (0:Ket m)=0 by unfold remove; rw [map_zero,star_zero],act_zero,map_zero]
  unfold lows; rw [sum_map]; apply sum_congr rfl; intro i _; unfold U; rw [←basis_shell, trails,summit_rule]
lemma tides(x:Wave n):pailL f s (acts (exp (dg K)) x)=acts (exp (dg (summit f K))) (pailL f s x):=by
  let A:=dg K; let B:=dg (summit f K)
  have he(i:ℕ):pailL f s (acts (A^i) x)=acts (B^i) (pailL f s x):=by
    induction i with
    | zero=>simp
    | succ i ih=> rw [pow_succ',pow_succ' B,act_mul,act_mul,wicker _ _ D h p k,ih]
  let u:= pailL f s x
  let L : FC n→ₗ[ℂ] Wave n:=⟨⟨fun P=>acts P x,fun i j=> act_add ..⟩,fun c A=>act_smul ..⟩; let M :FC m →ₗ[ℂ] Wave m:=⟨⟨fun P=>acts P u,fun i j=> act_add ..⟩,fun c A=>act_smul ..⟩
  let N:=(pailL f s) ∘L L.toContinuousLinearMap; let V:=M.toContinuousLinearMap;
  have hs(i:ℕ): N (A^i)=V (B^i):=he i
  change N (exp A)=V (exp B); rw [exp_eq_tsum ℂ, exp_eq_tsum ℂ]; dsimp only
  rw [N.map_tsum ( (norm_expSeries_summable' (𝕂:=ℂ) A).of_norm), V.map_tsum ((norm_expSeries_summable' (𝕂:=ℂ) B).of_norm)]
  apply tsum_congr; intro i; rw [map_smul,map_smul,hs]
end YM.CF.Fock
