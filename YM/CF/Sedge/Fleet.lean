import YM.CF.Sedge.Flake
/-! Injection exact on sector lines, orientation pins pure. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Finset NormedSpace Filter Function
attribute [local instance] opCStarAlgebra
variable {n m: Type*} [LinearOrder n][LinearOrder m][Fintype n][Fintype m]
variable (f:m↪n)(s:Finset n)(h:Deck f s)
include h
lemma dorm (A:Op m) : acts (quant (addS f s A)) (basisKet s)= basisKet s:=by
  let Q:=quant (cutM s); let U:= quant (addS f s A)
  have he:acts Q (basisKet s)=basisKet s:=by rw [show Q=cutM s.powerset from quantCut _, cut_basis,if_pos (mem_powerset.mpr (subset_refl _))]
  nth_rw 1 [←he]; rw [←act_mul, show quant (addS f s A)*Q=Q from ?_,he];
  unfold Q; rw [←quant_mul,addS,add_mul,(cutM_idp _).isIdempotentElem.eq,wingK _ _ h,add_zero]
lemma freezes (A:Op m)(x:Wave m): hoist f s (acts (quant A) x)=acts (quant (addS f s A)) (hoist f s x):=by
  let T:=quant (addS f s A); let L:=hoist f s
  have he(t:Finset m):hoist f s (acts (quant A) (basisKet t))=acts T (hoist f s (basisKet t)):=by
    induction t using Finset.induction_on with
    | empty=> rw [hoops,knot_empty,dorm _ _ h A,show acts _ _=basisKet (∅: Finset m) from quant_vac A,hoops,knot_empty]
    | @insert i t g ih=>
      rw [create_basis_is i t g, map_smul,map_smul,map_smul,map_smul]; congr 1
      rw [hoist_put,←act_mul, ←act_mul T, quant_put A, quant_put,act_mul,hoist_c _ _ h,ih,act_mul,←basis_shell,origin _ _ h] -- tune
  nth_rw 1 2 [←basis_expand x]; simp_rw [map_sum,map_smul,he]; rfl
lemma uniform_grade {N:ℕ}(A:Op m)(g:A.trace=(N:ℂ))(hp:N≤Fintype.card m): lineOp A=quant A * selector m N:=by
  unfold lineOp; simp only [g,choose_nat _ _ _ hp,ite_smul,one_smul,zero_smul,sum_ite_eq, mem_range, Nat.lt_succ_of_le hp,ite_true]
omit f s h in
lemma appoint {a:ℕ} (i:Finset m): acts (selector m a) (basisKet i)= if i.card=a then basisKet i else 0:=by simp [selector,cut_basis]
lemma jars (t:Finset m): (fog f s t).card=s.card+t.card:=by
  unfold fog; rw [card_union_of_disjoint (h.splitL.symm.mono_right (Finset.map_subset_map.mpr (subset_univ t))), card_map]
lemma billow (a:ℕ)(x:Wave m): hoist f s (acts (selector m a) x)=acts (selector n (s.card+a)) (hoist f s x):=by
  nth_rw 1 2 [←basis_expand x]; simp_rw [map_sum,map_smul]
  refine sum_congr rfl ?_; intro i _
  rw [appoint i,hoops]; obtain ⟨c,hc,hB⟩:=knotW f s h i
  rw [hB,map_smul,appoint, jars _ _ h]; split_ifs with q p p
  · rw [hoops,hB]
  · omega
  · omega
  simp
lemma flying {P:Op m} (p:IsStarProjection P)(x:Wave m): acts (lineOp (addS f s P)) (hoist f s x)= hoist f s (acts (lineOp P) x):=by
  obtain ⟨U,t,g⟩:= spot_projection P p; have hp : P.trace=(t.card:ℂ):=by rw [g,trace_twist,trace_cut]
  have he:= projectorD f s p h; have hz : (addS f s P).trace=((s.card+t.card:ℕ):ℂ):=by rw [addS,Matrix.trace_add,trace_cut,desk_trace,hp,Nat.cast_add]
  have hy : lineOp (addS f s P)=quant (addS f s P)* selector n (s.card+t.card):= uniform_grade (Embedding.refl _) ∅ ⟨by simp⟩ _ hz (jars _ _ h t ▸ card_le_univ (fog f s t)) -- tune
  rw [hy, uniform_grade f s h _ hp (card_le_univ t),act_mul,act_mul,← billow _ _ h, freezes _ _ h]
lemma stageUp {P:Op m} (p:IsStarProjection P) {v:Wave m}(k:Sea P v): Sea (addS f s P) (hoist f s v):=⟨by rw [flying _ _ h p,k.1],by rw [hoistN _ _ h, k.2]⟩
lemma strands {b:n} (g:b∉lows f)(e:b∉s)(x:Wave m): acts (takeF b) (hoist f s x)=0:=by
  nth_rw 1 [←basis_expand x]; rw [map_sum,map_sum]; refine sum_eq_zero fun i _=>?_;
  rw [map_smul,hoops,map_smul]; obtain ⟨c,hx,hB⟩:=knotW f s h i; rw [hB,map_smul,take_act,if_neg,smul_zero,smul_zero]
  exact fun p=>g (Finset.map_subset_map.mpr (subset_univ _) ((mem_union.mp p).resolve_left e))
lemma fur {b:n} (g:b∈s)(x:Wave m): acts (put b) (hoist f s x)=0:=by
  nth_rw 1 [←basis_expand x]; rw [map_sum,map_sum]; refine sum_eq_zero fun i _=>?_;
  rw [map_smul,hoops,map_smul]; obtain ⟨c,hx,hB⟩:= knotW f s h i; rw [hB,map_smul,put_act,if_pos (show b∈fog f s i from mem_union_left _ g),smul_zero,smul_zero]
lemma petals(i:m)(x:Wave n):pailL f s (acts (put (f i)) x)=acts (put i) (pailL f s x):=by
  apply PiLp.ext; intro j; rw [←basis_inner,pails _ _ h,←act_inner,←basis_inner (acts (put _ ) _),← act_inner]; change inner ℂ (acts (takeF _) _) x=inner ℂ _ _; rw [←hoist_t _ _ h,← pails _ _ h];
lemma rootsL(i:m)(x:Wave n): pailL f s (acts (takeF (f i)) x)=acts (takeF i) (pailL f s x):=by
  apply PiLp.ext; intro j; rw [←basis_inner,pails _ _ h,←act_inner,←basis_inner (acts (takeF _ ) _),←act_inner]; rw [takeF,takeF,star_star,star_star,←hoist_put, pails _ _ h]
lemma branchX {b:n}(g:b∉lows f)(e:b∉s)(x:Wave n):pailL f s (acts (put b) x)=0:=by
  apply PiLp.ext; intro j; rw [←basis_inner,pails _ _ h,←act_inner,show acts _ _=0 from strands _ _ h g e _,inner_zero_left]; rfl
lemma chipsX{b:n}(g:b∈s)(x:Wave n): pailL f s (acts (takeF b) x)=0:=by
  apply PiLp.ext; intro j; rw [←basis_inner,pails _ _ h,←act_inner,takeF,star_star,fur _ _ h g _,inner_zero_left]; rfl
lemma rattan (P:Op m)(e:Ket n)(g:acts (addS f s P) e=e)(x:Wave n):pailL f s (acts (remove e) x)=acts (remove (trailK f e)) (pailL f s x):=by
  rw [remove_def,act_sum,remove_def,act_sum,map_sum]; simp_rw [act_smul,map_smul]
  rw [←sum_subset (subset_univ (lows f))]; swap
  · intro i _ hi; by_cases he:i∈s; rw [chipsX f s h he,smul_zero]
    have hp:e.ofLp i=0:=by
      nth_rw 1 [←g]; rw [addS,act_add]; simp only [WithLp.ofLp_add,Pi.add_apply,cut_apply,he,ite_false,zero_add]; rw [economy,basin _ _ _ hi]
    rw [hp,star_zero,zero_smul]
  unfold lows; rw [sum_map]; refine sum_congr rfl ?_; intro i _; rw [rootsL f s h,seamK]
lemma planter (P:Op m)(e:Ket n)(g:acts (addS f s P) e=0)(x:Wave n):pailL f s (acts (create e) x)=acts (create (trailK f e)) (pailL f s x):=by
  rw [create_def,act_sum,create_def,act_sum,map_sum]; simp_rw [act_smul,map_smul]
  rw [←sum_subset (subset_univ (lows f))]; swap
  · intro i _ hi; by_cases hp:i∈s
    · have he : (acts (addS f s P) e).ofLp i=e.ofLp i:=by rw [addS,act_add,economy,WithLp.ofLp_add,Pi.add_apply,cut_apply,if_pos hp,basin _ _ _ hi,add_zero]
      rw [←he,g]; simp
    rw [branchX _ _ h hi hp,smul_zero]
  unfold lows; rw [sum_map]; refine sum_congr rfl ?_; intro i _; rw [petals _ _ h,seamK]
end YM.CF.Fock
