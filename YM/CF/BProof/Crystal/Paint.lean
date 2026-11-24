import YM.CF.BProof.Crystal.Page
/-! Yard of expanded decorated matching elements, without need for
independence of choices inside vertices. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Crystal
open Function Filter Fock Finset NormedSpace Garden Align Wick Double Pastry Sprinkle Lattice Tenant Palot Gas Branch Stilo
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
variable {V I: Type}[DecidableEq V][Fintype V][Fintype I][LinearOrder I]{P:Dew V I}
variable {N:Side} {A: V→ℂ}{F:I→I→Support N→ℂ}
lemma subsidize {S T:Finset (Deco P N)}(u:S⊆T)(a: Smooth T∧P.Honest T): Smooth S∧ P.Honest S:=by
 have he : (↑(down S): Set V) ⊆ ↑(down T):= coe_subset.mpr (image_subset_image u)
 exact ⟨Set.InjOn.mono (coe_subset.mpr u) a.1,Set.Pairwise.mono he a.2.1,Set.Pairwise.mono he a.2.2⟩
lemma squared (x y: FC I): inner ℂ (acts x (vacuum I)) (acts y (vacuum I))=(star x*y) ∅ ∅:=by nth_rw 1 [← star_star x]; rw [act_inner,←act_mul, vacuum,basis_inner,basis_act]
theorem Civic.divide (p:Civic N P)(h:p.Code F){S T:Finset (Deco P N)}(t: Disjoint S T)(d: Disjoint (S.biUnion (fun i=>(p.border i).val)) (T.biUnion (fun i=>(p.border i).val)))(f:∀ i∈S∪T,P.litmus A F i≠0) : P.notch (S∪ T) (down (S∪T))=P.notch S (down S)*P.notch T (down T):=by
 let X:=(S.biUnion fun i=>(p.border i).val); let Y:=(T.biUnion fun i=>(p.border i).val); have hz: Disjoint (p.room X) (p.room Y):= disjoint_left.mpr fun _ hi hj=> disjoint_left.mp d (mem_filter.mp hi).2 (mem_filter.mp hj).2; have hx:Sector (p.room X) false (P.light S).val:= p.costume h (fun i v=> f _ (mem_union_left _ v)) Subset.rfl; have hy: Sector (p.room Y) false (P.light T).val:= p.costume h (fun i v=> f _ (mem_union_right _ v)) Subset.rfl; have ht:=p.styleB S X Subset.rfl; have he:=p.styleB T Y Subset.rfl
 have H1:P.beam (down (S∪T))=P.beam (down S)*P.beam (down T):=by rw [down,image_union]; exact prod_union (p.downDis d)
 unfold Dew.notch; rw [H1,show P.light (S∪T)=_ from (prod_union (f:=P.flareL) t: P.light (S∪T)=P.light S * P.light T),squared,squared,squared]; let C:=(P.light S).val; let K:=(P.light T).val; let U:=(P.beam (down S)).val; let W:=(P.beam (down T)).val; change (star (C*K)*(U*W)) _ _=_; rw [star_mul,← (council hx.contr hy.contr hz).eq,(council ht hy.contr hz).symm.mul_mul_mul_comm]; exact Sector.sliced (hx.contr.mul ht) (hy.contr.mul he) hz _
theorem Civic.gather (p:Civic N P)(A:V→ℂ)(h:p.Code F): Gas.Yard p.border (P.quartet A F):=by
 have ht:Smooth (∅:Finset (Deco P N))∧ P.Honest (∅:Finset (Deco P N)):=by unfold Smooth Dew.Honest down Dew.mild Dew.terse Set.PairwiseDisjoint; simp only [image_empty,coe_empty,Set.injOn_empty,true_and]; exact ⟨Set.pairwise_empty _,Set.pairwise_empty _⟩
 constructor; · rw [Dew.quartet,if_pos ht]; unfold Dew.quint Dew.notch Dew.light Dew.beam down; simp [squared]
 intro i j d t; by_cases u:Smooth (i∪j)∧P.Honest (i∪j); swap
 · have he:¬ (Smooth i ∧ P.Honest i) ∨ ¬(Smooth j ∧ P.Honest j):=by by_contra! e; exact u ⟨p.smooth d e.1.1 e.2.1,p.vicinity d e.1.2 e.2.2⟩
   rw [Dew.quartet,if_neg u]; rcases he with he|he; simp [Dew.quartet,he]; simp [Dew.quartet,he]
 unfold Dew.quartet Dew.quint; rw [if_pos u,if_pos (subsidize subset_union_left u), if_pos (subsidize subset_union_right u)]; by_cases v:(∏ x∈i∪j,P.litmus A F x) ≠0; rw [p.divide h t d (fun _ hh hp=> v (prod_eq_zero hh hp)), prod_union t,mul_mul_mul_comm]; rw [ne_eq,not_not] at v; rw [v, zero_mul, mul_mul_mul_comm,←prod_union t,v,zero_mul]
end YM.CF.BProof.Crystal
