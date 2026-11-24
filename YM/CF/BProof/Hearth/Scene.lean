import YM.CF.BProof.Hearth.Grant

/-! model stamps on the windows. Alternative clan assumption at u=0 expressed paying
just the radius ≤ m from some Stamp of norm ≤2 over near *non-P fermion nodes*.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Hearth
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Spin Stint Fig Align
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
variable {N:Side}{j:ℕ}{d c a b l r ρ:ℝ} {P:Ready j a b l r}{F:Core j a b l r N}(h:Age P F d) {S:Support N} (Q:HScope N 3)
include h
lemma prefModel {M:Stamp}(T:Support (More N)){q:ℝ}(g:0≤q)(r:‖M‖≤2)(x:1≤j)(H:BoardH F 1 S c)(w:ℝ)(k:‖w‖≤1)(e:∀ i:Site N, node i ∈ T → ‖Q.val (node i)-M‖ ≤ q): ∃ V:HScope N 3,(∀ i∈T, ‖Q.val i-V.val i‖≤q)∧ gapE F 1 S V.val w=0 :=by -- include h
 let A:Quilt N:=fun i=> if i∈spot univ then M else Q.val i; have hp:∀ i, ‖A i‖≤3:=by intro i; unfold A; split; linarith; exact Q.property _
 refine ⟨⟨A,hp⟩,fun i p=>?_,?_⟩
 · by_cases g:i∈spot (univ:Support N); obtain ⟨i,hp,rfl⟩:=spotsNN _ g; simpa only [A,g,↓reduceIte] using e i p; change ‖Q.val i - A i‖≤_; rw [show A i=Q.val i from if_neg g,sub_self,norm_zero]; assumption
 change gapE F 1 S A w=_; unfold gapE; rw [match_pair (Y:=fun _=>M) A (by unfold A; simp)]; exact freeE x M w k H h
lemma stampModel(T:Support (More N)){M:Stamp}{q:ℝ}(g:0≤q)(r:‖M‖≤2)(x:1≤j)(H:BoardH F 1 S c)(e:∀ i:Site N,i∉S→node i∈T→‖Q.val (node i)-M‖≤ q): ∃ V:HScope N 3, (∀ i∈T,V.val i=Q.val i)∧ ‖gapE F 1 S V.val 0‖≤q:=by
 let A:Quilt N:=fun i=> if i∈T then Q.val i else M; have hp:∀ i,‖A i‖≤3:=by intro i; unfold A; split; exact Q.property _; linarith
 refine ⟨⟨A,hp⟩,fun i u=>if_pos u,?_⟩; apply clanModel h H x A M g; intro i u; unfold A; split; exact e i u ‹_›; simpa using g
structure Picture (N:Side)(Q:HScope N 3)(S:Support N)(q ρ:ℝ)(u:ℝ)(R:ℕ):Prop where
   near (z:Site (More N)) (h:z∈ spot S): ∃ M:Stamp, ‖M‖≤2∧ ((∀ i:Site N,node i∈ bay (terr (More N)) z R →‖Q.val (node i)-M‖≤q) ∨ (u=0∧∀ i:Site N,i∉S→node i∈ bay (terr (More N)) z R→ ‖Q.val (node i)-M‖≤ρ))
lemma modelPicture {q u:ℝ}{R:ℕ}(P₀:Picture N Q S q ρ u R)(p:1≤j)(hz:0≤q)(g:‖u‖≤1)(X:BoardH F 1 S c)(he:0≤ρ)(z:Site (More N))(e:z∈spot S)(T:Support (More N))(f:T⊆bay (terr (More N)) z R): ∃ V:HScope N 3,(∀ i∈T, ‖Q.val i-V.val i‖≤q)∧ ‖gapE F 1 S V.val u‖≤ρ:=by
 obtain ⟨M,v,H|⟨rfl,H⟩⟩:= P₀.near z e
 · obtain ⟨V,w,hV⟩:=prefModel h Q T hz v p X u g (fun i e=> H i (f e)); refine ⟨V,w,?_⟩; rwa [hV,norm_zero]
 obtain ⟨V,g,t⟩:= stampModel h Q T he v p X (fun i hz e=> H i hz (f e)); refine ⟨V,fun i hi=>?_,t⟩; rwa [g i hi,sub_self,norm_zero]
end YM.CF.BProof.Hearth
