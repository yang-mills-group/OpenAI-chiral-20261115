import YM.CF.BProof.Site.Micro
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Paths
import YM.Next.RANK.Stretch
import YM.Extra.ITERATION_NO_LOSS.Geometry

/-! Footprints for retained path stencils, including inspection. We use 8-halo for
all the weak atoms. No loss of support exponential in the ingredients. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Micro
open RG Wilson Lattice Relation Finset Function Push.AbsoluteSums.Paths Next.Rank.Thirst Extra.Iteration.Shapes ConnectedActivityE6.Raw
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{s:Side}(σ:Signed)(o:Site s){d:ℕ}
lemma lives_loc (l: Slot): Loc (lives o l):=by rw [reached]; exact visits_loc _ _
lemma lives_card (l: Slot): (lives o l).card ≤ l.length+1:=by rw [reached]; apply le_trans (visits_length ..); rw [List.length_append]; exact le_rfl
lemma lives_sub (l: Slot){r:ℕ} (h:l.length≤r): lives o l⊆halo r {o}:=by
 rw [reached]; intro x hx; exact halo_spec.mpr ⟨o,mem_singleton_self _,(visits_dist o x _ (List.mem_toFinset.mp hx)).trans ((List.length_append ..).trans_le h)⟩
lemma bundle_here (A: Fin d→Slot): bundle o A={o}∪ univ.biUnion (fun i=> lives o (A i)):=by rw [singleton_union]; rfl
lemma bundle_loc (A:Fin d→ Slot): Loc (bundle o A):=by rw [bundle_here]; exact Grid.pile _ (single o) (fun i=> lives o (A i)) (fun i _=>lives_loc _ _) (fun i _=> ⟨o,mem_singleton_self _, starts o _⟩) -- starts namespace?
lemma inspected_sub (S:Support s): inspected S⊆ halo 8 S:=Next.Rank.Thirst.inspect S
lemma atomHL_loc (A:Atom G d): Loc (halo 8 (A.footprint o)):= by rw [atom_foot]; exact halo_loc 8 (bundle_loc _ _)
lemma atomHL_local (A:Atom G d)(p:BudgetPoint) : LocalOn (↑(halo 8 (A.footprint o))) (fun U=> A.placed p U o):=fun U V h=> placed_local A p o U V (agrees_mono h (Finset.coe_subset.mpr (inspected_sub _)))
lemma atomHL_card (A:Atom G d) : (halo 8 (A.footprint o)).card ≤ (2*17^4)*(A.length+1):=by
 apply le_trans (Corona.halo_size ..); have ht:=Nat.mul_le_mul_right (17^4) (steps A o); nlinarith only [ht] -- tune
lemma atomHL_span (A:Atom G d)(t:Site s)(h:t∈ halo 8 (A.footprint o)): separation t o≤ A.length+8:=by
 obtain ⟨p,hp,ht⟩:= halo_spec.mp h; rw [atom_foot] at hp -- collision shadow
 rw [separation_comm]; exact (separation_triangle _ p t).trans (Nat.add_le_add (where_slot o _ p hp) ht)

lemma pair_loc (x:Pressure.Cell s)(A:PathData G)(i:ℕ×ℕ)(b:ℕ): Loc (pairFoot b A x i):= Grid.join (halo_loc b (single _)) (bundle_loc x.1 _) x.1 (halo_subset b _ (mem_singleton_self _)) (mem_insert_self ..)
lemma pair_card (x:Pressure.Cell s)(A:PathData G)(i:ℕ×ℕ)(b:ℕ): (pairFoot b A x i).card ≤ (2*b+1)^4 + length (duplex A x.2 i)+3:=by
 let D:=duplex A x.2 i
 have hi:(halo b ({x.1}:Support s)).card≤ (2*b+1)^4:=by have ht:= Corona.halo_size ({x.1}:Support s) b; simpa [two_mul] using ht
 have he:(bundle x.1 D).card ≤ 1+ length D+2:=by
   rw [bundle_here]; refine (card_union_le ..).trans ?_; rw [card_singleton]; exact (Nat.add_le_add_left (m:=∑ i:Fin 2,((D i).length+1)) (card_biUnion_le.trans (sum_le_sum fun i _=>lives_card ..)) 1).trans (by rw [sum_add_distrib]; simp [length,Nat.add_assoc]) -- tune
 apply (card_union_le (halo b {x.1}) (bundle x.1 D)).trans; unfold D at *; omega
lemma pair_span (x:Pressure.Cell s)(A:PathData G)(i:ℕ×ℕ)(b:ℕ)(z:Site s)(h:z∈pairFoot b A x i) : separation z x.1 ≤ length (duplex A x.2 i)+b:=by
 rw [separation_comm]; rcases mem_union.mp h with h|h; exact le_trans (show separation x.1 z ≤ b from by simpa [halo_spec] using h) (by omega); exact le_trans (where_slot x.1 _ _ h) (by omega)
end YM.CF.BProof.Micro
