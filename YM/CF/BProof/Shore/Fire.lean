import YM.CF.BProof.Stave.Corn
/-! Partial barycentric push combining ONLY good vertices. Control in sup norm. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mesh.Shore
open Function Filter Metric Finset Stave
open scoped Matrix Matrix.Norms.Frobenius Topology BigOperators NNReal Classical -- Pi single def classical
variable {I K A C: Type*} [Fintype I][Fintype K]
variable (P:I→Prop)(L:I→K)
def bale (x:Pool I): Pool K:= fun i=> ∑ j, if P j ∧ L j=i then x j else 0
variable {P L}{S T:Finset I}{x y:Pool I}
lemma tote {j:K}(h:Sim S x)(p:j∉(S.filter P).image L): bale P L x j=0:=by
 apply sum_eq_zero; intro k _; split; rename_i e; exact h.vanish (fun z=> p (mem_image.mpr ⟨k,mem_filter.mpr ⟨z,e.1⟩,e.2⟩)); rfl
lemma goods(h:Sim S x)(p:Set.InjOn L S){i:I}(v:P i)(hp:i∈S): bale P L x (L i)=x i:=by
 unfold bale; rw [sum_eq_single i] <;> try simp only [v, and_self, and_true, true_and,↓reduceIte,mem_univ,true_or,Bool.not_true]
 · intro b _ hb; split; exact h.vanish (fun q=> hb (p q hp (And.right (by assumption)))); rfl
 simp
lemma flows {r:ℝ}(h:Sim S x)(g:Sim S y)(p:dist x y≤r)(e:Set.InjOn L S) : dist (bale P L x) (bale P L y)≤r:=by
 refine (dist_pi_le_iff (dist_nonneg.trans p)).2 fun i=>?_; by_cases H:i∈(S.filter P).image L; · obtain ⟨a,hp,rfl⟩:= Finset.mem_image.mp H; obtain ⟨pA,V⟩:=mem_filter.mp hp; rw [goods h e V pA,goods g e V pA]; exact (dist_le_pi_dist ..).trans p
 rw [tote h H,tote g H,dist_self]; exact dist_nonneg.trans p
lemma bale_p (h:Sim S x) (P:I→Prop)(L:I→K) (i:K): 0≤ bale P L x i := sum_nonneg (fun i _=>by split; exact h.pos i; exact le_rfl)
-- sum dispatch
lemma costP (h:Sim S x)(P:I→Prop)(L:I→K): Stave.tome (bale P L x)=∑ i∈S, (if P i then x i else 0):=by
 unfold Stave.tome bale; rw [sum_comm]; classical
 have he(i:I): (∑ z:K, if P i∧L i=z then x i else 0)= if P i then x i else 0:=by by_cases t:P i <;> simp [t]
 rw [sum_congr rfl (fun i _=>he i)]; exact Eq.symm (sum_subset (subset_univ _) (fun i _ p=> by simp only [h.vanish p,ite_self]))
lemma traffic(h:Sim S x) (P:I→ Prop)(L:I→K):Fuse ((S.filter P).image L) (bale P L x):=by
 refine ⟨bale_p h _ _,fun i hi=> by_contra (fun e=> mem_supp.mp hi (tote h e)),?_⟩ -- tune
 change Stave.tome _ ≤_; rw [costP h]; apply (sum_le_sum (g:=x) _).trans ((sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=>h.pos i)).trans h.mass.le); intro i _; split; rfl; exact h.pos i
lemma depot(h:Sim S x)(L:I→ K)(p:∀ i∈S,P i): Stave.tome (bale P L x)=1:=by rw [costP h]; rw [sum_congr rfl (fun i hi=> if_pos (p i hi) : ∀ i∈ S, _ = x i),sum_subset (subset_univ S) (fun i _ q=> h.vanish q),h.mass]

end YM.CF.BProof.Mesh.Shore
