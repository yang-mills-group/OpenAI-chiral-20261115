import YM.CF.Rel.Cost
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
variable {f:SpaceX G n}{o:Site n}
abbrev KitM(G:Gauge)(n:Side)(m:ℕ):= Disk n m→Delph G m
abbrev hallmark (o:Site n)(r:ℕ): Finset (Body 2 n):= pavilion r o ×ˢ univ
abbrev Pots(o:Site n)(r:ℕ)(m:ℕ):=scope n (hallmark o r) m
lemma shade_p{o:Site n}{x: Disk n m}: x∈Pots o l m ↔ ∀ i,separation o (x i).1 ≤ l:=by simp [Pots,scope,hallmark,theatre]
def engages(W: KitM G n m)(k: Disk n m)(A:Fin m→InputZ G n):= W k (fun i=>sumH G (A i) (k i))
def payM(m r:ℕ):ℝ:=payF r^m*((plot r* Fintype.card Axis)^m:ℕ)
lemma rink (V:Nacre.AimX m G n ℂ)(A:Fin m→InputZ G n): V A=∑ v:Dike n m,timeA V v (fun i=>collect G (A i) (v i)):=by
 let P(i:Fin m)(j:Blip n):=Nacre.put G n j (collect G (A i) j)
 rw [show V A=V (fun i=>∑ j,P i j) from congr_arg (fun x=>V x) (funext fun i=> put_sum _),ContinuousMultilinearMap.map_sum]; rfl
lemma plaque(h:Atom f o r)(hs:ContDiffAt ℝ m (satX f) 0)(hp:cFoot m (satX f))(hz:payG r<n.val)(hc:‖cake m (satX f)‖≤ C): ∃ W:KitM G n m,(∑ i,‖W i‖) ≤ payM m r*C∧ (∀ i,i∉Pots o (payG r) m→ W i=0)∧ (∀ A:Fin m→InputZ G n, cake m (satX f) A=∑ p,engages W p A):=by
 let V:=cake m (satX f); obtain ⟨P,hP⟩:=repayB (G:=G) (r:=r) (n:=n) (by unfold payG at hz; omega) hz o
 let X:=scope n (spoke o r) m; let K(j:Dike n m)(q:Disk n m):= (∏ i,P (j i) (q i)); let Q(q:Disk n m):=∑ i∈X,K i q • timeA V i; refine ⟨Q,?_,?_,?_⟩
 · have hK (j:Dike n m) (hj:j∈X): (∑ i,‖K j i‖)≤ payF r^m:=by
      calc
       _ = ∏ k:Fin m,∑ i:Body 2 n, |P (j k) i|:=by unfold K Disk; simp_rw [Real.norm_eq_abs,Finset.abs_prod]; exact (Fintype.prod_sum (fun k:Fin m=>(fun i=> |P (j k) i|))).symm
       _ ≤ ∏ k:Fin m, payF r:= Finset.prod_le_prod (fun k _=>sum_nonneg fun i _=>abs_nonneg _) (fun k _=> (hP _ (Fintype.mem_piFinset.mp hj k)).1)
       _ = _:=by simp
   apply (sum_le_sum (g:=fun i=> ∑ j∈X, ‖K j i • timeA V j‖) (fun i _=> norm_sum_le ..)).trans; rw [sum_comm]; simp_rw [norm_smul,← sum_mul]; apply (sum_le_sum (g:=fun i=>payF r^m*‖timeA V i‖) (fun i hi=>mul_le_mul_of_nonneg_right (hK _ hi) (norm_nonneg _))).trans; rw [←mul_sum,payM,mul_assoc]
   apply mul_le_mul_of_nonneg_left _ (by unfold payF; positivity); exact (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun j _ _=>norm_nonneg _)).trans (sum_cost h hs hc)
 · intro p hh; unfold Q; apply sum_eq_zero; intro i hi
   rw [show K i p=0 from ?_,zero_smul]; unfold K; rw [shade_p,not_forall] at hh; obtain ⟨j,hj⟩:= hh; apply Finset.prod_eq_zero (mem_univ j); have hp : i j∈spoke o r:= Fintype.mem_piFinset.mp hi j; exact not_not.mp (mt ((hP (i j) hp).2.1 (p j)) hj)
 intro A; let G'(i):= fullG o (A i); let g(v:Dike n m):= timeA V v (fun i=> collect G (G' i) (v i)); rw [top_p h hs hp]; calc
    _ = ∑ v, g v:= rink ..
    _ = ∑ v∈X,g v:=by symm; apply sum_subset (subset_univ _); intro i _ hh; unfold X scope at hh; rw [Fintype.mem_piFinset,not_forall] at hh; obtain ⟨j,hj⟩:=hh; unfold g V; rw [spelt h hs j (by rw [vapour,not_le] at hj; exact hj)]; rfl
    _ = _:=by unfold engages Q; simp only [_root_.sum_apply,_root_.smul_apply]; rw [sum_comm (s:= (univ:Finset (Disk n m)))]; apply sum_congr rfl; intro i hi; unfold g G'; simp_rw [fun k=> (hP (i k) (Fintype.mem_piFinset.mp hi k)).2.2 (A k)]; rw [ContinuousMultilinearMap.map_sum]; exact sum_congr rfl fun j _=>ContinuousMultilinearMap.map_smul_univ ..
-- color invariance: origin coin derivative enough
end YM.CF.Rel
