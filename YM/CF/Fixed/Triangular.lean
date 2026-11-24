import YM.CF.Fixed.Pivots
import Mathlib.MeasureTheory.Integral.Pi

/-!
Update successively. Key relative factor tracking lemma in gauge-fixed
variables but BEFORE gauge fixing. Includes the usually lost seam pivots.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 12000
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Fixed.Pivots
open Function Filter MeasureTheory Gauge Lattice Finset Wilson
open scoped Matrix.Norms.Frobenius BigOperators Topology ENNReal InnerProductSpace
section ind
variable {ι E:Type*}[DecidableEq ι][Fintype ι][MeasurableSpace E] (μ:Measure E)[SigmaFinite μ]
local notation "Q_" => Measure.pi (fun _:ι=>μ)
lemma update_preserve (i:ι) (h:(ι→E)→E) (p:Measurable h)(V:∀ f:ι→E,MeasurePreserving (fun z:E=>h (update f i z)) μ μ) :
    MeasurePreserving (fun f=>update f i (h f)) (Measure.pi (fun _:ι=>μ)) (Measure.pi (fun _:ι=>μ)) := by
  let F:=fun f=>update f i (h f); have he:Measurable F:= by
    apply measurable_pi_lambda; intro k; by_cases t:k=i
    · subst k; simpa [F] using p
    simpa [F, Function.update_of_ne t] using measurable_pi_apply k (X:=fun _=>E)
  refine ⟨he,?_⟩; ext s hs; change Measure.map F _ s = _
  let X:=s.indicator (1:(ι→E)→ℝ≥0∞); have hX:Measurable X:=measurable_const.indicator hs
  rw [← lintegral_indicator_one hs, ← lintegral_indicator_one hs]; change (∫⁻ x,X x∂Measure.map F _)=(∫⁻ x,X x∂_); rw [lintegral_map hX he]
  apply lintegral_eq_of_lmarginal_eq {i} (hX.comp he) hX
  rw [lmarginal_singleton,lmarginal_singleton]; funext x; change (∫⁻ z:E,X (update (update x i z) i (h (update x i z)))∂μ)=_
  simp_rw [update_idem]; let g:=fun z=>h (update x i z)
  let Y(z):=X (update x i z); have hY: Measurable Y:=hX.comp (by fun_prop)
  rw [← lintegral_map hY (V x).measurable,(V x).map_eq]

def batch (S:Finset ι) (h:ι→(ι→E)→E)(x:ι→E):ι→ E:=fun i=> if i∈ S then h i x else x i

lemma batch_preserves (S:Finset ι)(h:ι→(ι→E)→E)(p:∀ i∈ S,Measurable (h i))(Z:ι→ℕ)
    (E':∀ i∈ S,∀ j∈ S, Z j ≤ Z i→ i≠j →∀ u c,h j (update u i c)=h j u)
    (W:∀ i∈S, ∀ x : ι→ E, MeasurePreserving (fun z:E=> h i (update x i z)) μ μ) : MeasurePreserving (batch S h) (Q_) (Q_) := by
  induction S using strongInduction with
  | _ S ih=>
    by_cases g:S.Nonempty
    · obtain ⟨i,hi,c⟩:= exists_max_image S Z g; let T:= S.erase i; let k:=fun x=>update x i (h i x)
      have hT:T ⊆ S:=erase_subset ..; have h': T ⊂ S := erase_ssubset hi; have hQ:= ih T h' (fun j hj=>p j (hT hj)) (fun i hi j hj=> E' i (hT hi) j (hT hj)) (fun j hj=> W j (hT hj))
      rw [show batch S h= batch T h ∘ k from ?_]; swap
      · funext u j; unfold Function.comp batch; by_cases e:j=i
        · subst j; rw [if_neg (notMem_erase i S), if_pos hi]; unfold k; rw [update_self]
        by_cases g:j∈T; swap
        · rw [if_neg g, if_neg (fun q=>g (mem_erase.mpr ⟨e,q⟩))]; exact (update_of_ne e ..).symm
        rw [if_pos g,if_pos (hT g)]; exact (E' i hi j (hT g) (c j (hT g)) (Ne.symm e) ..).symm
      exact hQ.comp (update_preserve μ i _ (p i hi) (W i hi))
    rw [not_nonempty_iff_eq_empty.mp g]; rw [show batch ∅ h=id by funext x i; simp [batch]]; exact MeasurePreserving.id _
end ind

variable (G:Gauge){N:Side}
open scoped Pointwise -- tune
local notation "U_" => Wilson.prior G N

def toothMark (e: Link N) (U:Config G N) := if h:Active e then faceValue U (mark e h) else U e
lemma toothMark_cont (e:Link N): Continuous (toothMark G e):=by
  by_cases h:Active e; · unfold toothMark; simp only [dif_pos h]; unfold faceValue; fun_prop
  unfold toothMark; simp only [dif_neg h]; fun_prop
lemma toothMark_pivot (x:Site N)(j:Axis)(h:Active (x,j))(U:Config G N): MeasurePreserving (fun z=> toothMark G (x,j) (update U (x,j) z)) G.probHaar G.probHaar := by
  let i:=tooth (x,j) h; let y:=x-step i; let V(z:G.El):= update U (x,j) z; have hx:i≠j:= (tooth_spec _ h).1; have ht:y+step i=x:=sub_add_cancel ..; have he:y≠x:= fun s=> by have hx:originSum y+1=originSum x:= reduced x i (tooth_spec _ h).2.1; rw [s] at hx; omega
  have hv(z:G.El): faceValue (V z) (mark (x,j) h)=travel (V z) y (square (min i j) (max i j)):=by
    unfold faceValue; congr 1; change square (min j i) (max j i)=_; rw [min_comm j i,max_comm j i]
  unfold toothMark; simp only [dif_pos h]; change MeasurePreserving (fun z=>faceValue (V z) (mark (x,j) h)) _ _; simp_rw [hv]
  rcases lt_or_gt_of_ne hx with t|t
  · simp only [min_eq_left t.le,max_eq_right t.le]; simp_rw [square_formula G y (V _) i j]; rw [ht]; unfold V
    have h(z) : U (y,i)*z*(U (y+step j,i))⁻¹*(U (y,j))⁻¹=U (y,i)*z*((U (y+step j,i))⁻¹*(U (y,j))⁻¹):= mul_assoc ..
    simp only [update_self, update_of_ne (show (y,i) ≠ (x,j) from by simp [hx]),update_of_ne (show (y+step j,i)≠(x,j) from by simp [hx]),update_of_ne (show (y,j)≠(x,j) from by simp [he]), h]; exact G.preserve_two_sided ..
  simp only [min_eq_right t.le,max_eq_left t.le]; simp_rw [square_formula G y (V _) j i]; rw [ht]; unfold V
  simp only [update_self, update_of_ne (show (y,i) ≠ (x,j) from by simp [hx]),update_of_ne (show (y+step j,i)≠(x,j) from by simp [hx]),update_of_ne (show (y,j)≠(x,j) from by simp [he])]; exact (G.preserve_two_sided ..).comp G.preserve_inv

def markRead (U:Config G N): Config G N:= batch (pivots N) (fun t=> toothMark G t) U
lemma markRead_measure : MeasurePreserving (markRead G (N:=N)) U_ U_ := by
  apply batch_preserves G.probHaar (pivots N) _ (fun i _=>(toothMark_cont G i).measurable) (fun i=>originSum i.1)
  · intro i hi j hj e h u c
    have p:Active j:= (mem_filter.mp hj).2; unfold toothMark; rw [dif_pos p,dif_pos p]; apply face_unique; intro a ha; apply update_of_ne; intro g; rw [g] at ha; exact not_le_of_gt (behind j p i (mem_filter.mp hi).2 ha h) e
  rintro ⟨x,j⟩ hi U; exact toothMark_pivot G x j (mem_filter.mp hi).2 U

lemma integral_pivots (A: Finset (Link N))(f:(i:Link N)→G.El→ℝ) : (∫ x:Config G N, ∏ i∈A,f i (x i) ∂U_)=∏ i∈ A, (∫ s, f i s∂G.probHaar):=by
  let F(i:Link N):=if i∈A then f i else fun _=>1; have he : ∀ x:Config G N,(∏ i∈A,f i (x i))=(∏ i:Link N,F i (x i)):=by
    intro x; rw [←prod_subset (subset_univ A)]; · apply Finset.prod_congr rfl; intro k hk; unfold F; rw [if_pos hk]
    intro j _ g; unfold F; rw [if_neg g]
  simp_rw [he,prior, integral_fintype_prod_eq_prod]; rw [←prod_subset (subset_univ A)]
  · apply Finset.prod_congr rfl; intro i p; unfold F; simp_rw [if_pos p]
  intro i _ t; unfold F; simp [t]
lemma mark_integral (f : G.El→ℝ)(h:Continuous f) :
    (∫ x:Config G N, ∏ i∈pivots N,f (toothMark G i x)∂U_)=(∫ s,f s∂G.probHaar)^(pivots N).card:=by
  let A:=pivots N; let F(U:Config G N):=∏ i∈A,f (U i)
  have ht(x:Config G N): (∏ i∈pivots N,f (toothMark G i x))=F (markRead G x):=by apply prod_congr rfl; intro i h; unfold markRead batch; rw [if_pos h]
  have hf: Continuous F:= continuous_finsetProd _ fun i _=>h.comp (continuous_apply _)
  simp_rw [ht]; rw [← integral_map_of_stronglyMeasurable (markRead_measure G).measurable hf.stronglyMeasurable,(markRead_measure G).map_eq]; unfold F; rw [integral_pivots G A (fun _=>f),prod_const]

end YM.CF.Fixed.Pivots
