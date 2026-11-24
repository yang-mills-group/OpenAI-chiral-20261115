/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import GaugeFieldConstruction.ΜiraJournalVU
/-! Extra M4 #122 on R=e^n, on product tests (multilinear paper only); no contour contact assumptions.
Variant constructs a product-Taylor subtraction, including the case fixed s in comparison to such arbitrary-parity
budget in the Signed-compatible extension. -/
set_option autoImplicit false
noncomputable section
namespace YM.NSF.Outer
open Function Set Filter MeasureTheory Measure Complex Boundary Probe Table Row Word OS Ward
open scoped Topology ContDiff BigOperators NNReal ENNReal InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {L : Register G} {S : Table L}
-- stage induct from project Next/ROTATIONS/Nodal (no axis fixed)
lemma mixedSelVU (V : ∀ i,Chamber S i) (H : S.Hierarchy) (B A : Weight L) (e e')
    (hi : Mixed Finset.univ e) (hj : Mixed Finset.univ e') (hb : ∀ i, Own B i (e i)) (ha : ∀ i, Own A i (e' i))
    (hB : ∀ i, Pressed i B) (hA : ∀ i, Pressed i A) (Z : Grouping → ℂ) (hZ : LinearTest Z)
    (ε : Axis→Bool) (he : ∀ j, signValue (ε j)=signValue (e j)*signValue (e' j))
    (δ : ℝ) (hd : 0<δ) (D : ℕ) (C : ∀ (g : Grouping), (∀ j, Ends (g j)) → ∀ j : Axis, Centred D (g j) →
      Z g = ∫ x,mixPlot S B A g x)
    (T : Finset Axis) (w : Axis→ℝ) (hw : ∀ i,w i ≤ 0) (hr : ∀ i,i ∉ T → w i=0)
    (f : Grouping) (hf : ∀ j, Ends (f j)) (hu : ∀ j∈T,Reflects (ε j) (f j)) : Budget δ (fun n => Z (mails w f n)) := by
  classical
  induction T using Finset.induction_on generalizing w f with
  | empty =>
    have he n : mails w f n=f := by ext1 x; unfold mails; rw [hr _ (by simp),bill_zero]
    simp_rw [he]; exact (constant_budget (Z f)).rise hd.le
  | @insert j T h ih =>
    have hy := hu j (by simp)
    obtain ⟨s,M,hs,hM⟩ := one_mode V H j B A e e' hi hj hb ha hB hA w hw (ε j) (he j) f hf hy δ hd
    let m := max M D
    let U n := GridTest (ε j) m s (mails w f n j)
    choose Y hY using fun n => hZ j (mails w f n)
    have hbake (n) : Far (Cakes (ε j) m s (mails w f n j)) := by unfold Cakes; split_ifs; exact OddB.far ..; exact bake_far ..
    have heq n : Z (update (mails w f n) j (U n))=∫ x,mixPlot S B A (update (mails w f n) j (U n)) x := by
      apply C _ _ j
      · rw [update_self]; exact fun v hh => vanish _ _ s _ (by linarith) ((hf _).width _) (hy.tall _) _ (by unfold m; omega)
      · intro k; by_cases h : k=j
        · subst k; rw [update_self]; exact ((hf _).width _).sub (hbake n).1
        rw [update_of_ne h ..]; exact (hf _).width _
    have hb : Budget δ (fun n => Y n (U n)) := ((hM m (le_max_left ..)).2).same (Eventually.of_forall fun n => Eq.symm ((hY n _).trans (heq n))) -- tune
    have ht := baked_budget δ m (ε j) s (w j) (hw j) Y (f j) (fun x hx => ?_)
    · refine (hb.add ht).same (Eventually.of_forall fun n => ?_)
      change Y n (_-_) + Y n _= _
      rw [map_sub]; change _-Y n _+Y n (Cakes (ε j) m s (mails w f n j))=_
      rw [sub_add_cancel, hY, update_eq_self]
    let v := update w j 0
    let g := update f j x
    apply (ih v ?cw ?ct g ?gc ?gt).same
    case cw =>
      intro k; by_cases ht : k=j; · simp [v,ht]
      simpa [v,ht] using hw k
    case ct =>
      intro k hk; by_cases hx : k=j; · simp [v,hx]
      simpa [v,hx] using hr k (by simp [hx,hk])
    case gc =>
      intro k; by_cases h : k=j; · subst k; simpa [g] using hx.1
      simpa [g,h] using hf k
    case gt =>
      intro k hk; have hp : k≠j := fun ht => h (ht ▸ hk)
      simpa [g,hp] using hu k (by simp [hk])
    refine Eventually.of_forall fun n => ?_
    change Z _= Y n x
    rw [hY]; congr 1; ext1 k
    by_cases hk : k=j; · subst k; simp [g,v,mails,bill_zero]
    simp [g,v,mails,hk]
-- tempered extension on product profiles, only tested prices not claiming extension continuity
lemma PhotoMixVU (V : ∀ i,Chamber S i) (H : S.Hierarchy) (B A : Weight L) (e e')
    (hi : Mixed Finset.univ e) (hj : Mixed Finset.univ e') (hb : ∀ i, Own B i (e i)) (ha : ∀ i, Own A i (e' i))
    (hB : ∀ i, Pressed i B) (hA : ∀ i, Pressed i A) (D : ℕ) (q:E4→ℂ)(hq:Measurable q)(h:∀ x,x≠0→ q x=readsCluster S B A x)(P:ScaleCap D q) (Z: Paper)
    (hE: ∀ f:Panels,∀ i,flat D (f i)→ Z f =∫ x,q x * tensor f x)
    (hp: ∀ f:Panels,∀ i:Axis,Z (moves (Signed.mirror i) f)= signValue (e i)*(signValue (e' i)*Z f))
    (δ : ℝ) (hd : 0<δ) (w : Axis→ℝ) (hw : ∀ i,w i ≤ 0) (f : Grouping) (hf : ∀ j, Ends (f j)):
      Budget δ (fun n=> sent Z (mails w f n)):=by
 let ε (j:Axis):= Bool.xor (e j) (e' j); let g:Grouping:=fun i=> modeSelVU (ε i) (f i)
 have he i : signValue (ε i)=signValue (e i)*signValue (e' i):=by cases hh:e i <;> cases hu:e' i <;> simp [signValue,ε,hh,hu]
 have heq (F:Grouping) (i: Axis)(hF: Centred D (F i)): sent Z F=∫ x,mixPlot S B A F x:=by
    rw [sent_at,hE _ _ (polar_flat F _ _ hF)]; apply integral_congr_ae; have hx: ∀ᵐ x : E4,x≠0:= by simp only [ae_iff]; simp
    filter_upwards [hx] with x hx; dsimp only [mixPlot]; rw [h _ hx]; rfl
 refine (mixedSelVU V H B A e e' hi hj hb ha hB hA (sent Z) (fun k u => ⟨(sent Z).toLinearMap u k,fun h => rfl⟩) ε he δ hd D (fun F _=> heq F) Finset.univ w hw (by simp) g (fun i=>modeEndsVU (hf i) _) (fun i _=>modeRefVU _ _)).same (Eventually.of_forall fun n=> Eq.symm (expenseSelectVU Z ε ?_ f w n))
 intro f i; rw [hp,he i,mul_assoc]
lemma PhotoBudgetVU (V : ∀ i,Chamber S i) (H : S.Hierarchy) (B A : Weight L) (e e')
    (hi : Mixed Finset.univ e) (hj : Mixed Finset.univ e') (hb : ∀ i, Own B i (e i)) (ha : ∀ i, Own A i (e' i))
    (hB : ∀ i, Pressed i B) (hA : ∀ i, Pressed i A) (D : ℕ) (q:E4→ℂ)(hq:Measurable q)(h:∀ x,x≠0→ q x=readsCluster S B A x)(P:ScaleCap D q)
    (δ : ℝ) (hd : 0<δ) (w : Axis→ℝ) (hw : ∀ i,w i ≤ 0) (f : Grouping) (hf : ∀ j, Ends (f j)):
      Budget δ (fun n=> sent (article q D P hq) (mails w f n)):=by
 refine PhotoMixVU V H B A e e' hi hj hb ha hB hA D q hq h P _ (fun f i=> article_test f i) ?_ δ hd w hw f hf
 intro f i
 let s:= Signed.mirror i; let Z:= s.ortho.motion
 change (∫ x,battle _ _ _ x)= _
 rw [← Z.measurePreserving.integral_comp Z.toHomeomorph.measurableEmbedding]
 change (∫ x,_)= _* (_*∫ x,battle _ _ _ x)
 rw[←integral_const_mul,←integral_const_mul]; have hh:∀ᵐ p:E4,p≠0:= by simp only [ae_iff]; simp
 refine integral_congr_ae (hh.mono fun x hx=>?_)
 dsimp only [battle,Z, Ortho.motion_at]
 rw [tensor_moves,moves_projections,tensor_moves,h _ (show Ortho.move s.ortho x≠0 by rw[← Ortho.motion_at]; exact fun H=>hx (Z.map_eq_zero_iff.mp H)),h x hx] -- tune
 rw[show s.ortho=Signed.reflect i from rfl,reads_mirror S H.spin i B A (e i) (e' i) (hb i) (ha i) x]; ring
#print axioms PhotoBudgetVU
end YM.NSF.Outer
end
