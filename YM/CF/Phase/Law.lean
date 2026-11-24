import YM.CF.Phase.Seeds

/-! Family probabilities. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Phase
open Cube Lat Lattice SU Fock Filter MeasureTheory Finset Function
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
variable (m B : Side)
section
variable {I : Type} [Fintype I] [DecidableEq I] (S : Finset I) (U : Skin m B) (f : I→ArrayF m) (r : I→Zone) (j : Row) (a : Index m) (x : Cue m)
lemma local_draw (y : Cue m) (g : ∀ b, Fits m b a→x b=y b) : draw m B S U f r j a x=draw m B S U f r j a y := by
  apply prod_congr rfl; intro i hi; apply fund_same; intro w hw; rcases hw with l|l
  · subst w; simp [capRow,g a (fits_id m a)]
  have H : Fits m w.1 a := l.1.1; simp [capRow,g w.1 H]
lemma price_local (y : Cue m) (g : ∀ b, Fits m b a→x b=y b) : priceW m B S U f r j a x=priceW m B S U f r j a y := by
  have he : limitW m B S U f r j a x=limitW m B S U f r j a y := by
    apply integral_congr_ae; apply Eventually.of_forall; intro w
    apply local_draw; intro i H; by_cases h:i=a <;> simp [update_of_ne,g i H,h]
  unfold priceW; rw [local_draw m B S U f r j a x y g,he]
lemma link_profile (k : S.card≤6) : Continuous (fun t:Skin m B×(I→ArrayF m)×Cue m=>rates m B S t.1 t.2.1 r j t.2.2) :=
  continuous_finsetProd _ fun i _=>price_cont m B S r j i k
lemma launched (g : S.card≤6) : ∫ x, rates m B S U f r j x ∂rains m=1 := by
  let F a := priceW m B S U f r j a
  have he (a : Index m) : Continuous (F a) := by
    let f₁ := fun x:Cue m=> (U,f,x)
    let K := fun t:Skin m B×(I→ArrayF m)× Cue m => priceW m B S t.1 t.2.1 r j a t.2.2
    change Continuous (K ∘ f₁); exact (show Continuous K from price_cont m B S r j a g).comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  refine Sample.dense_norm (μ:=cloud) univ F (degree m) he (fun i v=>price_integral m B S U f r j i v g) ?_
  intro i j' hl h v t; apply price_local m B S U f r j i (update v j' t) v; intro b H; by_cases hp : b=j'
  · subst b; have ht := (fits_degree H hl.symm); omega
  simp [update_of_ne hp]
lemma live_rate (k : S.card≤6) : 0 ≤ rates m B S U f r j x := prod_nonneg (fun i _=>price_pos m B S U f r j i x k)
lemma germ (k : S.card≤6) (h : 0<rates m B S U f r j x) (i : Index m) : 0<priceW m B S U f r j i x :=
  lt_of_le_of_ne (price_pos m B S U f r j i x k) (fun g=>h.ne' (prod_eq_zero (mem_univ i) g.symm))
lemma draw_g (k) : draw m B S (gauge k U) (fun i=>onF k (f i)) r j a (partner m B k x) = draw m B S U f r j a x := by
  apply prod_congr rfl; intro i _; unfold dry
  rw [show capRow (onF k (f i)) j (partner m B k x)=onF k (capRow (f i) j x) by
    funext v; unfold capRow onF partner; split <;> simp_all,fund_g]
lemma remits (k) : rates m B S (gauge k U) (fun i=>onF k (f i)) r j (partner m B k x)=rates m B S U f r j x := by
  apply prod_congr rfl; intro b _; unfold priceW; rw [draw_g]; unfold limitW; congr 1
  let v := k (address m B b)
  rw [← MeasurePreserving.integral_comp (drop_map v) (dropE v).measurableEmbedding] -- tune where
  apply integral_congr_ae; apply Eventually.of_forall; intro t
  change draw _ _ _ _ _ _ _ _ (update _ _ (scaledV v t))=_
  have hg : update (partner m B k x) b (scaledV v t)=partner m B k (update x b t) := by
    funext d; by_cases h:d=b
    · subst d; unfold partner; simp [v]
    unfold partner; simp [update_of_ne h]
  rw [hg]; exact draw_g m B S U f r j b (update x b t) k
end
-- simplify to base DAG: no need alternate field dependency. x represented by slot, dummy in limits must drop.
variable (U : Skin m B) (a : Index m) (x : Cue m)
def water := priceW m B (Finset.univ:Finset Unit) U (fun _=> slot m x) (fun _=>∅) 0 a x
def law := ∏ a, water m B U a x
lemma vacant_price (y : ArrayF m) : priceW m B (Finset.univ:Finset Unit) U (fun _=> y) (fun _=>∅) 0 a x=water m B U a x := by
  have ht (z:Cue m) : draw m B (Finset.univ:Finset Unit) U (fun _=>y) (fun _=>∅) 0 a z= draw m B (Finset.univ:Finset Unit) U (fun _=>slot m x) (fun _=>∅) 0 a z := by
    unfold draw; apply prod_congr rfl; intro i _; apply fund_same
    rintro w (g|g)
    · subst w; simp [capRow]
    have he : w.2=0 := by simpa using g.2
    simp [capRow,he]
  unfold water priceW limitW; rw [ht]; simp_rw [ht]
lemma law_base (s : ArrayF m) : rates m B (univ:Finset Unit) U (fun _=>s) (fun _=>∅) 0 x=law m B U x := by simp only [rates,vacant_price m B U _ x s,law]
lemma law_positive : 0 ≤ law m B U x := by rw [←law_base m B U x (slot m x)]; exact live_rate m B _ _ _ _ _ _ (by simp)
lemma law_cont : Continuous (fun t:Skin m B×Cue m=>law m B t.1 t.2) := by
  let f := Classical.arbitrary (ArrayF m)
  simp_rw [←law_base m B _ _ f]
  let F := fun t:Skin m B× Cue m=> (t.1,(fun _:Unit=>f),t.2)
  let H := fun t:Skin m B×(Unit→ArrayF m)×Cue m=>rates m B univ t.1 t.2.1 (fun _=>∅) 0 t.2.2
  change Continuous (H ∘ F)
  exact (show Continuous H from link_profile _ _ _ _ _ (by simp)).comp (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))
lemma rain_law : ∫ x, law m B U x ∂rains m=1 := by
  let f := Classical.arbitrary (ArrayF m)
  simp_rw [←law_base m B _ _ f]; exact launched _ _ _ U _ _ _ (by simp)
lemma law_g (k : Site (Domain m B)→E) : law m B (gauge k U) (partner m B k x)=law m B U x := by
  rw [←law_base m B U x (slot m x), ←law_base m B (gauge k U) (partner m B k x) (onF k (slot m x))]
  exact remits _ _ _ _ (fun _:Unit=>slot m x) _ _ x k
lemma law_ready (a : Spot m) (g : a.2=(0:Row)) (l : List (Ramp m)) (h : l∈permits m a {0}) (u : 0<law m B U x) :
    broad < rateF m B U (slot m x) a l := by
  let w := slot m x; rw [←law_base m B U x w] at u
  rcases a with ⟨a,j⟩; dsimp at g; subst j
  have he := germ m B univ U (fun _:Unit=>w) (fun _=>∅) 0 x (by simp) u a
  have hg := price_live m B univ U (fun _:Unit=>w) (fun _=>∅) 0 a x (by simp) he () (mem_univ _)
  unfold dry at hg; rw [insert_empty] at hg
  rw [show slot m x=capRow w 0 x by funext i; unfold capRow w slot; split <;> rfl]; exact pay m B U _ _ _ hg l h -- tune
lemma law_stock : tsupport (fun t:Skin m B×Cue m=>law m B t.1 t.2) ⊆ {t|ZeroF m B t.1 t.2} := by
  let f := fun t:Skin m B×Cue m=>law m B t.1 t.2
  intro t hx a h₁ l h₂
  have hC : Continuous (fun t:Skin m B×Cue m=>rateF m B t.1 (slot m t.2) a l) := by
    let H := fun t:Skin m B×Cue m=>(t.1,slot m t.2)
    let F := fun v : FlagU m B=>rateF m B v.1 v.2 a l
    change Continuous (F ∘ H); exact (show Continuous F from fee_cont ..).comp (continuous_fst.prodMk ((slot_cont m).comp continuous_snd))
  have hB : ∀ v∈support f, broad ≤ rateF m B v.1 (slot m v.2) a l := fun v hv=> (law_ready m B v.1 v.2 a (mem_singleton.mp h₁) l h₂ (lt_of_le_of_ne (law_positive m B v.1 v.2) (Ne.symm (show f v≠0 from hv)))).le
  exact broad_margin.trans_le (show broad≤rateF m B _ _ _ _ from closure_minimal hB (isClosed_le continuous_const hC) hx)
lemma law_rich (h : law m B U x≠0) : ZeroF m B U x := by
  intro a ha l hl; exact broad_margin.trans (law_ready m B U x a (mem_singleton.mp ha) l hl (lt_of_le_of_ne (law_positive m B U x) h.symm))
end YM.CF.Phase
