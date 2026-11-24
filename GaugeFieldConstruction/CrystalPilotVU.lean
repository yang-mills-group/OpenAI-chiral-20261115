/- This file incorporates modified third-party source. See the source attributions in notices/. -/ -- Adapted from submitted project YM.Next.ROTATIONS and the indicated GaugeFieldConstruction/M modules, all-width (NONSEQUENCE) estimates
import GaugeFieldConstruction.StyriaRel.YM.Next.ROTATIONS.Nodal
import GaugeFieldConstruction.CrystalTonesVU
/-! # Full-width companion to EXP budget -/
set_option autoImplicit false
noncomputable section
namespace YM.NSF.Outer
open Set Filter Function MeasureTheory Measure Row Nodes OS Word Complex Boundary Probe
open scoped Topology ContDiff BigOperators NNReal ENNReal
private lemma price_creditAllRC (b : Bool) (m j k : ℕ) (s x : ℝ) (hx : x≤0) (f : Profile) : BudgetAllRC 0
    (fun n => credits m j k s (if b then pump 1 (billAllRC x n f) else billAllRC x n f)) := by
  cases b
  case false =>
    refine (credit_budgetAllRC m j k s f x 0).rise ?_ |>.same (Eventually.of_forall fun i => ?_)
    · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    change credits _ _ _ (_*_) _ = _; rw [fuel0AllRC,mul_one]; rfl
  case true =>
    have ht := credit_budgetAllRC m j k s (pump 1 f) x 0
    refine ((budget_fuelAllRC x).prod ht).rise ?_ |>.same (Eventually.of_forall fun i => ?_)
    · apply add_nonpos hx (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))
    dsimp only [billAllRC]
    rw [fuel0AllRC,mul_one, pump_width,pow_one]; simp [credits]; ring
lemma baked_budgetAllRC (δ : ℝ) (m : ℕ) (b : Bool) (s x : ℝ) (hx : x≤0) (Y : ℝ≥0 → Profile→ₗ[ℝ] ℂ) (f : Profile)
    (hh : ∀ g : Profile, Far g → BudgetAllRC δ (fun n => Y n g)) : BudgetAllRC δ (fun n => Y n (Cakes b m s (billAllRC x n f))) := by
  let A (j k : ℕ) := width s (menu j k)
  have ha (j k : ℕ) := (show Far (A j k) from (menu_far ..).width _)
  let F (n : ℝ≥0) := if b then pump 1 (billAllRC x n f) else billAllRC x n f
  let L (n j k) := credits m j k s (F n)
  let W (j k) := if b then slash 1 (A j k) else A j k
  have hz (j k : ℕ) : Far (W j k) := by unfold W; split_ifs; exact slash_far (ha j k) _; exact ha j k
  have ht n : Cakes b m s (billAllRC x n f)= ∑ j∈Finset.range m, ∑ k∈dish m j,L n j k • W j k := by
    cases b
    · rfl
    ext p
    simp only [Cakes, ↓reduceIte, OddB,slash_at (bake_far m s _)]; unfold bake board
    simp only [W,A,F,L, ↓reduceIte, _root_.sum_apply, Finset.mul_sum,_root_.smul_apply,
      slash_at (show Far (width s (menu _ _)) from ha _ _)]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [smul_eq_mul]; ring
  simp_rw [ht,_root_.map_sum,map_smul]
  refine budget_sumAllRC _ (fun j n => _) _ fun j h => budget_sumAllRC _ (fun i n => _) _ fun k hK => ?_
  have hC : BudgetAllRC 0 (fun n => (L n j k:ℂ)) := by
    apply BudgetAllRC.reduce (X:=ℝ) (f:=fun n => L n j k) (price_creditAllRC b m j k s x hx f) (Eventually.of_forall fun n => le_of_eq (Complex.norm_real _))
  simpa only [zero_add,Complex.real_smul] using (show BudgetAllRC (0+δ) _ from hC.prod (hh (W j k) (hz j k)))

lemma bill_zeroAllRC (n : ℝ≥0) (f : Profile) : billAllRC 0 n f=f := by ext; simp [billAllRC,fuel0AllRC,width_at]

variable {G : Gauge} {L : Register G} {S : Table L} (V : ∀ i,Chamber S i)
include V
lemma fix_costAllRC (H : S.Hierarchy) (i : Axis) (B A : Weight L) (e e')
    (hi : Mixed Finset.univ e) (hj : Mixed Finset.univ e') (hb : ∀ i, Own B i (e i)) (ha : ∀ i, Own A i (e' i))
    (hB : ∀ i, Pressed i B) (hA : ∀ i, Pressed i A) (Z : Grouping → ℂ) (hZ : LinearTest Z)
    (ε : Axis→Bool) (he : ∀ j, signValue (ε j)=signValue (e j)*signValue (e' j))
    (δ : ℝ) (hd : 0<δ) (F F' : Profile) (hF' : Ends F')
    (c : ℂ) (D : ℕ) (C : ∀ (g : Grouping), (∀ j, Ends (g j)) → g i=F → ∀ j : Axis,j≠i → Centred D (g j) →
      Z g = c*(∫ x,mixPlot S B A (update g i F') x))
    (T : Finset Axis) (hT : i∉T) (w : Axis→ℝ) (hw : ∀ i,w i ≤ 0) (hr : ∀ i,i ∉ T → w i=0)
    (f : Grouping) (hf : ∀ j, Ends (f j)) (hu : ∀ j∈T,Reflects (ε j) (f j)) (hl : f i=F) :
    BudgetAllRC δ (fun n => Z (mailsAllRC w f n)) := by
  classical
  induction T using Finset.induction_on generalizing w f with
  | empty =>
    have he n : mailsAllRC w f n=f := by ext1 x; unfold mailsAllRC; rw [hr _ (by simp),bill_zeroAllRC]
    simp_rw [he]; exact (constant_budgetAllRC (Z f)).rise hd.le
  | @insert j T h ih =>
    have hij : i≠j := fun hk => hT (by simp [hk])
    let g := update f i F'
    have hg : ∀ k, Ends (g k) := by
      intro k; by_cases hk : k=i
      · subst k; rw [show g i=F' from update_self ..]; exact hF'
      rw [show g k=f k from update_of_ne hk ..]; exact hf k
    have hz n : mailsAllRC w g n = update (mailsAllRC w f n) i F' := by
      ext1 x; unfold mailsAllRC
      by_cases he : x=i
      · subst x; simp [g,hr i hT,bill_zeroAllRC]
      simp [he,g]
    have hl' n : mailsAllRC w f n i=F := by unfold mailsAllRC; rw [hr _ hT,bill_zeroAllRC,hl]
    have hy := hu j (by simp)
    obtain ⟨s,M,hs,hM⟩ := one_modeAllRC V H j B A e e' hi hj hb ha hB hA w hw (ε j) (he j) g hg
      (show Reflects (ε j) (g j) from by simpa [g,hij.symm] using hy) δ hd
    let m := max M D
    let U n := GridTest (ε j) m s (mailsAllRC w f n j)
    choose Y hY using fun n => hZ j (mailsAllRC w f n)
    have hJ (n) : mailsAllRC w g n j=mailsAllRC w f n j := by rw [hz]; exact update_of_ne hij.symm ..
    have hbake (n) : Far (Cakes (ε j) m s (mailsAllRC w f n j)) := by unfold Cakes; split_ifs; exact OddB.far ..; exact bake_far ..
    have heq n : Z (update (mailsAllRC w f n) j (U n))= c*∫ x,mixPlot S B A (update (mailsAllRC w g n) j (GridTest (ε j) m s (mailsAllRC w g n j))) x := by
      rw [C _ ?_ ?_ j hij.symm ?_,hJ,hz, Function.update_comm hij.symm]
      · intro k; by_cases h : k=j
        · subst k; rw [update_self]; exact ((hf _).width _).sub (hbake n).1
        rw [update_of_ne h ..]; exact (hf _).width _
      · rw [update_of_ne hij ..,hl']
      rw [update_self]; exact fun v hh => vanish _ _ s _ (by linarith) ((hf _).width _) (hy.tall _) _ (by unfold m; omega)
    have hh := ((hM m (le_max_left ..)).2).times c
    have hb : BudgetAllRC δ (fun n => Y n (U n)) := hh.same (Eventually.of_forall fun n => by change _=Y n (U n); rw [hY,heq])
    have ht := baked_budgetAllRC δ m (ε j) s (w j) (hw j) Y (f j) (fun x hx => ?_)
    · refine (hb.add ht).same (Eventually.of_forall fun n => ?_)
      change Y n (_-_) + Y n _= _
      rw [map_sub]; change _-Y n _+Y n (Cakes (ε j) m s (mailsAllRC w f n j))=_
      rw [sub_add_cancel, hY, update_eq_self]
    let v := update w j 0
    let g := update f j x
    apply (ih (fun hv => hT (by simp [hv])) v ?cw ?ct g ?gc ?gt (show g i=F by simp [g,hij,hl])).same
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
    by_cases hk : k=j; · subst k; simp [g,v,mailsAllRC,bill_zeroAllRC]
    simp [g,v,mailsAllRC,hk]
end YM.NSF.Outer
