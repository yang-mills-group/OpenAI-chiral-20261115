/- This file incorporates modified third-party source. See the source attributions in notices/. -/ -- Adapted from submitted project YM.Next.ROTATIONS and the indicated GaugeFieldConstruction/M modules, all-width (NONSEQUENCE) estimates
import GaugeFieldConstruction.EisJournalVU
import GaugeFieldConstruction.CrystalSagaVU
/-! # Full-width companion to EXP budget -/
set_option autoImplicit false
noncomputable section
namespace YM.NSF.Outer
open Function Set Filter MeasureTheory Measure Complex Boundary Probe Table Row Word OS Ward
open scoped Topology ContDiff BigOperators NNReal ENNReal InnerProductSpace Matrix.Norms.Frobenius Classical
lemma extendExpensesAllRC {f : Grouping} {w : Axis → ℝ} {D : ℕ} {T : Paper} (hw : ∀ i,w i ≤ 0)
    (hp : ∀ f: Panels,∀ i,flat D (f i)→T f=0) : BudgetAllRC 0 (fun n => T (polar (mailsAllRC w f n))) := by
  have he (g : Panels) : T g=∑ p∈ Fintype.piFinset (fun i : Axis => Finset.range D),
      (∏ j,iteratedDeriv (p j) (g j) 0)*T (formal p) := by
    conv_lhs=>rw [projectDiffVU T D hp g]
    unfold projections collect; rw [T.map_sum_finset (fun i j => _) (fun i => Finset.range D)]
    apply Finset.sum_congr rfl; intro p hp; exact T.map_smul_univ (fun j => _) (formal p)
  have hx (b : Axis → ℕ) (j : Axis) : BudgetAllRC 0 (fun n => iteratedDeriv (b j) (polar (mailsAllRC w f n) j) 0) := by
    have ht := (budget_fuelAllRC (w j)).pow (b j)
    have hr : BudgetAllRC (w j*b j) (fun n => ((fuelAllRC (w j) n ^ b j:ℝ):ℂ)) := ht.reduce (Eventually.of_forall (fun n => le_of_eq (norm_real _)))
    refine ((hr.times ((-I)^b j * (tally (b j) (f j):ℂ))).rise (by nlinarith [hw j])).same <| .of_forall fun n => ?_
    change _=iteratedDeriv _ (hat (stamp (width (fuelAllRC _ n) _))) _
    rw [jet_at_origin,tally_width _ _ (fuel_posAllRC ..)]; push_cast; ring
  have hl (b : Axis→ℕ) (s : Finset Axis) : BudgetAllRC 0
      (fun n => ∏ j∈s, iteratedDeriv (b j) (polar (mailsAllRC w f n) j) 0) := by
    induction s using Finset.induction_on with
    | empty => simpa using constant_budgetAllRC (1:ℂ)
    | insert i s h ih => simp_rw [Finset.prod_insert h]; simpa using (hx b i).prod ih
  simp_rw [show ∀ n, T (polar (mailsAllRC w f n))=_ from fun n => he (polar (mailsAllRC w f n))]; refine budget_sumAllRC _ (fun b n => _) _ fun b _ => ?_
  have h:= (hl b Finset.univ).times (T (formal b))
  simp_rw[mul_comm _ (T (formal b))]; exact h
noncomputable abbrev GroupsJetAllRC (f: Panels)(w:Axis→ℝ)(n:ℝ≥0): Panels:=fun j=> hat (ComplexWidthVU (fuelAllRC (w j) n) (f j))
lemma ComplexWordBudgetAllRC (w: Axis→ℝ)(f:Panels) (P:Paper)(δ:ℝ)
    (h:∀ c: Axis→Bool, BudgetAllRC δ (fun n=> sent P (mailsAllRC w (fun i=>cardJetVU (f i) (c i)) n))):
    BudgetAllRC δ (fun n=> P (GroupsJetAllRC f w n)):=by
 let d (b: Axis→Bool) n:= sent P (mailsAllRC w (fun i=>cardJetVU (f i) (b i)) n)
 let r (b:Axis→Bool):=∏ i,pieModeVU (b i)
 have hp n:P (GroupsJetAllRC f w n)= ∑ b∈ModeListVUX,r b*d b n := by
    unfold GroupsJetAllRC ComplexWidthVU; simp_rw [_root_.map_sum,map_smul]
    rw [P.map_sum_finset (fun (j:Axis) x=>_) (fun _=>Finset.univ (α:=Bool))] -- tune
    apply Finset.sum_congr rfl; intro b _
    exact P.map_smul_univ (fun j=>pieModeVU (b j)) (polar (mailsAllRC w (fun i=>cardJetVU (f i) (b i)) n))
 simp_rw [hp]; exact budget_sumAllRC _ (fun b n=>r b * d b n) _ (fun b _=>(h b).times _)
lemma axisTunedAllRC (w: Axis→ℝ)(P : Paper) (D:ℕ)(h:∀ f:Panels,∀ i,flat D (f i)→P f=0) (hw:∀ i,w i≤0) (f:Panels):BudgetAllRC 0 (fun n=>P (GroupsJetAllRC f w n)):= ComplexWordBudgetAllRC w f P 0 (fun i=>extendExpensesAllRC hw h)
variable {G : Gauge}{L:Register G}{S:Table L}
lemma PureSavingsAllRC (V : ∀ i,Chamber S i) (H : S.Hierarchy) (B A : Weight L) (e e')
    (hi : Mixed Finset.univ e) (hj : Mixed Finset.univ e') (hb : ∀ i, Own B i (e i)) (ha : ∀ i, Own A i (e' i))
    (hB : ∀ i, Pressed i B) (hA : ∀ i, Pressed i A) (D : ℕ) (q:E4→ℂ)(hq:Measurable q)(h:∀ x,x≠0→ q x=readsCluster S B A x)(P:ScaleCap D q)(Z:Paper)
    (hE: ∀ f:Panels,∀ i,flat D (f i)→ Z f =∫ x,q x * tensor f x)
    (δ : ℝ) (hd : 0<δ) (w : Axis→ℝ) (hw : ∀ i,w i ≤ 0) (f : Panels) (hf : ∀ j, HasCompactSupport ⇑(f j)): BudgetAllRC δ (fun n=>Z (GroupsJetAllRC f w n)) :=by
 let T:= article q D P hq
 have hu:BudgetAllRC δ (fun n=> T (GroupsJetAllRC f w n)):= ComplexWordBudgetAllRC w f T _ (fun b=>PhotoBudgetAllRC V H B A e e' hi hj hb ha hB hA D q hq h P δ hd w hw _ (fun i=>endCardVU _ (hf i) _))
 refine (((axisTunedAllRC w (Z-T) D ?_ hw f).rise hd.le).add hu).same (Eventually.of_forall fun n=>?_)
 · intro g i hv; change Z g-T g=0; rw [hE _ _ hv,show T g = _ from article_test g i hv,sub_self]
 change Z _ - T _ + T _ = _; rw [sub_add_cancel]
lemma MainFixedAllRC (V : ∀ i,Chamber S i) (H : S.Hierarchy) (P : DiffPlan S) (hp : P.Derivatives S) (ho : P.Orientation H.spin)
    (J : Stress S) (C : Conserved P H.spin J) (Y : RawTensor H.spin J) {D : ℕ}
    {R: Series} (h:Portrait J D R)(a b c d i: Axis)(T:Paper) (hE: ∀ f:Panels,∀ i,flat D (f i)→ T f= ∫ x,linePair J a b c d x * tensor f x)(f : Panels)
    (hf : ∀ j,HasCompactSupport ⇑(f j)) (hF : ⇑(f i)=ᶠ[𝓝 0] fun _ => 0)
    (w : Axis → ℝ) (he : w i=0) (hw : ∀ i,w i ≤ 0) (δ : ℝ) (hδ : 0<δ) : BudgetAllRC δ (fun n=> T (GroupsJetAllRC f w n)):=by
 let L:= R a b c d
 have hu:= ComplexWordBudgetAllRC w f L δ (fun j=>portraitFixedAllRC V H P hp ho J C Y h a b c d i (fun u=>cardJetVU (f u) (j u)) (farCardVU _ (hf i) hF _) (fun i=>endCardVU _ (hf i) _) w he hw δ hδ)
 refine (((axisTunedAllRC w (T-L) D ?_ hw f).rise hδ.le).add hu).same (Eventually.of_forall fun n=>?_)
 · intro g i hv; change T g-L g=0; rw [hE _ _ hv,show L g=_ from h.agrees _ _ _ _ g i hv,sub_self]
 change T _- L _ + L _ = _; rw[sub_add_cancel]
#print axioms PureSavingsAllRC
#print axioms MainFixedAllRC
end YM.NSF.Outer
end
