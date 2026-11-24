/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import GaugeFieldConstruction.ValeJournalVU
/-!
 Product contact arguments on tested Schmidt papers. Additional specialized M4 complex extension on all four;
 msm along R=exp(n). Profiles with support selected fixed.To define premises on rational moments elliptical.
-/
set_option autoImplicit false
noncomputable section
namespace YM.NSF.Outer
open Function Set Filter MeasureTheory Measure Complex Boundary Probe Table Row Word OS Ward
open scoped Topology ContDiff BigOperators NNReal ENNReal InnerProductSpace Matrix.Norms.Frobenius Classical
-- contact healing along arbitrary costs; does not require parity on the paper itself
lemma projectDiffVU (P : Paper) (D:ℕ) (h:∀ f:Panels,∀ i,flat D (f i)→ P f=0) (f): P f=P (projections f D):=by
 let u (s:Finset Axis) (j:Axis):= if j∈s then collect D (f j) else f j
 have hu (s:Finset Axis): P f=P (u s):=by
    induction s using Finset.induction_on with
    | empty=> simp [u]
    | insert i s hi ih=>
       rw[ih]; let g:=u s
       have hl:g i=f i:=by simp[g,u,hi]
       let a:= f i-collect D (f i)
       have hp:P (update g i a)=0:=h _ i (by rw [update_self]; exact missed D (f i))
       unfold a at hp; rw[P.map_update_sub,sub_eq_zero] at hp
       have he: P g=P (update g i (f i)) := by rw [←hl,update_eq_self]
       change P g= _; rw [he,hp]; congr 1; ext1 j; by_cases k:j=i <;> simp [k,u,g]
 exact (hu Finset.univ).trans (by rw [show u Finset.univ=projections f D from funext fun j=>if_pos (Finset.mem_univ j)])
-- unqualified polynomial paper lift. (cf Next/ROTATIONS/Symbol lifted_cost)
lemma extendExpensesVU {f : Grouping} {w : Axis → ℝ} {D : ℕ} {T : Paper} (hw : ∀ i,w i ≤ 0)
    (hp : ∀ f: Panels,∀ i,flat D (f i)→T f=0) : Budget 0 (fun n => T (polar (mails w f n))) := by
  have he (g : Panels) : T g=∑ p∈ Fintype.piFinset (fun i : Axis => Finset.range D),
      (∏ j,iteratedDeriv (p j) (g j) 0)*T (formal p) := by
    conv_lhs=>rw [projectDiffVU T D hp g]
    unfold projections collect; rw [T.map_sum_finset (fun i j => _) (fun i => Finset.range D)]
    apply Finset.sum_congr rfl; intro p hp; exact T.map_smul_univ (fun j => _) (formal p)
  have hx (b : Axis → ℕ) (j : Axis) : Budget 0 (fun n => iteratedDeriv (b j) (polar (mails w f n) j) 0) := by
    have ht := (budget_fuel (w j)).pow (b j)
    have hr : Budget (w j*b j) (fun n => ((fuel (w j) n ^ b j:ℝ):ℂ)) := ht.reduce (Eventually.of_forall (fun n => le_of_eq (norm_real _)))
    refine ((hr.times ((-I)^b j * (tally (b j) (f j):ℂ))).rise (by nlinarith [hw j])).same <| .of_forall fun n => ?_
    change _=iteratedDeriv _ (hat (stamp (width (fuel _ n) _))) _
    rw [jet_at_origin,tally_width _ _ (fuel_pos ..)]; push_cast; ring
  have hl (b : Axis→ℕ) (s : Finset Axis) : Budget 0
      (fun n => ∏ j∈s, iteratedDeriv (b j) (polar (mails w f n) j) 0) := by
    induction s using Finset.induction_on with
    | empty => simpa using constant_budget (1:ℂ)
    | insert i s h ih => simp_rw [Finset.prod_insert h]; simpa using (hx b i).prod ih
  simp_rw [show ∀ n, T (polar (mails w f n))=_ from fun n => he (polar (mails w f n))]; refine budget_sum _ (fun b n => _) _ fun b _ => ?_
  have h:= (hl b Finset.univ).times (T (formal b))
  simp_rw[mul_comm _ (T (formal b))]; exact h
-- complex profile option on product Schwartz
noncomputable def imageJetVU (f:Form): Profile:= SchwartzMap.postcompCLM imCLM f
noncomputable def realJetVU (f:Form): Profile:=SchwartzMap.postcompCLM reCLM f
noncomputable abbrev cardJetVU (f : Form)(b:Bool):Profile:=if b then imageJetVU f else realJetVU f
noncomputable abbrev pieModeVU (b:Bool): ℂ:=if b then I else 1
lemma imageSplitVU (f:Form): f=(stamp (realJetVU f)) + I • (stamp (imageJetVU f)):=by
 ext1 t; change f t=_ + I*_ ; rw [mul_comm I]; exact (re_add_im (f t)).symm
lemma endCardVU (f:Form)(h:HasCompactSupport ⇑f)(b:Bool): Ends (cardJetVU f b):=by
 unfold cardJetVU; split_ifs
 · exact h.comp_left (show im (0:ℂ)=0 from rfl)
 exact h.comp_left (show re (0:ℂ)=0 from rfl)
lemma farCardVU (f:Form)(h:HasCompactSupport ⇑f)(hp: ⇑f=ᶠ[𝓝 0] fun _=>0)(b:Bool): Far (cardJetVU f b):=by
 refine ⟨endCardVU f h b,?_⟩; filter_upwards [hp] with t ht; unfold cardJetVU; split_ifs
 · change (f t).im=0; rw [ht]; rfl
 change (f t).re=0; rw [ht]; rfl
noncomputable abbrev ComplexWidthVU (v:ℝ)(f:Form): Form:= ∑ b:Bool,pieModeVU b • stamp (width v (cardJetVU f b))
lemma complexWidthAtVU (v:ℝ)(f:Form)(t): ComplexWidthVU v f t= v⁻¹ • f (t/v):=by
 -- tune
 unfold ComplexWidthVU; simp only [_root_.add_apply,_root_.smul_apply, stamp_at, width_at, ↓reduceIte,Bool.false_eq_true, Fintype.sum_bool,cardJetVU,pieModeVU];
 rw [Complex.real_smul]; simp only [ofReal_mul]; change _=(v⁻¹:ℝ) * f (t/v)
 change I * ((v⁻¹:ℝ) * ((f (t/v)).im:ℂ)) + 1 * ((v⁻¹:ℝ) * ((f (t/v)).re:ℂ)) = _; conv_rhs => rw [←re_add_im (f (t/v))]
 ring
noncomputable abbrev GroupsJetVU (f: Panels)(w:Axis→ℝ)(n:ℕ): Panels:=fun j=> hat (ComplexWidthVU (fuel (w j) n) (f j))
noncomputable abbrev ModeListVUX:= Fintype.piFinset (fun _: Axis=> Finset.univ (α:=Bool))
lemma ComplexWordBudgetVU (w: Axis→ℝ)(f:Panels) (P:Paper)(δ:ℝ)
    (h:∀ c: Axis→Bool, Budget δ (fun n=> sent P (mails w (fun i=>cardJetVU (f i) (c i)) n))):
    Budget δ (fun n=> P (GroupsJetVU f w n)):=by
 let d (b: Axis→Bool) n:= sent P (mails w (fun i=>cardJetVU (f i) (b i)) n)
 let r (b:Axis→Bool):=∏ i,pieModeVU (b i)
 have hp n:P (GroupsJetVU f w n)= ∑ b∈ModeListVUX,r b*d b n := by
    unfold GroupsJetVU ComplexWidthVU; simp_rw [_root_.map_sum,map_smul]
    rw [P.map_sum_finset (fun (j:Axis) x=>_) (fun _=>Finset.univ (α:=Bool))] -- tune
    apply Finset.sum_congr rfl; intro b _
    exact P.map_smul_univ (fun j=>pieModeVU (b j)) (polar (mails w (fun i=>cardJetVU (f i) (b i)) n))
 simp_rw [hp]; exact budget_sum _ (fun b n=>r b * d b n) _ (fun b _=>(h b).times _)
lemma axisTunedVU (w: Axis→ℝ)(P : Paper) (D:ℕ)(h:∀ f:Panels,∀ i,flat D (f i)→P f=0) (hw:∀ i,w i≤0) (f:Panels):Budget 0 (fun n=>P (GroupsJetVU f w n)):= ComplexWordBudgetVU w f P 0 (fun i=>extendExpensesVU hw h)
variable {G : Gauge}{L:Register G}{S:Table L}
lemma PureSavingsVU (V : ∀ i,Chamber S i) (H : S.Hierarchy) (B A : Weight L) (e e')
    (hi : Mixed Finset.univ e) (hj : Mixed Finset.univ e') (hb : ∀ i, Own B i (e i)) (ha : ∀ i, Own A i (e' i))
    (hB : ∀ i, Pressed i B) (hA : ∀ i, Pressed i A) (D : ℕ) (q:E4→ℂ)(hq:Measurable q)(h:∀ x,x≠0→ q x=readsCluster S B A x)(P:ScaleCap D q)(Z:Paper)
    (hE: ∀ f:Panels,∀ i,flat D (f i)→ Z f =∫ x,q x * tensor f x)
    (δ : ℝ) (hd : 0<δ) (w : Axis→ℝ) (hw : ∀ i,w i ≤ 0) (f : Panels) (hf : ∀ j, HasCompactSupport ⇑(f j)): Budget δ (fun n=>Z (GroupsJetVU f w n)) :=by
 let T:= article q D P hq
 have hu:Budget δ (fun n=> T (GroupsJetVU f w n)):= ComplexWordBudgetVU w f T _ (fun b=>PhotoBudgetVU V H B A e e' hi hj hb ha hB hA D q hq h P δ hd w hw _ (fun i=>endCardVU _ (hf i) _))
 refine (((axisTunedVU w (Z-T) D ?_ hw f).rise hd.le).add hu).same (Eventually.of_forall fun n=>?_)
 · intro g i hv; change Z g-T g=0; rw [hE _ _ hv,show T g = _ from article_test g i hv,sub_self]
 change Z _ - T _ + T _ = _; rw [sub_add_cancel]
lemma MainFixedVU (V : ∀ i,Chamber S i) (H : S.Hierarchy) (P : DiffPlan S) (hp : P.Derivatives S) (ho : P.Orientation H.spin)
    (J : Stress S) (C : Conserved P H.spin J) (Y : RawTensor H.spin J) {D : ℕ}
    {R: Series} (h:Portrait J D R)(a b c d i: Axis)(T:Paper) (hE: ∀ f:Panels,∀ i,flat D (f i)→ T f= ∫ x,linePair J a b c d x * tensor f x)(f : Panels)
    (hf : ∀ j,HasCompactSupport ⇑(f j)) (hF : ⇑(f i)=ᶠ[𝓝 0] fun _ => 0)
    (w : Axis → ℝ) (he : w i=0) (hw : ∀ i,w i ≤ 0) (δ : ℝ) (hδ : 0<δ) : Budget δ (fun n=> T (GroupsJetVU f w n)):=by
 let L:= R a b c d
 have hu:= ComplexWordBudgetVU w f L δ (fun j=>portraitFixedVU V H P hp ho J C Y h a b c d i (fun u=>cardJetVU (f u) (j u)) (farCardVU _ (hf i) hF _) (fun i=>endCardVU _ (hf i) _) w he hw δ hδ)
 refine (((axisTunedVU w (T-L) D ?_ hw f).rise hδ.le).add hu).same (Eventually.of_forall fun n=>?_)
 · intro g i hv; change T g-L g=0; rw [hE _ _ hv,show L g=_ from h.agrees _ _ _ _ g i hv,sub_self]
 change T _- L _ + L _ = _; rw[sub_add_cancel]
#print axioms PureSavingsVU
#print axioms MainFixedVU
end YM.NSF.Outer
end
