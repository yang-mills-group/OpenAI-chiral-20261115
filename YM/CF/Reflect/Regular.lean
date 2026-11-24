import YM.CF.Reflect.Analytic

/-! Nonzero finite denominators (simultaneously all volumes), not a claim on pressure. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.RP
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology BoundedContinuousFunction ComplexOrder
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset Reflect
attribute [local instance] opCStarAlgebra
variable {m B : Side} {c : Phase.Part m B} {A D d e β : ℝ} (β) {W : Scroll m B c} (H : ScaleK A D W) (g : Budget B e d)
lemma movable (m B) (c : Cue m) (h : 0<e) {Z : Type*} [Fintype Z] [DecidableEq Z] (R : E →* UNI Z) (p : Continuous (fun t:E=> (R t).val)) : ∀ᶠ t:Pack m B in 𝓝 ((1:Skin m B),c),PlaqBound R t.1 e := by
  let k : Skin m B := fun _=>1
  let w : Pack m B := (k,c)
  unfold PlaqBound; simp_rw [eventually_all]
  intro x i j _; let f := fun t:Pack m B=> ‖(R (travel t.1 x (square i j))).val-1‖
  have ht : Continuous f := (((p.comp (travel_cont x (square i j))).comp continuous_fst).sub continuous_const).norm
  have he : f w=0 := by
    rw [show f w= ‖(R (travel k x (square i j))).val-1‖ from rfl];
    have hk (x:Site (Domain m B)) (l:Walk) : travel k x l=1 := by
      induction l generalizing x with | nil=>rfl | cons i l ih => rw [travel,Step.read]; simp only [k,inv_one,ite_self,one_mul]; exact ih _ -- tune shadow
    rw [hk,map_one,show (1:UNI Z).val=1 from rfl,sub_self,norm_zero]
  filter_upwards [ht.continuousAt.eventually (gt_mem_nhds (he.trans_lt h))] with i hi; exact (show f i<e from hi).le
include H g
set_option maxHeartbeats 350000 in
lemma empty_pos (l : Foot m B) (h : 0<e) : rawE W e β 0 0 l (emptyF m B) ≠ 0 := by
  let F := net m B β; let Y := TallyR m B e β; let v := wheel m B
  have he x (hx:x∈Y) : amplitude W l β 0 0 (emptyF m B) x=(F x:ℂ) := by
    let C := pair m B x.1 x.2; let A := Model (CSide m B)
    have hm := tallyP (show x∈TallyR m B e β from hx)
    let s := upperP (CSide m B)
    have hk : inner ℂ (linearB (CSide m B)) (pairWave (n:=A) C)=1 := by
      rw [linearB,inner_smul_left,basis_inner]; change star (unitV (CSide m B))*pf C s=1
      rw [show pf C s=unitV _ from pf_free (grain _ _ _ _ _) (grain_unit g.1 hm.1 (show Verified m B margin x.1 _ {0} from hm.2) (stick_in _ (mem_singleton_self _))), scale_unit_self (unit_phase (CSide m B))]
    unfold amplitude; change (F x:ℂ)*Complex.exp _ * inner ℂ _ (acts (1*quant (n:=A) _) (pairWave C))= _; rw [grow]; simp only [Complex.ofReal_zero,neg_zero,zero_mul,Complex.exp_zero,mul_one,zero_smul,exp_zero,quant_one,one_mul,act_one,hk]
  have hp := tally_meas m B e β
  unfold rawE ratioR; rw [integral_indicator hp]
  have hl : ∫ x in Y, amplitude W l β 0 0 (emptyF m B) x ∂v=(↑(∫ x in Y,F x ∂v):ℂ) := by
    rw [←integral_complex_ofReal]; apply integral_congr_ae; filter_upwards [ae_restrict_mem hp] with x hx; exact he x hx
  rw [hl]
  norm_cast; rw [← integral_indicator hp]
  apply ne_of_gt
  letI : (barrow m B).IsOpenPosMeasure := by unfold barrow Sample.fares ux; infer_instance
  letI : (rains m).IsOpenPosMeasure := by unfold rains; infer_instance
  letI : v.IsOpenPosMeasure := by unfold v wheel; infer_instance
  have hI : Integrable F v := net_compact (net_cont ..)
  have hj : Set.Nonempty (interior (Function.support (Y.indicator F))) := by
    let k : Skin m B := fun _=>1
    obtain ⟨x,f⟩ : ∃ x, Phase.law m B k x≠0 := by by_contra! p; have ht := rain_law m B k; simp_rw [p,integral_zero] at ht; exact zero_ne_one ht
    let w : Pack m B := (k,x)
    refine ⟨w, mem_interior_iff_mem_nhds.mpr ?_⟩
    have hr : ∀ᶠ i:Pack m B in 𝓝 w, Guard i.1 e := by
      have he₁ : ∀ᶠ i:Pack m B in 𝓝 w, PlaqBound firstF i.1 e := movable m B x h _ (p:=SU.fund_cont)
      have he₂ : ∀ᶠ i:Pack m B in 𝓝 w, PlaqBound matter i.1 e := movable m B x h _ matter_cont
      exact he₁.and he₂
    have hf : F w ≠ 0 := mul_ne_zero f (Wilson.bare_pos (G:=SU.group) β k).ne'
    have hU : Continuous F := net_cont ..
    filter_upwards [hr,hU.continuousAt.eventually (eventually_ne_nhds hf)] with i l r
    have hk : i∈Y := ⟨l,r⟩; change Y.indicator F i≠0; rw [Set.indicator_of_mem hk]; exact r
  exact (integral_pos_iff_support_of_nonneg (fun i:Pack m B => Set.indicator_nonneg (fun x _=>net_pos x β) i) (hI.indicator hp)).mpr (lt_of_lt_of_le (IsOpen.measure_pos v isOpen_interior hj) (measure_mono interior_subset))
lemma certainly (l : Foot m B) (t k : ℝ) (p:0≤t) : 0 ≤ rawE W e β t k l (emptyF m B) := by
  let i : Axis := 0; let v := emptyF m B; let h : Site (More m) := 0
  have ht : OfferedF m B i v false := ⟨continuous_const,fun _=> Sector.one,fun _ _ _=>rfl⟩
  have he : squareR m B h l i v false=v := by
    funext x; unfold squareR fiscal
    let U := star (quantU (costarU m B h l i))
    change twist U ((1:ℂ) • (theta _ 1 *1))=1
    rw [theta_one,one_mul,one_smul]; rw [twist_formula,mul_one]; exact U.property.2
  change 0 ≤ rawE _ _ _ _ _ _ v; rw [←he]; exact displacement H g _ _ _ _ _ p _ _ ht -- tune implicit beta?
omit H g
lemma solid (f : ℝ → ℂ) (h : AnalyticOnNhd ℝ f Set.univ) (e : f 0≠0) : Dense {x | f x≠0} := by
  rw [dense_iff_inter_open]; intro s hs hN
  by_contra p
  obtain ⟨a,hA⟩ := hN
  have he : f =ᶠ[𝓝 a] 0 := by filter_upwards [hs.mem_nhds hA] with x hx; change f x=0; by_contra g; exact p ⟨x,hx,g⟩
  have ht := h.eq_of_eventuallyEq (g:=fun _=>0) analyticOnNhd_const he
  exact e (congr_fun ht 0)
lemma choose_price {I : Type*} [Countable I] (v : I→ℝ→ℂ) (h : ∀ i,AnalyticOnNhd ℝ (v i) Set.univ) (e : ∀ i,v i 0≠0) (a b : ℝ) (g : a<b) : ∃ p,a<p∧p<b ∧∀ i,v i p≠0 := by
  let X (i : I) := {x:ℝ | v i x ≠ 0}
  have he i : IsOpen (X i) := isOpen_ne_fun (continuousOn_univ.mp (h i|>.continuousOn)) continuous_const
  obtain ⟨x,l,f⟩ := (dense_iInter_of_isOpen he (fun t=> solid (v t) (h t) (e t))).inter_open_nonempty (Set.Ioo a b) isOpen_Ioo (Set.nonempty_Ioo.mpr g)
  exact ⟨x,l.1,l.2,Set.mem_iInter.mp f⟩ -- tune
lemma covered (B : Side) (u v d E β e : ℝ) (g : Budget B E d) (h : 0<E) (c : ∀ m,Foot m B) (W : ∀ m, Scroll m B (c m)) (q : ∀ m, ScaleK u v (W m)) (l : 0<e) : ∃ a:ℝ,1-e<a∧a<1∧∀ i:ℕ,∃ x:ℝ, i<x∧x<(i:ℝ)+1∧∀ m:Side,0< rawE (W m) E β x a (c m) (emptyF m B) := by
  let F (i : Side) (t a:ℝ) := rawE (W i) E β t a (c i) (emptyF i B)
  obtain ⟨a,z,w,G⟩ := choose_price (fun i=> F i 0) (fun i=>(analytic_f β (q i) g (c i)).1 _) (fun i=>empty_pos β (q i) g (c i) h) (1-e) 1 (by linarith)
  refine ⟨a,z,w,fun i=>?_⟩
  obtain ⟨t,v,p,s⟩ := choose_price (fun i t=> F i t a) (fun i=> (analytic_f β (q i) g (c i)).2 _) G (i:ℝ) ((i:ℝ)+1) (by linarith)
  exact ⟨t,v,p,fun j=>lt_of_le_of_ne (certainly β (q j) g _ _ _ ((Nat.cast_nonneg _).trans v.le)) (s j|>.symm)⟩
end YM.CF.RP
