/- This file incorporates modified third-party source. See the source attributions in notices/. -/ -- Adapted from submitted project YM.Next.ROTATIONS and the indicated GaugeFieldConstruction/M modules, all-width (NONSEQUENCE) estimates
import GaugeFieldConstruction.StyriaRel.YM.Next.ROTATIONS.Mode
import GaugeFieldConstruction.CrystalRouteVU
/-! # Full-width companion to EXP budget -/
set_option autoImplicit false
noncomputable section
namespace YM.NSF.Outer
open MeasureTheory Measure Set Function Filter Metric Complex Boundary Probe Row Word OS
open scoped Topology NNReal ENNReal BigOperators ContDiff

variable {G : Gauge} {L : Register G} {S : Table L}
private lemma cross_runsAllRC (H : S.Hierarchy) (i : Axis) (V : Chamber S i) (B A : Weight L) (b a : Bool)
    (hB : Pressed i B) (hA : Pressed i A) : ∃ D : ℕ, ∀ g : Profile, Centred D g → ∀ j,
        Runs (ν V (combo B A j)) i (signValue b * signValue a) (stamp g) := by
  have he j : Pressed i (combo B A j) := by
    classical
    intro v hv; apply Or.elim (Finset.mem_union.mp (Finsupp.support_add hv))
    · exact hB v
    exact fun h => hA v (Finsupp.support_smul h)
  choose D h using fun j => runs_point V H _ (he j)
  refine ⟨∑ j,D j,fun g hp j => h j _ (centred_hollow g (D j) (fun k hk => hp k (hk.trans_le ?_))) _ ?_⟩
  · exact Finset.single_le_sum (f:=D) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  · cases b <;> cases a <;> simp [signValue]
variable (V : ∀ i, Chamber S i)

include V
/-- One-variable subtraction (per fixedAllRC transverse profiles, no uniform choice asserted).
Time-collision order requirements always may be raised after all tests are fixedAllRC. -/
lemma one_modeAllRC (H : S.Hierarchy) (i : Axis) (B A : Weight L) (e e')
    (hi : Mixed Finset.univ e) (hj : Mixed Finset.univ e') (hb : ∀ i, Own B i (e i)) (ha : ∀ i, Own A i (e' i))
    (hB : ∀ i, Pressed i B) (hA : ∀ i, Pressed i A) (w : Axis→ℝ) (hw : ∀ i,w i ≤ 0)
    (b : Bool) (hbb : signValue b=signValue (e i)*signValue (e' i))
    (f : Grouping) (hf : ∀ i, Ends (f i)) (ht : Reflects b (f i)) (δ : ℝ) (hd : 0<δ) :
    ∃ (s : ℝ) (M : ℕ),1≤s ∧ ∀ m≥M,
      let Z n := update (mailsAllRC w f n) i (GridTest b m s (mailsAllRC w f n i))
      (∀ n, Integrable (mixPlot S B A (Z n))) ∧
        BudgetAllRC δ (fun n => ∫ x,mixPlot S B A (Z n) x) := by
  obtain ⟨g,s,hg,hG,hT,hS,h⟩ := white (f i) b (hf i) ht
  let K (n j) := fuelAllRC (w j) n
  have hv n j : 0<K n j := fuel_posAllRC ..
  have hi' n j : K n j ≤ 1 := by simpa only [K,fuel0AllRC] using fuel_leAllRC (hw j) n
  choose F hF hp hh hup using fun j => major (f j) (hf j)
  let X := update F i g
  have he : Colors Finset.univ X := by
    intro j _; by_cases ht : j=i
    · subst j; simp only [X,update_self]; exact ⟨hg,hG,hT⟩
    rw [show X j=F j from update_of_ne ht ..]; exact ⟨hF j,hp j,hh j⟩
  let Y := mailsAllRC w X; let Q := mailsAllRC w f
  have hy n : Y n i=width (K n i) g := by unfold Y X mailsAllRC billAllRC; rw [update_self]
  obtain ⟨D,Hd⟩ := cross_runsAllRC H i (V i) B A (e i) (e' i) (hB i) (hA i)
  have hQ n : Room (mailsAllRC w X n i) (s*fuelAllRC 0 n) := by
    rw [show mailsAllRC w X n i= _ from hy n,fuel0AllRC,mul_one]; exact ((h 0).choose_spec.2 _ (hv ..) (hi' ..)).1
  obtain ⟨l,hL⟩ : ∃ l : ℕ, ∀ m≥l,(∀ n,Integrable (Reel i (Resid m s (Y n i))) (ν (V i) A) ∧ Integrable (Reel i (Resid m s (Y n i))) (ν (V i) B)) ∧
      BudgetAllRC δ (fun n => pay (ν (V i) A) i Finset.univ (Resid m s (Y n i)) (Y n)) ∧ BudgetAllRC δ (fun n => pay (ν (V i) B) i Finset.univ (Resid m s (Y n i)) (Y n)) := by
    obtain ⟨u,r,hr⟩ := walkAllRC V H Finset.univ e i (Finset.mem_univ _) hi B (fun j _ => hB j) (fun j _ => hb j) w (fun j _ => hw j) _ hd
    obtain ⟨t,ht,hy'⟩ := walkAllRC V H Finset.univ e' i (Finset.mem_univ _) hj A (fun j _ => hA j) (fun j _ => ha j) w (fun j _ => hw j) _ hd
    obtain ⟨D,h₀⟩ := hr 0 le_rfl r.le s hS X he (Eventually.of_forall hQ)
    obtain ⟨R,h₁⟩ := hy' 0 le_rfl ht.le s hS X he (Eventually.of_forall hQ)
    obtain ⟨M,hM⟩ := runs_order (V i) H A (hA i)
    obtain ⟨N,hN⟩ := runs_order (V i) H B (hB i)
    refine ⟨max D (max R (max M N)),fun m hm => ⟨fun n => ?_,?_,?_⟩⟩
    · rw [hy n]
      exact ⟨reel_int _ (hM m (by omega) s (by linarith) _ (hg.width _) (hT.tall _)),
        reel_int _ (hN m (by omega) s (by linarith) _ (hg.width _) (hT.tall _))⟩
    · simpa only [Y,lampsAllRC,mailsAllRC,fuel0AllRC,mul_one] using h₁ m (by omega)
    · simpa only [Y,lampsAllRC,mailsAllRC,fuel0AllRC,mul_one] using h₀ m (by omega)
  refine ⟨s,max l D,hS,fun m hm => ?_⟩
  obtain ⟨hmA,h₁,h₂⟩ := hL m (by omega)
  obtain ⟨C,hC,h⟩ := h m
  let T n := GridTest b m s (mailsAllRC w f n i)
  intro Z
  let W n j := stamp (Z n j)
  have Wt n : W n i=stamp (T n) := by simp [W,Z,T]
  let ξ n := answer i (signValue b) (W n)
  have hr n : Integrable (mixPlot S B A (Z n)) ∧ fits (V i) B A (ξ n) ∧ signValue (e i)*(∫ x,mixPlot S B A (Z n) x)=(toll:ℂ)*cross (V i) B A (ξ n) := by
    unfold ξ; rw [hbb]
    apply cross_slice (V i) H B A (hb i) (ha i) (W n) (allows_all B A i _ (hB i) (hA i))
    rw [Wt]; apply Hd
    refine fun j hj => vanish b m s _ (by linarith) ((hf i).width _) (ht.tall _) _ (by omega)
  let μ := ν (V i) A; let μ' := ν (V i) B
  let Fee (n) (p : E4) := C*(Reel i (Resid m s (Y n i)) p * crop (Finset.univ.erase i) (Y n) p)
  have hFo : BudgetAllRC δ (fun n => ∫ p,Fee n p ∂μ) := (h₁.times C).same (Eventually.of_forall fun n => by
    change _=(∫ p,Fee n p ∂μ); unfold Fee; rw [integral_const_mul];rfl)
  have hFu : BudgetAllRC δ (fun n => ∫ p,Fee n p ∂μ') := (h₂.times C).same (Eventually.of_forall fun n => by
    change _=(∫ p,Fee n p ∂μ'); unfold Fee; rw [integral_const_mul]; rfl)
  refine ⟨fun i => (hr i).1,?_⟩
  apply ((hFu.add hFo).times toll).priced
  refine Eventually.of_forall fun n => ?_
  have hN := (hr n).2.2
  have heq : ‖∫ x,mixPlot S B A (Z n) x‖=toll*‖cross (V i) B A (ξ n)‖ := by
    have hv := congr_arg norm hN
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg toll_pos.le, show ‖signValue (e i)‖=1 by cases e i <;> simp [signValue],one_mul] at hv; exact hv
  rw [heq]; apply mul_le_mul_of_nonneg_left _ toll_pos.le
  have hh := cross_le (V i) B A (ξ n) (hr n).2.1 (Fee n) (Fee n) ((crop_int (hmA n).2 _ _).const_mul C) ((crop_int (hmA n).1 _ _).const_mul C) ?HH 1 (by norm_num)
  · simpa only [one_mul,div_one] using hh
  case HH =>
    intro p hvp
    have hI : 0 ≤ Reel i (Resid m s (Y n i)) p := by rw [hy]; exact lamp_sign _ _ _ _ (by linarith) hvp (hg.width _) (hG.tall _ (hv ..).le) ((h _ (hv ..) (hi' ..)).1)
    have hX j : Plus (Y n j) := bill_plusAllRC (he _ (Finset.mem_univ j)).2.1 (w j) n
    have ht : 0≤Fee n p := mul_nonneg hC (mul_nonneg hI (crop_nonneg _ _ (fun j h => hX j) _))
    refine ⟨ht,ht,(sq_le_sq₀ (norm_nonneg _) ht).2 ?_ |>.trans_eq (pow_two _)⟩
    unfold ξ answer Fee
    rw [norm_mul,Wt n,crop_read i (Z n), Complex.norm_real,← mul_assoc]
    refine mul_le_mul ?_ ?_ (norm_nonneg _) (mul_nonneg hC hI)
    · rw [hy]; exact (h _ (hv ..) (hi' ..)).2 _ hvp
    · unfold crop
      rw [norm_prod]
      refine Finset.prod_le_prod (fun j _ => norm_nonneg _) fun j hh => ?_
      have hz : j ≠ i := (Finset.mem_erase.mp hh).1
      unfold Z; rw [update_of_ne hz ..]
      have hl : Y n j=billAllRC (w j) n (F j) := by unfold Y mailsAllRC; rw [show X j=F j from update_of_ne hz g F]
      rw [hl]; unfold mailsAllRC billAllRC; rw [width_at,width_at,norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr (fuel_posAllRC _ _).le)]
      exact mul_le_mul_of_nonneg_left (hup ..) (inv_nonneg.mpr (fuel_posAllRC ..).le)
end YM.NSF.Outer
