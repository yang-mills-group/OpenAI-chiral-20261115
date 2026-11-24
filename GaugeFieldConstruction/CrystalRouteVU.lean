/- This file incorporates modified third-party source. See the source attributions in notices/. -/ -- Adapted from submitted project YM.Next.ROTATIONS and the indicated GaugeFieldConstruction/M modules, all-width (NONSEQUENCE) estimates
import GaugeFieldConstruction.StyriaRel.YM.Next.ROTATIONS.Walk
import GaugeFieldConstruction.CrystalDialsVU
/-! # Full-width companion to EXP budget -/
set_option autoImplicit false
noncomputable section
namespace YM.NSF.Outer
open Set Function Filter MeasureTheory Measure Row Boundary Probe OS Word Nodes
open scoped Topology NNReal ENNReal ContDiff BigOperators
variable {G : Gauge} {L : Register G} {S : Table L} (V : ∀ i, Chamber S i)
def CanAllRC (A : Weight L) (Q U : Finset Axis) (δ K : ℝ) (i : Axis) :=
  ∃ a : ℝ, 0<a ∧ ∀ (d : ℝ), 0≤d → d≤a → ∀ w : Axis→ℝ,
    (∀ j∈Q,-K ≤ w j ∧ w j ≤ a) → w i ≤ d → (∀ j∈Q,j∉U → 0≤w j) →
    ∀ f : Grouping, Colors Q f → ∀ s : ℝ,1≤s →
    (∀ᶠ n in atTop, Room (mailsAllRC w f n i) (s*fuelAllRC d n)) → ∃ M : ℕ, ∀ m ≥ M,
      BudgetAllRC δ (fun n => pay (ν (V i) A) i Q (lampsAllRC m (w i) d s (f i) n) (mailsAllRC w f n))

private lemma tinyAllRC (D : ℕ) (δ b : ℝ) (hd : 0<δ) (hb : 0<b) : ∃ a : ℝ, 0<a ∧ a<b ∧ a*D < δ := by
  refine (Eventually.exists (p:=fun a => 0<a ∧ a<b ∧ a*D < δ) (f:=𝓝[>] (0:ℝ)) ?_)
  have he : Tendsto (fun x : ℝ => x*D) (𝓝[>] 0) (𝓝 0) := by
    simpa using (continuous_id.mul_const (D:ℝ)).continuousAt (x:=0) |>.continuousWithinAt (s:=Ioi 0) |>.tendsto
  filter_upwards [self_mem_nhdsWithin,(gt_mem_nhds hb).filter_mono (nhdsWithin_le_nhds (s:=Ioi 0)), he.eventually (gt_mem_nhds hd)] with a ha hu hv
  exact ⟨ha,hu,hv⟩
private lemma doneAllRC (H : S.Hierarchy) (Q : Finset Axis) (δ K) (hd : 0<δ) (i : Axis) (hi : i∈Q)
    (A : Weight L) (hp : Pressed i A) : CanAllRC V A Q ∅ δ K i := by
  obtain ⟨j,hj⟩ := exists_ne i
  obtain ⟨D,hD⟩ := accountsAllRC (V i) H A hp j hj 0
  obtain ⟨a,ha,ht,hδ⟩ := tinyAllRC D δ 1 hd zero_lt_one
  refine ⟨a,ha,fun d hz hk w hv hw hu f hh s hs hM => ?_⟩
  have Hx (j) (hi : j∈Q) : 0 ≤ w j := hu j hi (by simp)
  obtain ⟨hu,hl,hp⟩ := hh i hi
  refine ⟨D,fun m he => ?_⟩
  have he := hD (w i) d s hz hs _ hu hl hM m he
  simp only [Nat.mul_zero,pow_zero,mul_one] at he
  have h' : ∀ᶠ n in atTop, ∀ p : E4, 0≤p i → 0≤Reel i (lampsAllRC m (w i) d s (f i) n) p := hM.mono fun n hn p hi => lamp_signsAllRC _ _ _ _ (f i) hu hl n (by linarith) hn _ _ hi
  have h := done_payAllRC (V i) A _ Q f w h' Hx _ he.1 he.2
  apply h.rise
  exact max_le ((neg_nonpos.mpr (Hx _ hi)).trans hd.le) ((mul_le_mul_of_nonneg_right hk (by positivity)).trans hδ.le)

private lemma forwardsAllRC (H : S.Hierarchy) (Q U : Finset Axis) (δ K : ℝ) (hd : 0<δ) (hK : 0 ≤ K) (i j : Axis)
    (he : i∈Q) (hk : j∈Q) (hn : i≠j) (A : Weight L) (b c : Bool) (hbc : b≠c) (hi : Own A i b) (hj : Own A j c)
    (hp : Pressed i A) (hr : Pressed j A) (HH : CanAllRC V A Q (U.erase i) δ K j) :
    CanAllRC V A Q U δ K i := by
  obtain ⟨a',ha',HH⟩ := HH
  let R := (Q.erase i).erase j
  let p := K*R.card
  let z := max K δ
  obtain ⟨k,h⟩ := exists_nat_gt ((p+z)/a')
  obtain ⟨D,hD⟩ := accountsAllRC (V i) H A hp j (Ne.symm hn) k
  obtain ⟨a,ha,ht,hT⟩ := tinyAllRC D δ a' hd ha'
  obtain ⟨B,hB⟩ := runs_order (V i) H A hp
  refine ⟨a,ha,fun d hz hv w hL hW hU f hf s hs hF => ⟨max D B, fun m hM => ?_⟩⟩
  let X := lampsAllRC m (w i) d s (f i)
  obtain ⟨hu,ho,hY⟩ := hf i he
  obtain ⟨C,oH,oY⟩ := hf j hk
  have hM' := hD (w i) d s hz hs (f i) hu ho hF m (by omega)
  obtain ⟨g,hG,gp,gf,gm⟩ := paid_billAllRC m s hs (w i) d hW (f i)
  let L := update w i d
  let F := update f i g
  have hJ : F j=f j := update_of_ne hn.symm ..
  have hE : L j=w j := update_of_ne hn.symm ..
  have ht' (n) : mailsAllRC L F n = update (mailsAllRC w f n) i (billAllRC d n g) := by
    ext1 x; by_cases h : x=i; · subst x; simp [mailsAllRC,L,F]
    simp [mailsAllRC,L,F,h]
  have hp' (n) : mailsAllRC L F n j = mailsAllRC w f n j := by simp [mailsAllRC,hE,hJ]
  have co : Colors Q F := by
    intro l hl; by_cases h : l=i
    · subst l; simp only [F,update_self]; exact ⟨hG.1,gp,gf⟩
    rw [show F l=f l from update_of_ne h ..]; exact hf l hl
  have wh : w j < a' := lt_of_le_of_lt (hL j hk).2 ht
  have hQ : ∀ᶠ n in atTop, Room (mailsAllRC L F n j) ((1:ℝ)*fuelAllRC a' n) := by
    simp_rw [hp',one_mul]; exact mail_roomAllRC wh _ C
  have hh := HH a' ha'.le le_rfl L (by
    intro l hl; by_cases h : l=i
    · subst l; simp only [L,update_self]; exact ⟨(neg_nonpos.mpr hK).trans hz,hv.trans ht.le⟩
    rw [show L l=w l from update_of_ne h ..]; exact ⟨(hL l hl).1,(hL l hl).2.trans ht.le⟩) (hE ▸ wh.le)
    (fun l hl h => by
      by_cases H : l=i
      · subst l; simpa only [L,update_self] using hz
      rw [show L l=w l from update_of_ne H ..]; exact hU _ hl (fun hh => h (Finset.mem_erase.mpr ⟨H,hh⟩))) F co 1 le_rfl hQ
  obtain ⟨m',hh⟩ := hh
  obtain ⟨M,hR⟩ := runs_order (V j) H A hr
  let N := max m' M
  let Y := lampsAllRC N (w j) a' 1 (f j)
  have hy : BudgetAllRC δ (fun n => pay (ν (V j) A) j Q (Y n) (update (mailsAllRC w f n) i (billAllRC d n g))) := by
    have ht := hh N (le_max_left ..); simp_rw [hE,hJ,ht'] at ht; exact ht
  have hiM i : 1≤ fuelAllRC d i := by simpa only [fuel0AllRC] using fuel_leAllRC hz i
  have hu' (n) : 0 < s*fuelAllRC d n := by have := hiM n; positivity
  have hA (n) : 0<(1:ℝ)*fuelAllRC a' n := by simpa using fuel_posAllRC a' n
  have hX (n) : Runs (ν (V i) A) i 1 (stamp (X n)) := hB m (by omega) _ (hu' n) _ (hu.width _) (hY.tall _)
  have hd' (n) : Runs (ν (V j) A) j 1 (stamp (Y n)) := hR N (le_max_right ..) _ (hA n) _ (C.width _) (oY.tall _)
  obtain ⟨e,aO,hk',hb',hb⟩ := paid_billAllRC N 1 le_rfl (w j) a' wh.le (f j)
  have o : ∀ᶠ n in atTop, ∀ p : E4, 0≤p i → 0≤Reel i (X n) p := hF.mono fun n hn p hi => lamp_signsAllRC _ _ _ _ (f i) hu ho n (by linarith) hn _ _ hi
  have cost := far_payAllRC (V i) A X Q f w o K (fun l v => (hL l v).1) j hk hn.symm k _ hM'.1 hM'.2 e aO a' ha'.le
  have kO : BudgetAllRC δ (fun n => pay (ν (V i) A) i Q (X n) (update (mailsAllRC w f n) j (billAllRC a' n e))) := by
    refine cost.rise ?_
    have hz := (div_lt_iff₀ ha').1 h
    have hl : d*D ≤ z := ((mul_le_mul_of_nonneg_right hv (by positivity)).trans hT.le).trans (le_max_right ..)
    have o1 : -w i ≤ z := (by
      apply le_trans (b:=K) _ (le_max_left ..); linarith [(hL i he).1])
    have hu (n : ℕ) : a'*n ≤ a'*(2*n:ℕ) := by gcongr; omega
    change -a'* _+ p + _ ≤ _
    linarith [max_le o1 hl, hu k]
  apply (kO.add hy).signed
  · refine o.mono fun n hv => ?_
    exact pay_nonneg (V i) A (mailsAllRC w f n) _ _ hv fun l hh => bill_plusAllRC (hf _ (Finset.mem_of_mem_erase hh)).2.1 _ _
  filter_upwards [gm,hb,hQ,o] with n hx hh hq hh'
  let W := mailsAllRC w f n
  let P := bake m (s*fuelAllRC d n) (W i)
  let T := bake N ((1:ℝ)*fuelAllRC a' n) (W j)
  have wP (l) (hh : l∈Q) : Plus (W l) := bill_plusAllRC (hf l hh).2.1 _ _
  have hy' : ∀ p : E4, 0 ≤ p j → 0 ≤ Reel j (W j-T) p := by
    rw [hp' n] at hq
    exact lamp_signsAllRC _ _ _ _ _ C oH n zero_lt_one hq j
  have Hi : pay (ν (V i) A) i Q (W i-P) W ≤ pay (ν (V i) A) i Q (W i-P) (update W j T) + pay (ν (V j) A) j Q (W j-T) (update W i P) := alternate H i j _ _ A _ _ hi hj hn hbc Q W he hk P T (allows_all A A i _ hp hp) (allows_all A A j _ hr hr) (hX n) (hd' n) hy' wP
  apply Hi.trans
  exact add_le_add (pay_mono (V i) A W Q (W i-P) hh' wP _ _ (hX n) j hk hn.symm (fun x => (le_abs_self _).trans (hh x)))
    (pay_mono (V j) A W Q _ hy' wP P _ (hd' n) i he hn (fun x => (le_abs_self _).trans (hx x)))

theorem affordableAllRC (H : S.Hierarchy) (Q U : Finset Axis) (i : Axis) (e : Axis→Bool) (ht : Track Q e i U) (A : Weight L)
    (hp : ∀ j∈Q,Pressed j A) (hb : ∀ j∈Q,Own A j (e j)) (δ K : ℝ) (hd : 0<δ) (hK : 0≤K) : CanAllRC V A Q U δ K i := by
  induction ht with
  | rest hi => exact doneAllRC V H Q _ _ hd _ hi A (hp _ hi)
  | advance hi hj ho hx ih =>
    refine forwardsAllRC V H Q _ _ K hd hK _ _ hi hj ?_ A _ _ ho (hb _ hi) (hb _ hj) (hp _ hi) (hp _ hj) ih
    exact fun h => ho (congr_arg e h)

/-- Allows first correction scale growing! -/
theorem walkAllRC (H : S.Hierarchy) (Q : Finset Axis) (e : Axis→Bool) (i) (hi : i∈Q)
    (he : Mixed Q e) (A : Weight L) (hp : ∀ j∈Q,Pressed j A) (hb : ∀ j∈Q,Own A j (e j))
    (w : Axis→ℝ) (hw : ∀ j∈Q,w j ≤ 0) (δ : ℝ) (hd : 0<δ) : ∃ a : ℝ, 0 < a ∧
    ∀ (d : ℝ), 0 ≤ d → d ≤ a → ∀ (s : ℝ), 1≤s → ∀ (f : Grouping), Colors Q f →
      (∀ᶠ n in atTop, Room (mailsAllRC w f n i) (s*fuelAllRC d n)) → ∃ M : ℕ, ∀ m≥M,
        BudgetAllRC δ (fun n => pay (ν (V i) A) i Q (lampsAllRC m (w i) d s (f i) n) (mailsAllRC w f n)) := by
  obtain ⟨B,hB⟩ := (finite_range w).bddBelow
  let k := max 0 (-B)
  obtain ⟨a,ha,H⟩ := affordableAllRC V H Q Q i e (tracking Q Q e he (by simp) i hi) A hp hb _ k hd (le_max_left ..)
  refine ⟨a,ha,fun d hv hk s hs f hf hr => H _ hv hk w ?_ ((hw i hi).trans hv) ?_ f hf s hs hr⟩
  · intro j hj; refine ⟨?_,(hw j hj).trans ha.le⟩
    have ht : B ≤ w j := hB ⟨j,rfl⟩
    have he := show -B ≤ k from le_max_right ..; linarith
  · intro j h hh; contradiction
end YM.NSF.Outer
