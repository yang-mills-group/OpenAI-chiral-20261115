import YM.CF.Vp929.Stage.Real
import YM.CF.Vp929.Budget.Read
import YM.CF.Continuum.LaurelGold

/-!
# Lemma limsup, for the physical identification in VOLUME_RATE.

Keep the proof with two prices; use a finite-height quantitative version of the simultaneous
limsups proof (induct on the amount of cutoff allowance remaining). In this application steps are
common starting at k-1; k tends to infinity. Outputs satisfy the starred inequalities in Certified.
-/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief VolumeRate
open scoped Mew
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
variable {d : ℝ} {m N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
  {h x delay : ℝ} {C D R0 : ℝ → ℝ} {N0 k : ℕ} {P : Prescription R B}
namespace Branch
local notation "M" => cell m B R.L
local notation "X" => hat R.L x
local notation "F" => dleaf R.L
variable (H : Service V U W J q h D C R0 P N0 delay) (hh : 1≤h)
    {A A' : Branch W m k x N0} (a : Bon J q h D delay A) (a' : Bon J q h D delay A')
    {b b' : Bet k} {z : ℝ} (s : Solved P A z b) (s' : Solved P A' z b')
    (e : A.T=A'.T) (t : A.toSpine=A'.toSpine)
local notation "Z" => A.gram P b
local notation "Y" => A'.gram P b'
local notation "Q" => A.chargeLevel P b
local notation "Q'" => A'.chargeLevel P b'
abbrev decline (r : ℕ) : ℝ := 2*(1/2:ℝ)^r
include a a' s s' H e t
lemma run_bound (r : ℕ) (i : ℕ) (hk : i+r≤k) : Cost (A.T.a i) h (F (X i)*decline r) (Q i-Q' i) ∧
       |(Z i).beta-(Y i).beta| ≤ strip (X i)*decline r := by
  let x₁:= fun j=> (Z j).beta; let x₂:= fun j=> (Y j).beta; let d₁:=A.fee P; let d₂:= A'.fee P
  induction r generalizing i with
  | zero =>
    have h:= a.charged H s.toRealQ i hk; have he:= a'.charged H s'.toRealQ i hk
    constructor
    · exact (h.toCost.sub (show Cost (A.T.a i) _ _ _ from e ▸ he.toCost)).mono (by simp only [decline,pow_zero,mul_one]; linarith [(a.clocks i).leaf])
    have hx:= (s.paid i (Nat.zero_le _) hk); have hy:= (s'.paid i (Nat.zero_le _) hk); rw [←t] at hy
    let u:= A.toSpine.pilot x i
    rw [← s.toRealQ.coeRe i hk,←Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hx
    rw [← s'.toRealQ.coeRe i hk,←Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hy
    have hq:= abs_sub_le (Z i).beta u (Y i).beta; rw [abs_sub_comm u (Y i).beta] at hq
    simp only [decline,pow_zero,mul_one]; linarith
  | succ r ih=>
    have η:0≤decline r:=by unfold decline; positivity
    have stars (j) (u : j+1+r ≤ k) : Cost (A.T.a j) h (F (X j)*((decline r+decline r)/4)) (Q j-Q' j) ∧
         |(d₁ j b).re-(d₂ j b').re| ≤ 100* D (X j)*(decline r+decline r) := by
      have hi:j<k:=by omega
      have e₁:A.op P j=A'.op P j:= by unfold op; rw [e,t]
      obtain ⟨hv,hY⟩:= ih (j+1) u
      have hg:= (a.certified H j hi); rw [a.corr_successor H s.toRealQ j hi,a'.corr_successor H s'.toRealQ j hi]; dsimp only [d₁,d₂]; rw [←a.fee_eq H s.toRealQ j hi,←a'.fee_eq H s'.toRealQ j hi,←e₁,Complex.ofReal_re,Complex.ofReal_re]; refine hg.stars _ _ _ _ _ _ ?_ η η (hat_step j ▸ hv) (hat_step j ▸ hY)
      rintro u ht; obtain rfl|ht:= ht
      · exact ⟨hat_step j ▸ (a.beta_ok H s.toRealQ _ hi).1, hat_step j ▸ a.charged H s.toRealQ _ hi⟩
      rw [Set.mem_singleton_iff] at ht; subst u; refine ⟨hat_step j ▸ (a'.beta_ok H s'.toRealQ _ hi).1,?_⟩
      change Charged (A.T.a (j+1)) (A.last.Q (j+1)) _ _ _ _ _; rw [e,← hat_step]; exact t ▸ a'.charged H s'.toRealQ _ hi
    constructor
    · exact (stars i (by omega)).1.mono (by unfold decline; rw [pow_succ]; exact le_of_eq (by ring))
    have hi : i ≤ k := by omega
    have h1 : b.read i= (A.toSpine.pilot x i:ℂ)+(z:ℂ)+∑ j∈range i,d₁ j b := by rw [Bet.read_of_le _ hi]; exact congrFun s.fixp.symm _
    have h2 : b'.read i= (A.toSpine.pilot x i:ℂ)+(z:ℂ)+∑ j∈range i,d₂ j b' := by rw [Bet.read_of_le _ hi,t]; exact congrFun s'.fixp.symm _
    change |(b.read i).re-(b'.read i).re| ≤ _
    rw [h1,h2,Complex.add_re,Complex.add_re _ (∑ j∈_,d₂ j b'),add_sub_add_left_eq_sub, Complex.re_sum, Complex.re_sum, ←Finset.sum_sub_distrib]
    let t j:= strip (X j); have he:(∑ j∈range i, D (X j)) ≤ t i * (1/400):= by
      have p(j) : 0 < t j := strip_pos (a.clocks j).grade
      apply le_trans _ (mul_le_mul_of_nonneg_left (prices_sum a.prices i) (p i).le)
      rw [mul_sum]; refine sum_le_sum fun j h=>?_; set y:= D (X j); have hY:0 ≤ y:=(a.clocks j).bank; let b:=t (j+1); have hx':0<b:=p _
      change y ≤ t i*(y/b); rw [←mul_div_assoc]; exact (le_div_iff₀ hx').2 (le_trans (mul_le_mul_of_nonneg_left ((a.clocks _).increase _ (hat_mono (mem_range.mp h))) hY) (le_of_eq (mul_comm ..)))
    refine (Finset.abs_sum_le_sum_abs ..).trans <| le_trans (sum_le_sum fun j p=> (stars j (by have ht:= mem_range.mp p; omega)).2) ?_
    rw [←sum_mul,←mul_sum]; refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ)≤100)) (add_nonneg η η)) (le_of_eq ?_); unfold t decline; rw [pow_succ]; ring

open Graph Graph.Diff Graph.Angle Window
omit a' s' e t in
lemma Bon.warm (i) (hi : i ≤ k) : Integrable (fun x=> beamZ (M i) (field U (Z i) (A.loom i) x)) (city (M i)) := by
  let U':= (a.can.cape i).paid; have g:= denInt W (I:=A.last.Q i) (show Roof _ J.k d J.n (A.loom i) from {U' with paid:=fun j=>(U'.paid j).shrink J.hr.le}) (k-i) (J.gran.trans (a.can.cape i).size) _ _ ((a.charged H s.toRealQ i hi).toCost.lot (Z i).beta (Z i).v)
  have h : Integrable (denZ (Z i) U (A.loom i)) (city (M i)) := Integrable.of_bound g.meas.aestronglyMeasurable _ (Eventually.of_forall g.cost.choose_spec)
  exact (innerSL ℂ (mateK (M i)) |>.restrictScalars ℝ).integrable_comp (h.smul (Complex.exp (-(Z i).v)))
omit a a' H e t s s' in
private lemma diff_mono {n B:Side} {U' : Grasp V.U B d} {Xx Xx' : GramM (mid n B)} {S S'} (ε:ℝ) (L:∀ i, ‖field U' Xx S i-field U' Xx' S' i‖ ≤ ε) (g:Integrable (fun i=>beamZ _ (field U' Xx S i)) (city _)) (g':Integrable (fun i=>beamZ _ (field U' Xx' S' i)) (city _)) : ‖compensated U' Xx S-compensated U' Xx' S'‖ ≤ ε := by
  rw [←integral_beam,←integral_beam,←integral_sub g g']
  have h(i:Orbit (mid n B)): ‖beamZ _ (field U' Xx S i)-beamZ _ (field U' Xx' S' i)‖ ≤ ε:= by
    unfold beamZ; rw [←inner_sub_right]; exact (norm_inner_le_norm ..).trans (by rw [(tickB (mid n B)).2,one_mul]; exact L i)
  exact (norm_integral_le_of_norm_le (integrable_const ε) (Eventually.of_forall h)).trans_eq (by rw [integral_const,probReal_univ,one_smul])

omit a a' s s' e t
include hh
lemma limsup (T : Month x 1 6 2 N0 V W) (ε : ℝ) (he : 0<ε) (i : ℕ) : ∀ᶠ k : ℕ in atTop,
    ∀ (A A' : Branch W m k x N0) b b' z, A.T=T → A'.T=T → A.toSpine=A'.toSpine → A.Bon J q h D delay → A'.Bon J q h D delay → Solved P A z b → Solved P A' z b' →
    (|(A.gram P b i).beta-(A'.gram P b' i).beta| ≤ ε) ∧ (∀ y, ‖field U (A.gram P b i) (A.loom i) y-field U (A'.gram P b' i) (A'.loom i) y‖ ≤ ε) ∧ ‖compensated U (A.gram P b i) (A.loom i)-compensated U (A'.gram P b' i) (A'.loom i)‖ ≤ ε := by
  let δ:= F (X i)/1000; let p:=T.a i; let N:= (M i); let Rr:= K.top.clip; let κ:= K.top.paths; let f:= taxPart V p (2*(X i))*sites N; let α:= Real.exp f; let w:= α*Real.exp (flagBill (M i) δ δ (cashU W.C))
  let D':= strip (X i); let u:= F (X i); have t:Tendsto decline atTop (𝓝 0):= by
    simpa only [mul_zero] using ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num)).const_mul (2:ℝ))
  have θ:Tendsto (fun r=>Record.paceZ p N Rr κ (D'*decline r) (u*decline r)) atTop (𝓝 0):= by
    unfold Record.paceZ Graph.Diff.rankV; exact (by simpa only [mul_zero,zero_mul,add_zero] using! ((((t.const_mul D').mul_const (jumpTax p (More N) Rr κ)).const_mul 2).add (((t.const_mul u).mul_const ((More N).val^4 : ℝ)).const_mul 3)))
  have hf₁ : ∀ᶠ r : ℕ in atTop, D'*decline r ≤ ε:= (t.const_mul D').eventually (ge_mem_nhds (by simpa using he))
  have hf₂ : ∀ᶠ r : ℕ in atTop, (D'*decline r)*jumpTax p (More N) Rr κ ≤ 1/2:= ((t.const_mul D').mul_const _).eventually (ge_mem_nhds (by norm_num))
  have hf₃ : ∀ᶠ r : ℕ in atTop, (u*decline r)* ((More N).val:ℝ)^4 ≤ 1/2 := ((t.const_mul u).mul_const _).eventually (ge_mem_nhds (by norm_num))
  have hf₄ : ∀ᶠ r : ℕ in atTop, w*Record.paceZ p N Rr κ (D'*decline r) (u*decline r) ≤ ε:= (θ.const_mul w).eventually (ge_mem_nhds (by simpa using he))
  obtain ⟨r,p₁,p₂,p₃,p₄⟩:= (hf₁.and (hf₂.and (hf₃.and hf₄))).exists
  filter_upwards [eventually_ge_atTop (i+r)] with k hk; intro A A' b b' z aT aT' t a a' s s'; let Zh:= gram P A b i; let Yh:= gram P A' b' i; let r':=decline r; let w':=Record.paceZ p N Rr κ (D'*r') (u*r')
  have hi:i≤ k:= (Nat.le_add_right i r).trans hk; let D0:= D'*decline r; let Vμ:=u*decline r
  obtain ⟨q₁,q₂⟩:= run_bound H a a' s s' (aT.trans aT'.symm) t r i hk
  have e : Zh.p=p:=congrArg (fun z: Month x 1 6 2 N0 V W => z.a i) aT; have e' : Yh.p=p:=congrArg (fun z: Month x 1 6 2 N0 V W => z.a i) aT'
  have hc : Record.Cart Zh Yh h κ Vμ D0 := ⟨e.trans e'.symm,rfl,rfl,congrArg (fun A : Spine W m k => A.last.Q i) t,q₂,rfl,rfl, ⟨⟨q₁.inc.weight,fun _ v=> v.elim⟩,⟨q₁.dark.weight,fun _ v=> v.elim⟩⟩,e ▸ p₂,p₃⟩
  let T:= (a.can.cape i).paid; let S:= A.loom i; have hw:A'.loom i=S:=congrArg (fun A : Spine W m k => A.loom i) t.symm; have hR: Roof _ J.k d J.n S:={T with paid:=fun i=>(T.paid i).shrink J.hr.le}
  let g:= levelQ W.C; let C:= cashU W.C; have pw: Ledger h δ δ g C Zh:= frostQ ((a.charged H s.toRealQ i hi).toCost.lot _ _) (zero_le_one.trans hh) (A.last.sound i); have pu:Ledger h δ δ g C Yh:= frostQ ((a'.charged H s'.toRealQ i hi).toCost.lot _ _) (zero_le_one.trans hh) (A'.last.sound i)
  have pv:=V.L.mood (k-i); have hu:=J.gran.trans (a.can.cape i).size; have hp:0≤δ:=div_nonneg (a.clocks i).leaf.le (by norm_num)
  let F'(i:Orbit N):= Record.on_trace Zh Yh S hR hu hc pv pw pu hh hp (cash_v _) (level_p _).le (paths_nonneg V) i
  have ha: 0 ≤ w' := by
    unfold w'; rw [←e]; exact Record.respects Zh Yh S hR hu hc pv pw pu hh hp (cash_v _) (level_p _).le (paths_nonneg V)
  have hX (b:Orbit N) : past Yh b.1 ≤ α := by
    have ht: X i/2 ≤ Yh.beta ∧ Yh.beta ≤ 2* X i := matched_of_enters (a'.clocks i) (a'.beta_ok H s'.toRealQ i hi).2; have hx:= a.clocks i
    have h:= Window.energy_low Yh.p Yh.path Rr pv (b:=Yh.beta) (by linarith [hx.grade,ht.1]) b.1
    have ht' := ((neg_le.mp h).trans (tax_price V N ht.2)); rw [e'] at ht'
    unfold Graph.past; rw [e']; exact Real.exp_monotone ht'
  have hY(j:Orbit N) : ‖field U Zh S j-field U Yh (A'.loom i) j‖ ≤ ε := by
      rw [hw]; have he:= F' j; rw [e] at he; exact he.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hX _) (Real.exp_pos _).le) ha).trans p₄)
  exact ⟨q₂.trans p₁,hY,diff_mono _ hY (Bon.warm H a s i hi) (Bon.warm H a' s' i hi)⟩
end Branch
end YM.CF.Py.Rate
