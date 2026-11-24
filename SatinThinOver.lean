import SatinThinAxis
import SatinThinLean

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Gleam.Tempest
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix Module Regis clocks
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ:ℝ}{U:Config G n}{A:Support c}{o x z:Site n}{f m:ℕ} {X:T.Slice G}{Y:LinkArray G (Blip T (univ : Finset T.Free))} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L_:Floor H q n δ w)(D:LocalRatio J)

open CF.BProof Pressure.Worth Pressure.Worth.Pays Work.E09
/-- Pressure-tilt conjunct **uniform** before opportunity probes:
 accountant needed not only for expenditure of meter at a single root. -/
lemma shelfPressure (q: Clip)(R: Rules G)(D:LocalRatio J)(p:0<η)(g:0≤C)(S:ℝ)(L:Side)(t:ℝ)(h:0 ≤ t): ∀ᶠ x:ℝ in atTop, ∀ w:Side, Odd w.val → respire x L w.val → ∀ (p':BudgetPoint)(β:ℝ), β∈Set.Icc (x/2) (2*x) → p'.threshold=temp x → ∀ κ k:ℝ,κ ≤ β*unitDueS q p'/2→ k≤ empress q β x →∀ (n c:Side)(R':Ratio c n),2*(R'.count.val+1)<n.val → R'.count=w → ∀ {H:Bed} {Z:PathData G} (P:Attached H Z) (B':Z.Bounds q η C S){μ a:ℝ}(L_:Floor H q n μ a),0<μ → (∀ i,(Precision.K (H.metric.acts n)) i i ≤ t) → ∀ (τ Q R₁ R₂:ℝ) {φ:Config G n→ℝ}, Envelope φ → GaugeInvariant φ → ∀ (W:Altar G n→ℝ), ContDiff ℝ 1 W → (∀ i,|W i| ≤ R₁) → (∀ i, ‖fderiv ℝ W i‖ ≤ R₂) → (∀ a:Support c,∀ F:Finset (Cell n), ShelfScene B' P p' R' (radiusB x) β (ageC x) (shieldC x) (Q+healthC x*(trap R' (radiusB x) a+trap_s (radiusB x) F)) a F τ φ W) → (∫ U:Config G n,twice_rich Z q p' β κ k (shieldC x) U*Real.exp (τ * φ U) ∂prior G n) ≤ Real.exp (Roof J β n H + 7*meterC x*Fintype.card (Site n)+ Q + plumeCost B' P W τ + trend*R₂^2*τ^2):=by
 filter_upwards [outside_reserve L t D h, rate_long q R p g S, level_s q R D L,eventually_gt_atTop 0,agenda_cost] with x hp hg hl hx hx' w hw hc p' β hz v κ k hK hk n c X wX rfl H Z P B' μ a L_ h₁ d τ Q B1 B2 φ p3 g1 W0 p4 hb1 hb2 bnd
 let V:= meterC x; let M:=descendCost J β t (healthC x); let K:= radiusB x
 obtain ⟨he,ht,hu,hT⟩:= hp β hz.1 hz.2 X.count.val hw hc
 have hE := harvest_civil B' P L_ D (hl X.count.val hc β p' κ k hz.1 v hK hk) wX p3 p4 hb1 hb2 (coin_pos x 0 1 0).le hw he d h₁ ((half_pos hx).trans_le hz.1) h g (hx' n) ht hu g1 bnd -- tune arg order
 apply hE.trans (Real.exp_monotone ?_); unfold rentRoom; let N:ℝ:= Fintype.card (Site n); let T:ℝ:=Fintype.card (Site c); let t:= largerBill X.count.val (hallBill K); have hzN:0≤N:=by unfold N; positivity
 have hpx:0≤T:=by unfold T; positivity
 let D:ℝ:= X.count.val
 have hN:N=T*D^4:=by unfold N T D; rw [site_card,site_card,X.exact_size]; push_cast; ring
 have hm: taxΔ R q n p' β (ageC x) η C S K ≤ V*N:= hg p' β hz.2 v n
 change Roof _ _ _ _ + (taxΔ R q n _ β (ageC x) _ _ _ K +4*V*N+ 4*M*T*t) + Q + _+_+ Real.log 2*T+V*N≤ _
 have ht:0≤ V:= (coin_pos ..).le; change 4*M* t+Real.log 2≤ V*D^4 at hT; nlinarith only [mul_le_mul_of_nonneg_left hT hpx, mul_le_mul_of_nonneg_left hN.le ht, mul_le_mul_of_nonneg_left hN.ge ht, hm] -- maybe rhs V N implicit

/-! gauge-only (but both shelves). -/
def shelfShelf (q: Clip)(Z:PathData G)(J:ChartRatio G)(p:BudgetPoint)(β x:ℝ)(n:Side)(H:Bed) : Prop:= ∀ κ k:ℝ, κ ≤ β*unitDueS q p/2→ k ≤ empress q β x→
 (∫ U:Config G n,twice_angled Z q p β κ k (shieldC x) U∂prior G n) ≤ Real.exp (Roof J β n H + 7*meterC x*Fintype.card (Site n))

private lemma tiltRender (x y:ℝ) {U:Type*}: (fun _ :U => Real.exp y) = (fun _ => Real.exp y) :=rfl
lemma shelfUnmarked (q: Clip)(R: Rules G)(D:LocalRatio J)(p:0<η)(g:0≤C)(S:ℝ)(L:Side)(t:ℝ)(h:0 ≤ t): ∀ᶠ x:ℝ in atTop, ∀ w:Side, Odd w.val → respire x L w.val → ∀ (p':BudgetPoint)(β:ℝ), β∈Set.Icc (x/2) (2*x) → p'.threshold=temp x → ∀ (n c:Side)(R':Ratio c n),2*(R'.count.val+1)<n.val → R'.count=w → ∀ {H:Bed} {Z:PathData G} (P:Attached H Z) (B':Z.Bounds q η C S){μ a:ℝ}(L_:Floor H q n μ a),0<μ → (∀ i,(Precision.K (H.metric.acts n)) i i ≤ t) → shelfShelf q Z J p' β x n H:=by
 filter_upwards [shelfPressure q R D p g S L t h] with x hp w hw hc p' β hz v n c X wX wL H Z P B μ a L h₁ d κ k hK hk
 let u:= 7*meterC x* (Fintype.card (Site n):ℝ); let χ := X; let Ω:= unitDueL q p' (shieldC x); let φ:=fun _ :Config G n=> (0:ℝ); let W:= fun (_:Altar G n) => (0:ℝ)
 have hF:= hp _ hw hc _ _ hz v _ _ hK hk n c X wX wL P B L h₁ d 0 0 0 0 (φ:=φ) (Envelope.const _) (fun _ _=>rfl) W contDiff_const (fun z=>by simp [W]) (fun z=>by simp [W]) (fun a F A _ _ _ _ _ _=> by have hx:0≤healthC x:=(coin_pos ..).le; simp only [zero_mul,zero_add]; unfold trap trap_s; positivity)
 let V:=Real.exp (Roof J β n H+u); have hu: ∀ i:Config G n, Real.exp (0*φ i)=1:=fun i=>by rw [zero_mul,Real.exp_zero];
 simp only [hu,mul_one, plumeCost, mul_zero,zero_mul,zero_pow (by decide:(2:ℕ)≠0),mul_zero,add_zero] at hF
 simp only [Real.exp_zero,mul_one] at hF -- simp_rw sequential hazard order
 have hG:= forCivil (p:=p') (ε:=shieldC x) (κ:=κ) (dbκ:=k) (β:=β) B (show Envelope φ from Envelope.const _) V 0 (fun i=>by simpa only [hu,mul_one] using hF)
 simpa only [hu,mul_one] using hG
end YM.Gleam.Tempest
#print axioms YM.Gleam.Tempest.shelfPressure
#print axioms YM.Gleam.Tempest.shelfUnmarked
