import YM.SU5.WakeInvestment.ThirdHall
import SatinThinOver


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
lemma near_flake(f:ℝ)(hf:0<f) : ∀ᶠ x:ℝ in atTop,∀ (q':BudgetPoint) (β:ℝ), x/2≤ β → q'.threshold=temp x → droitC x ≤ β*Wake.unitDueN q (f*q'.threshold)/2:=by
 let A:= (q.linear/16*f^2); have hs:0<A:=by unfold A; have h:=q.tail_pos; positivity
 filter_upwards [eventually_gt_atTop (0:ℝ),coin_budget (Or.inr (Or.inl (show (0:ℝ)=0 ∧ (3/2:ℝ)<2 from ⟨rfl,by norm_num⟩))) 1 A hs (c:=0) (f:=0)] with x hx h q' β hp hP
 let X:=temp x; let Y:=q'.threshold
 have ht: x* X^2=coin x 0 2 0:= by unfold X; rw [←thresh_eq hx,coin_pow]; nth_rw 1 [←coinY hx]; rw [coin_mul]; norm_num
 unfold droitC; rw [one_mul,←ht] at h; unfold A at h; unfold Wake.unitDueN; rw [hP]; unfold X at h; nlinarith only [h.le, mul_le_mul_of_nonneg_right hp (mul_nonneg q.tail_pos.le (sq_nonneg (f*temp x)))]
/-- Pressure-tilt conjunct **uniform** before opportunity probes:
 accountant needed not only for expenditure of meter at a single root. -/
lemma atNear (f:ℝ)(hf:0<f)(f1:f≤1) (q: Clip)(R: Rules G)(D:LocalRatio J)(p:0<η)(g:0≤C)(S:ℝ)(L:Side)(t:ℝ)(h:0 ≤ t): ∀ᶠ x:ℝ in atTop, ∀ w:Side, Odd w.val → respire x L w.val → ∀ (p':BudgetPoint)(β:ℝ), β∈Set.Icc (x/2) (2*x) → p'.threshold=temp x → ∀ κ k:ℝ,κ ≤ β*unitDueS q p'/2→ k≤ empress q β x →∀ z:ℝ,z≤ β* Wake.unitDueN q (f*p'.threshold)/2→∀ (n c:Side)(R':Ratio c n),2*(R'.count.val+1)<n.val → R'.count=w → ∀ {H:Bed} {Z:PathData G} (P:Attached H Z) (B':Z.Bounds q η C S){μ a:ℝ}(L_:Floor H q n μ a),0<μ → (∀ i,(Precision.K (H.metric.acts n)) i i ≤ t) → ∀ (τ Q R₁ R₂:ℝ) {φ:Config G n→ℝ}, Envelope φ → GaugeInvariant φ → ∀ (W:Altar G n→ℝ), ContDiff ℝ 1 W → (∀ i,|W i| ≤ R₁) → (∀ i, ‖fderiv ℝ W i‖ ≤ R₂) → (∀ a:Support c,∀ F:Finset (Cell n), Wake.nearScene B' P p' R' (radiusB x) β (ageC x) (shieldC x) (f*p'.threshold) (Q+healthC x*(trap R' (radiusB x) a+trap_s (radiusB x) F)) a F τ φ W) → (∫ U:Config G n,Wake.nearRich Z q p' β κ k (shieldC x) z (f*p'.threshold) U*Real.exp (τ * φ U) ∂prior G n) ≤ Real.exp (Roof J β n H + 7*meterC x*Fintype.card (Site n)+ Q + plumeCost B' P W τ + trend*R₂^2*τ^2):=by
 filter_upwards [outside_reserve L t D h, rate_long q R p g S, level_s q R D L,eventually_gt_atTop 0,agenda_cost,near_flake (q:=q) f hf] with x hp hg hl hx hx' hzN w hw hc p' β hz v κ k hK hk z ℓ n c X wX rfl H Z P B' μ a L_ h₁ d τ Q B1 B2 φ p3 g1 W0 p4 hb1 hb2 bnd
 let V:= meterC x; let M:=descendCost J β t (healthC x); let K:= radiusB x
 obtain ⟨he,ht,hu,hT⟩:= hp β hz.1 hz.2 X.count.val hw hc
 have hE := Wake.near_civil B' P L_ D (hl X.count.val hc β p' κ k hz.1 v hK hk) wX p3 p4 hb1 hb2 (mul_pos hf p'.threshold_pos).le (mul_le_of_le_one_left p'.threshold_pos.le f1) hK (show z+droitC x ≤ β* Wake.unitDueN q (f*p'.threshold) from (by linarith only [hzN p' β hz.1 v,ℓ])) (coin_pos x 0 1 0).le hw he d h₁ ((half_pos hx).trans_le hz.1) h g (hx' n) ht hu g1 bnd
 apply hE.trans (Real.exp_monotone ?_); unfold rentRoom; let N:ℝ:= Fintype.card (Site n); let T:ℝ:=Fintype.card (Site c); let t:= largerBill X.count.val (hallBill K); have hzN:0≤N:=by unfold N; positivity
 have hpx:0≤T:=by unfold T; positivity
 let D:ℝ:= X.count.val
 have hN:N=T*D^4:=by unfold N T D; rw [site_card,site_card,X.exact_size]; push_cast; ring
 have hm: taxΔ R q n p' β (ageC x) η C S K ≤ V*N:= hg p' β hz.2 v n
 change Roof _ _ _ _ + (taxΔ R q n _ β (ageC x) _ _ _ K +4*V*N+ 4*M*T*t) + Q + _+_+ Real.log 2*T+V*N≤ _
 have ht:0≤ V:= (coin_pos ..).le; change 4*M* t+Real.log 2≤ V*D^4 at hT; nlinarith only [mul_le_mul_of_nonneg_left hT hpx, mul_le_mul_of_nonneg_left hN.le ht, mul_le_mul_of_nonneg_left hN.ge ht, hm]

lemma turnL (s:Signed) (U:Config G n)(κ t :ℝ) : κ*(misdemean t (pull s 0 U)).card=κ*(misdemean t U).card:= by
 let i:Equiv.Perm (Cell n):= Equiv.ofBijective (Face.send s 0) ⟨Face.injective_send s 0,Finite.injective_iff_surjective.mp (Face.injective_send s 0)⟩
 have h(b:Cell n): b∈ misdemean t (pull s 0 U) ↔ i b∈ misdemean t U:=by simp only [misdemean,mem_filter]; rw [Face.send_price U b s 0 G.chord G.chord_inv (fun _ u=> G.chord_conj u _)]; simp; rfl
 rw [← counts_tax,← counts_tax]; exact (sum_congr rfl (s₂:=univ) (g:=fun x=> if i x∈misdemean t U then κ else 0) (fun x _=>by simp only [h] )).trans (Equiv.sum_comp i (fun x=> if x∈misdemean t U then κ else 0))

include B in
/-- Extra invoice in one actual measure and the Wick comparator, not before symmetrisation. -/
lemma nearTurns (ι β κ k αcost ε τ Q:ℝ)(p:BudgetPoint)(F:Config G n→ℝ)(u:Envelope F)(X:∀ s:Signed, (∫ U:Config G n,Wake.nearRich Z q p β κ k ε αcost τ U*Real.exp (ι*F (pull s 0 U))∂prior G n) ≤ Q): (∫ U:Config G n,twice_angled Z q p β κ k ε U * Real.exp (αcost*(misdemean τ U).card) * Real.exp (ι*F U)∂prior G n) ≤ Q:=by
  let φ(U:Config G n):= αcost*(misdemean τ U).card + ι*F U
  have hu:Envelope φ:=(conduct ..).add ((Envelope.const ι).mul u)
  have he:= forCivil (β:=β) (κ:=κ) (dbκ:=k) (ε:=ε) (p:=p) B hu Q 1 ?_
  swap; · intro i; unfold φ; simp_rw [one_mul, turnL, Real.exp_add]; simpa only [Wake.nearRich, twice_rich, Real.exp_add, mul_assoc] using X i
  unfold φ at he; simpa only [one_mul, Real.exp_add,mul_assoc] using he
end YM.Gleam.Tempest
