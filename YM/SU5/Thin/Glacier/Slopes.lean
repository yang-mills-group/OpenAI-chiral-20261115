import YM.SU5.Thin.Glacier.Billing
import YM.SU5.Thin.Glacier.Canyon
import YM.SU5.Thin.Glacier.Reservoir
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Gleam
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ:ℝ}{U:Config G n}{A:Support c}{m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
namespace clocks
open Work.E09 AnalyticBridge.Annulus1AD
local notation "B" x:max=> (height x:ℝ)
lemma canyonRide(k: Clip)(R: Rules G)(D:LocalRatio J)(t:ℝ)(L:Side)(p:0<η)(g:0≤C)(S:ℝ)(h:0 ≤ t)(R0:ℝ)(hr:0 ≤ R0) : ∀ᶠ x:ℝ in atTop, ∀ w:Side, Odd w.val → starSpan x w.val L→ ∀ (p':BudgetPoint)(β:ℝ), β∈Set.Icc (x/2) (2*x) → p'.threshold=temp x → ∀ (n c:Side)(R':Ratio c n),2*(R'.count.val+1)<n.val → R'.count=w → ∀ {H:Bed} {Z:PathData G} (P:Attached H Z) (B':Z.Bounds k η C S){μ a:ℝ}(q:Floor H k n μ a),0<μ → (∀ i,(Precision.K (H.metric.acts n)) i i ≤ t) → ∀ (τ Q R₁ R₂:ℝ) {φ:Config G n→ℝ}, Envelope φ → GaugeInvariant φ → ∀ (W:Altar G n→ℝ), ContDiff ℝ 1 W → (∀ i,|W i| ≤ R₁) → (∀ i, ‖fderiv ℝ W i‖ ≤ R₂) → (∀ (a:Support c)(W':Finset (Cell n)), RimScene B' P p' R' (height x) β (scant x) (Q+R0*fritTrap R' (height x) a W') (outerMark x) a W' τ φ W) → (∫ U:Config G n,heatG Z k p' β (grain x) (ledge x) (outerMark x) U * Real.exp (τ * φ U) ∂prior G n) ≤ Real.exp (Roof J β n H + oar x*Fintype.card (Site n)+ Q + plumeCost B' P W τ + Regis.trend*R₂^2*τ^2):=by
 obtain ⟨A,hA,H⟩:= descends J D t h R0 hr
 filter_upwards [H, slip L,stainBeat A hA.le,ledge_due L A hA.le,fuelling k L D R,stainSurface A L hA.le,(chipTreasury k L p g R S).discounts (by norm_num: -(1/10:ℝ)< -(1/500:ℝ)) (by norm_num:(0:ℝ)<1/12),fright_fee (Fintype.card PlaqAxes) (Nat.cast_nonneg _), eventually_gt_atTop (0:ℝ)] with x hD hS V W hE hW uF vF t' w hM k' p' b hB l₀ n c r T F0 H Z u B' μ a q v d τ Q B1 B2 φ p3 g1 W0 p4 hb1 hb2 bnd
 have hy: Odd r.count.val:=F0.symm ▸ hM; have hY:starSpan x r.count.val L:=F0.symm ▸ k'; let d':= descendCost J b t R0; have hv': d' ≤ A*B x:= hD b hB.1 hB.2
 let C':=(1/12:ℝ)*oar x; let iB:= B x; have hp:= hE r.count.val r.count.property hY _ _ hB.1 l₀; obtain hh:= hS r.count.val hY; have ht:Gleam.hallBill (height x) ≤ r.count.val/2:=hh
 refine (ice_canyon B' u q D hp T p3 p4 hb1 hb2 hr hy ht d v ((half_pos t').trans_le hB.1) h g ?_ (d₀:=B x) ?_ g1 bnd).trans (Real.exp_monotone ?_)
 · exact (W _ hY).trans' (by change 4*d'*_ ≤ _; gcongr)
 · exact V.trans' (by change 4*d'*_+_ ≤ _; gcongr)
 let M:ℝ:=Fintype.card (Site c); let N:ℝ:=Fintype.card (Site n); let X:= height x; let y:= r.count; have hz:0≤N:=by unfold N; positivity; -- indent
 have he: 0≤ M:=by unfold M; positivity
 have hf:N=M*(y.val:ℝ)^4:=by unfold N M y; rw [site_card,site_card,r.exact_size]; push_cast; ring
 let z:=largerBill (y.val) (hallBill X); let p₀:=M*Real.log 2; have hg: 4*d'*M*z+p₀ ≤ C'*N:=by
    rw [hf]; let a':=(A*iB); have hu:=mul_le_mul_of_nonneg_right (hW y hY hy) he; unfold p₀; change _ ≤ C'*_; change (4*a'*z+Real.log 2)*M ≤ C'*(y.val:ℝ)^4*M at hu
    have hw:d' ≤ a':=hv'; nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hw he) (show 0≤ (z:ℝ) by positivity),hu]
 let b':= taxΔ R k n p' b (scant x) η C S X
 have hb : b' ≤ C'*N:= (chipFuel L k hB.2 l₀ R g t'.le).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans uF) hz)
 let s:=Regis.trend*B2^2*τ^2; have hx:Real.exp (-iB)*(Fintype.card (Cell n):ℝ) ≤ C'*N:=by
    rw [show Fintype.card (Cell n)=Fintype.card (Site n)*Fintype.card PlaqAxes from Fintype.card_prod ..,Nat.cast_mul,mul_left_comm]; change N* (Real.exp (-iB)*_) ≤ _; rw [mul_comm (Real.exp _), mul_comm C']; exact mul_le_mul_of_nonneg_left vF hz
 change Roof J b n H+(b'+4*C'*N+4*d'*M*z)+Q+_+s+Real.log 2*M+_ ≤ _+ _ + _ + _ + _; unfold C' at *; unfold iB at hx; unfold p₀ at *; change _ ≤ Roof J b n H + oar x*N+_+_+s; nlinarith only [hg,hb,hx,hz, mul_nonneg (shinyH x t').2.2.2.le hz]
end clocks

end YM.Gleam