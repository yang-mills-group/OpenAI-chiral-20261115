import YM.CF.Neon.Price
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Neon
open Py
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
variable{N P B:Side}{S_O:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S_O}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
open Moto Hove Tap Tune Taxi Nor Oath Larch
open Moto Hove Tap Tune Taxi Nor Oath Larch Haro
local notation "L'"=> R.L
variable (L0:Side)(k p l j:ℕ)(A':ℝ) (Ωs:Hove.Grant j p)(a:ℝ)(ha:0 <a)
-- aura.i covers forecast.
abbrev mast_ζ(x C:ℝ):= (2*((2:ℝ)^p*mintY p (a:=a) (C:=C) (radiusB x)*mintY p (a:=a) (C:=C) 0)+ Ωs.A/(L0.val:ℝ)^5)
include ha
lemma frost_Q(C:ℝ) : ∀ᶠ x:ℝ in atTop, mast_ζ L0 p j Ωs a x C≤ (Ωs.A+2)*(L0.val:ℝ)⁻¹^5:=by
 let H(x:ℝ):=mintY p (a:=a) (C:=C) (radiusB x); let h1(x:ℝ):=-(radiusB x:ℝ)*a; let P'(x:ℝ):=Real.exp (h1 x)
 have hp:Tendsto H atTop (𝓝 0):=by
    have he: Tendsto h1 atTop atBot:=by unfold h1; simp_rw [neg_mul]; apply tendsto_neg_atBot_iff.mpr; exact Tendsto.atTop_mul_const ha (tendsto_natCast_atTop_atTop.comp Work.E01.radiusB_tendsto)
    let X:= ((Real.exp a)* polV p a)* lurch a*C; have ht':Tendsto P' atTop (𝓝 0):= Real.tendsto_exp_atBot.comp he
    have hk(i): H i=P' i* X:=by unfold H mintY Haro.frost X P' h1; ring
    simp_rw [funext hk]; simpa using (ht'.mul_const X)
 let A(x):= 2*((2:ℝ)^p*H x*mintY p (a:=a) (C:=C) 0); let Ξ:= (L0.val:ℝ)⁻¹^5; have he:Tendsto A atTop (𝓝 0):=by simpa only [mul_zero,zero_mul] using! ((((hp.const_mul ((2:ℝ)^p)).mul_const (mintY p (a:=a) (C:=C) 0)).const_mul 2))
 have hv:0< Ξ:=by unfold Ξ; positivity
 filter_upwards [he.eventually (ge_mem_nhds (show 0< 2* Ξ from by positivity))] with x v
 change A x+Ωs.A / (L0.val:ℝ)^5 ≤ _; unfold Ξ at *; rw [div_eq_mul_inv, inv_pow, add_mul]; unfold A H at *; exact le_trans (add_le_add v le_rfl) (by rw [add_comm,inv_pow]) -- tune
omit ha
local notation "x_"=> (L0.val:ℝ)⁻¹
abbrev TimΞ (x v u:ℝ)(s:BudgetPoint):Prop := ∀ X Y:BudgetPoint, Siete.Find X Y k p x L0 →X.supportExponent=s.supportExponent→Y.supportExponent=s.supportExponent→ Tune.qCorset X.threshold Y.threshold (L0.val:ℝ) ≤ 4*(L0.val:ℝ)⁻¹^4 ∧ (L0.val:ℝ)⁻¹^4/4 ≤ Tune.qCorset X.threshold Y.threshold (L0.val:ℝ) ∧ mNv X Y l v u L0 ≤ 2*((L0.val:ℝ)⁻¹)^5
-- two-sided.
lemma pinchQ (M N:ℝ)(u:M≤2*N)(v:N ≤2*M)(hM:0 < M)(hN:0 < N): Tune.qCorset M N (L0.val:ℝ)≤ 4*(L0.val:ℝ)⁻¹^4∧ (L0.val:ℝ)⁻¹^4/4≤ Tune.qCorset M N (L0.val:ℝ):=by
 let a:ℝ:=(L0.val:ℝ)⁻¹^4; have hh:0 ≤ a:=pow_nonneg (by positivity) _
 unfold Tune.qCorset; constructor
 · rw [div_le_iff₀ (pow_pos hN _)]; apply (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hM.le u 2) hh).trans_eq; ring
 rw [le_div_iff₀ (pow_pos hN _)]; exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hN.le v 2) (by positivity)).trans_eq (by ring)
lemma scaleP : ∀ᶠ x:ℝ in atTop, temp x ≤2*fiery SU.group x L0 ∧ fiery SU.group x L0 ≤2*temp x:=by
 have ht:Tendsto (fun x=>fiery SU.group x L0/temp x) atTop (𝓝 1):=Work.E09.temp_ratio _
 filter_upwards [ht.eventually (ge_mem_nhds (show (1:ℝ)<2 by norm_num)), ht.eventually (le_mem_nhds (show (1/2:ℝ)<1 by norm_num)),eventually_gt_atTop (0:ℝ)] with x v w t
 have he:= Work.E09.temp_pos t; exact ⟨by linarith only [(le_div_iff₀ he).mp w],(div_le_iff₀ he).mp v⟩
-- purchase precision request and gamma trace lamp.Tie post x profile oμ. grants hscope; l0 sticker. lower via threshold.F. cost functions independent matured. 
lemma ray_p(U:ℝ→ℝ)(t:Tendsto U atTop (𝓝 0))(s:BudgetPoint): ∃ v:ℝ, v>0 ∧∀ᶠ x:ℝ in atTop, TimΞ L0 k p l x v (U x) s:=by
 let y:= L0.val; let K:ℝ:=Fintype.card (PlaqAxes×PlaqAxes); let g:= (y:ℝ)⁻¹^5
 have hx:0<g:=by unfold g y; positivity
 have hp:0 < K:=by unfold K; positivity
 let ν:=g/(2*K); have he:0 <ν:=div_pos hx (by positivity)
 let Y(x:ℝ):= |U x| *(KX l:ℝ)*(4*x_^4); have ht:Tendsto Y atTop (𝓝 0):=by simpa only [abs_zero,zero_mul] using ((t.abs.mul_const (KX l:ℝ)).mul_const (4*x_^4))
 refine ⟨ν,he,?_⟩; filter_upwards [scaleP L0,ht.eventually (ge_mem_nhds hx)] with x H uh X0 Y0 pT _ _ -- κs.forall body TimΞ abbrev scope binder shadows x.
 obtain ⟨hz,hL⟩:= H; have hh:= pT.large; have hs:=pT.low
 rewrite [←hh,←hs] at hz hL; obtain ⟨ho,hq⟩:= pinchQ L0 X0.threshold Y0.threshold hz hL X0.threshold_pos Y0.threshold_pos
 refine ⟨ho,hq,?_⟩
 let X:=Tune.qCorset X0.threshold Y0.threshold L0.val; change Tune.l_fee K Y0 X0 ν 1+U x*(KX l:ℝ)*‖(X:ℂ)‖ ≤ 2*g
 have hv:0≤ X:=le_trans (by positivity) hq
 apply le_trans _ (two_mul g).symm.le; apply add_le_add _ _; swap
 · rw [Complex.norm_real,Real.norm_eq_abs, abs_of_nonneg hv]; apply le_trans _ uh; exact mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)) ho hv (by positivity) -- tune
 unfold Tune.l_fee; apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ X0.threshold_pos.le hz 2) he.le) (one_div_nonneg.mpr (show 0≤2*Y0.threshold^2 from (by positivity)))) hp.le)
 have hY:0 < Y0.threshold:= Y0.threshold_pos; unfold ν; field_simp; linarith -- tune
lemma nought_X : (1+(L0.val^2:ℕ):ℝ)⁻¹ ≤ (L0.val:ℝ)⁻¹^2:=by rw [inv_pow]; apply inv_anti₀ (by positivity); push_cast; linarith
end YM.CF.Neon
