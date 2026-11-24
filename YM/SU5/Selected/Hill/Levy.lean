import YM.SU5.Selected.Hill.Par
import YM.SU5.Selected.Hill.Cote
/-! Counts and loss. -/
set_option autoImplicit false
noncomputable section
namespace YM.Hill.Post
open Function Filter Metric Finset Lattice Tree Wilson RG Pressure Exterior Work.F03 Precision MeasureTheory Chene Trunk FreeResolvent Matrix Chene.Tail Melody SectorNext.Vacuum.FlatTree Calculus Next.Rank.Axial Chene.Perks
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius MatrixOrder Matrix InnerProductSpace Kronecker
open Next.SectorChange Luge SectorTools.PhysicalGaussianSwitch
open CF CF.BPress CF.Graph Box AnalyticBridge.Annulus1AD
variable {G:Gauge}{n:Side}{r:Side}{S:Lots n}{B' B R m:ℕ}
variable {P:BudgetPoint}{W:PathData G}(C:Clip){σ θ τ b:ℝ}
variable (Z:ChartRatio G)(p:LocalRatio Z) (L: Next.Rank.Spindle.Rules G) (X D A:ℝ)
lemma windows_x (ε:ℝ)(u:0<ε) : ∃ θ τ:ℝ,0<θ∧ θ<1∧ 0<τ∧ nearF G θ τ≤ ε:=by
 let g(x:ℝ):= nearF G x x; have hp:ContinuousAt g 0:= by apply ContinuousAt.sub (continuous_id.continuousAt); apply ContinuousAt.div_const; exact continuousAt_const.mul (ContinuousAt.log (continuousAt_const.sub continuousAt_id) (by simp)) -- tune
 have he : ∀ᶠ x:ℝ in 𝓝[>] 0,x<1∧ g x≤ ε:= by apply Filter.Eventually.filter_mono (nhdsWithin_le_nhds); refine Filter.Eventually.and (gt_mem_nhds zero_lt_one) (hp.eventually (ge_mem_nhds ?_)); simpa [g,nearF] using u
 obtain ⟨x,h,p⟩:=(he.and (self_mem_nhdsWithin)).exists; exact ⟨x,x,p,h.1,p,h.2⟩
abbrev Λ₁(r:Side)(B':ℕ):=96*(B':ℝ)/(r.val:ℝ)
lemma tickets_ (p':r.val ≤ n.val) (S:Lots n): (Fintype.card (outside r S B'):ℝ) ≤ Λ₁ r B'*bulk n+ (4*r.val^4:ℝ)* S.card:=by
 apply le_trans (Nat.cast_le.mpr (outside_count r S B')); unfold bulk; rw [site_card]; push_cast
 let d:=(n.val:ℝ); let k:=(r.val:ℝ); have hx:0<k:= Nat.cast_pos.mpr r.property; have hv:k≤ d:= Nat.cast_le.mpr p'
 have hp:(↑(n.val / r.val)+1:ℝ)*k≤ 2*d:=by
    rw [_root_.add_mul,one_mul]; have h : (↑(n.val/r.val):ℝ)*k≤d:=by unfold k d; exact_mod_cast Nat.div_mul_le_self n.val r.val
    linarith only [h,hv]
 let A:=(↑(n.val/r.val):ℝ)
 change 4*(12*(A+1)*B'*d^3+ S.card* k^4) ≤ 96*B'/k*d^4+ (4*k^4 * _) -- power maybe cast r^ℕ? push casts
 apply le_of_mul_le_mul_right ?_ hx; rw [_root_.add_mul, mul_right_comm _ (d^4), div_mul_cancel₀ _ hx.ne']; nlinarith only [mul_le_mul_of_nonneg_right hp (show 0 ≤ (B':ℝ)*d^3 from (by have h':=hx.trans_le hv; positivity))]
include p
lemma highB : ∃ K≥ (0:ℝ),∀ᶠ x in atTop,∀ b∈Set.Icc (x/2) (2*x), glazeB Z b A ≤ K*lscale x := by
 let Q:= logCash Z; let e(x:ℝ):= 1+Real.log x; let g(x:ℝ):=lscale x; let f:= atoms0 G*dollar A/2; have h0:0≤f:=by unfold f atoms0 dollar; positivity; -- need next line
 have hQ:0≤Q:= logCash_nonneg _
 refine ⟨f+2*Q,by positivity,?_⟩; filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1,eventually_ge_atTop (1:ℝ)] with x h d b v
 have hp:= price_spare Z p.scale d v; have ht:Real.log x ≤ lscale x:=by unfold lscale; have hv:Real.log x^2 ≤ (radiusB x:ℝ) := Nat.le_ceil _; nlinarith
 change f-_≤ _; calc
 _ ≤ f+Q*e x:=by change |Real.log (spare Z b)|≤ Q* e x at hp; linarith only [(abs_le.mp hp).1] -- whitespace
 _ ≤ _:=by nlinarith only [mul_le_mul_of_nonneg_left (lscale_one x) h0,mul_le_mul_of_nonneg_left (show e x ≤2*lscale x from add_le_add (lscale_one x) ht |>.trans_eq (by ring)) hQ]
omit p
lemma rain (K:ℝ→ℝ)(h:PL K):∀ᶠ x in atTop,∀ b∈Set.Icc (x/2) (2*x),K x ≤ b*daily C (temp x):=by
 have he:Tendsto (fun x=> K x*((drift x)^(2:ℝ))⁻¹) atTop (𝓝 0):= (h.times (npl_drift _ (by norm_num))).drop
 have hx:=C.tail_pos
 filter_upwards [he.eventually (ge_mem_nhds (half_pos hx)),eventually_gt_atTop (0:ℝ)] with x p n' b v -- x missing variable due Lean notation; tune
 let a':=temp x; let d':=drift x; have h':0<d':= drift_pos _
 apply le_trans (b:=(C.linear/2)*d'^2)
 · rw [← div_le_iff₀ (pow_pos h' _)]; rw [div_eq_mul_inv]; change K x * _ ≤ _ at p; simpa only [show (drift x ^ (2:ℝ))=d'^2 from (by unfold d'; norm_num)] using p -- inspect
 rw [← xt_squared n' ]; unfold daily; nlinarith only [mul_le_mul_of_nonneg_right v.1 (mul_nonneg hx.le (sq_nonneg (temp x)))]
lemma fee_window (s:0<θ)(t:0<σ)(ε:ℝ)(v:0<ε): ∀ᶠ x in atTop, ∀ b∈Set.Icc (x/2) (2*x),∀ n:Side, fee₁ n C L b X D θ (screen x) σ (temp x) (melt x)≤ ε*bulk n:=by
 let k:=(Fintype.card PlaqAxes:ℝ); let h(x:ℝ):=vault_fee C L X θ (screen x) σ (melt x); let f(x:ℝ):= (x*h x)*k + (x*temp x^3*(2*|X|) + x*temp x^4*(2*|X|)+ |D| *(temp x*temp x)); have hf:Tendsto f atTop (𝓝 0):= (( (incline_r C L X θ t).mul (PL.const k)).add (((npl_three.mul (PL.const _)).add (npl_four.mul (PL.const _))).add ((npl_temp.mul npl_temp.pl).const_mul _))).drop -- pow_two vs temp*temp adjust
 filter_upwards [hf.eventually (ge_mem_nhds v),eventually_gt_atTop (0:ℝ)] with x w p b z n
 have hp:=BPress.temp_pos p; have hP:0≤bulk n:= Nat.cast_nonneg _; have hB:0<b:=lt_of_lt_of_le (half_pos p) z.1
 have hg: (Fintype.card (Plane n):ℝ)= bulk n*k:=by unfold Plane Face; rw [Fintype.card_prod,Nat.cast_mul]; -- need rfl?
 let K:=temp x; have he:0 ≤ h x:=by unfold h vault_fee; positivity [C.quadratic_pos]
 apply le_trans _ (mul_le_mul_of_nonneg_right w hP); unfold fee₁ taxY; have hu:bulk n=n.val^4:=by unfold bulk; rw [site_card]; push_cast; rfl -- casts
 rw [hg,← hu]; calc
 _ ≤ (k*h x/2 + |X| *K^3+|X| *K^4)* b * bulk n+ |D| *K^2 * bulk n:=by
    nlinarith only [mul_le_mul_of_nonneg_right (le_abs_self X) (mul_nonneg (mul_nonneg hB.le (pow_nonneg hp.le 3)) hP),mul_le_mul_of_nonneg_right (le_abs_self X) (mul_nonneg (mul_nonneg hB.le (pow_nonneg hp.le 4)) hP),mul_le_mul_of_nonneg_right (le_abs_self D) (mul_nonneg hP (pow_nonneg hp.le 2))]
 _ ≤ (k*h x/2 + |X| *K^3+ |X| * K^4)*(2*x)*bulk n+ |D| *K^2 * bulk n:= by
    have h₀:0≤ k:=Nat.cast_nonneg _; have h':0 ≤ k*h x/2+|X| *K^3+ |X| * K^4:=by have v0:0<K:=hp; positivity
    gcongr; exact z.2
 _ = _:=by unfold f; ring
end YM.Hill.Post
#print axioms YM.Hill.Post.fee_window
