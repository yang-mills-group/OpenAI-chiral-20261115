import YM.SU5.Gleam.Menhir
/-! # Growth estimates on all components, Δ cost. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Gleam
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ:ℝ}{U:Config G n}{A:Support c}{m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
namespace clocks
open Work.E09 AnalyticBridge.Annulus1AD
local notation "B" x:max=> (height x:ℝ)
lemma Δ_pos (v':0 ≤ v)(h:0≤C) : 0≤Δ₁ R q v m η C:=by
 unfold Δ₁; have he :0 ≤ faceCutError R v:=by unfold faceCutError; have v:= G.colorScale_pos; have u:=R.positive; positivity
 have := q.quadratic_pos; have hf := acry_zero (R:=R) (m:=m) (η:=η) h v'; positivity
lemma surge (L:Side)(x:ℝ)(hx:0≤x):0≤pace L x:=by have ht:=Work.E04.temp_nonneg x; unfold pace; positivity
lemma Δ_area (q:Clip)(R:Rules G)(L:Side)(hp:0<η)(h:0≤C) : Tendsto (fun x:ℝ=>x*Δ₁ R q (pace L x) (height x) η C) atTop (𝓝 0):=by
 let a:=G.colorScale; let Y:= 16*a+4*R.C; let p:= pace L; let v(x:ℝ):=x*p x^3; let W:= q.direct *8*Y +8*C^2*Y; let D(x:ℝ):=W*v x+(64*C^2*a)*(B x*v x)+(8*C^2*p x)*(2+8*p x) +32*C^2*(p x)^2*x⁻¹
 have h0:Tendsto p atTop (𝓝 0):= by simpa using heel L 0
 have hv:Tendsto v atTop (𝓝 0):= by simpa only [pow_zero,one_mul] using pillar L 0
 have hb:Tendsto (fun x=> B x*v x) atTop (𝓝 0):= by simpa only [pow_one] using pillar L 1
 have hw:Tendsto D atTop (𝓝 0):= by simpa using ((hv.const_mul W).add (hb.const_mul (64*C^2*a)) |>.add ((h0.const_mul (8*C^2)).mul (tendsto_const_nhds (x:=2) |>.add (h0.const_mul 8))) |>.add (((h0.pow 2).const_mul (32*C^2)).mul tendsto_inv_atTop_zero))
 refine squeeze_zero' ?_ ?_ hw
 · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx; exact mul_nonneg hx.le (Δ_pos (surge L x hx.le) h)
 filter_upwards [eventually_gt_atTop (0:ℝ),tail_gone (G:=G) η hp] with x hx k
 let X:=p x; let J:= B x; let V:=trail η (height x); let F(z:ℝ):= x*(q.direct*(faceCutError R X * (4*(2*X))) + (C*(slotError R (height x) X + (2+4*(2*X))*z))*(C*(4*(2*X))) + (C*(4*(2*X)*z))^2/2)
 have hz:0≤ V:= (Real.exp_pos _).le; have ha:0≤X:= surge L _ hx.le
 refine (show _= F V from rfl).trans_le (le_trans (show F V ≤ F x⁻¹ from ?_) (le_of_eq ?_))
 · unfold F; gcongr
 unfold D F v X W Y a slotError faceCutError; field_simp; ring
-- taxY n etc normalized
abbrev simpleTax (q:Clip)(L:Side)(R:Rules G)(η C S x:ℝ):ℝ:=2*x*(C*temp x^3+C*temp x^4)+ S*temp x^2 + (Fintype.card PlaqAxes:ℝ)*(2*(x*Δ₁ R q (pace L x) (height x) η C))
lemma shown (q:Clip)(R:Rules G)(L:Side)(hp:0<η)(h:0≤C) (S:ℝ) : Tendsto (simpleTax q L R η C S) atTop (𝓝 0) :=by
 have hx : Tendsto (fun x:ℝ=> x*temp x^3) atTop (𝓝 0):= by simpa using cubic 0
 have hs:Tendsto temp atTop (𝓝 0):= by simpa using Work.E09.radiusB_temp 0
 let A:=Fintype.card PlaqAxes; have V:= (hx.const_mul (2*C)).add ((hx.mul hs).const_mul (2*C)) |>.add ((hs.pow 2).const_mul S) |>.add ((Δ_area q R L hp h).const_mul (2*(A:ℝ)))
 simp only [mul_zero,zero_add,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow] at V; apply V.congr; intro x; unfold simpleTax A; ring
lemma bill_simpl (L:Side)(k: Clip)(h: β ≤ 2*v)(e:p.threshold=temp v)(R:Rules G)(g:0 ≤ C)(f:0 ≤ v): taxΔ R k n p β (pace L v) η C S (height v)≤ (simpleTax k L R η C S v)*(Fintype.card (Site n):ℝ):=by
 have hv:= Δ_pos (q:=k) (R:=R) (m:=height v) (η:=η) (surge L v f) g; let W:=Δ₁ R k (pace L v) (height v) η C
 have hk:= Work.E04.temp_nonneg v
 unfold simpleTax taxΔ CF.Graph.taxY; rw [show Fintype.card (Cell n)= Fintype.card (Site n)*Fintype.card PlaqAxes from Fintype.card_prod .., Nat.cast_mul, site_card,e]; push_cast
 let k:=Fintype.card PlaqAxes
 nlinarith only [mul_le_mul_of_nonneg_right h (show 0 ≤ (n.val:ℝ)^4*(C*temp v^3+C*temp v^4) by positivity),mul_le_mul_of_nonneg_right h (show 0 ≤ (n.val:ℝ)^4*(Fintype.card PlaqAxes:ℝ)* _ from mul_nonneg (by positivity) hv)]
end clocks
end YM.Gleam
#print axioms YM.Gleam.clocks.Δ_area
