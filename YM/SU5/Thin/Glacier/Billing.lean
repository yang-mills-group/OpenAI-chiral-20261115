import YM.SU5.Thin.Glacier.Responsive
import YM.SU5.Thin.Press.Lance
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
set_option maxHeartbeats 800000
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
open Sleigh Paddled

lemma suitBlast(L:Side):∀ᶠ x:ℝ in atTop,∀ w:ℕ,0<w → starSpan x w L → suitedFee w (outerMark x) ≤ scant x:=by
 let a:ℝ:= 2*L.val; have ha:0<a:=by unfold a; positivity; -- indentation
 let α(x:ℝ):= a*averge x; have hf:Paddled (1/200) α:= (park _).scale _
 have H := (((hf.scale 9).mul ( ((park (-(45/100:ℝ))).scale 4).mul (hf.scale 2)))).pure (b:=-(2/5:ℝ)) (by norm_num)
 filter_upwards [eventually_gt_atTop (0:ℝ),H] with x p g w u h
 have hv : (w:ℝ)≤ α x:= h.2; have ht:= shiny x p; have hw:1 ≤ (w:ℝ):= Nat.one_le_cast.mpr u; have he:0≤α x:= zero_le_one.trans (hw.trans hv); have hx:0<outerMark x:=(shinyH x p).2.1; change 9*α x*(4*outerMark x*(2*α x))≤ scant x at g
 apply g.trans'; unfold suitedFee; gcongr <;> linarith
lemma neckElection: ∀ᶠ x:ℝ in atTop, temp x ≤ outerMark x:= (tempay (by norm_num : (0:ℝ)<1/40)).pure (b:=-(45/100:ℝ)) (by norm_num)
lemma stamp_priced (q:Clip):∀ᶠ x:ℝ in atTop,∀ b:ℝ,x/2≤b → (grain x)+(grain x) ≤ b* (leaff q*temp x^2):=by
 let f:= leaff q; have hf:=leaf_p q; have h:0 < f:=hf
 filter_upwards [dust_money 60 (4/f) (by positivity),eventually_gt_atTop (0:ℝ)] with x p e b hp
 change 4/f *grain x ≤ _ at p; apply le_trans _ (mul_le_mul_of_nonneg_right hp (mul_nonneg h.le (sq_nonneg _))); field_simp at p; linarith only [p]
lemma slab_priced (q:Clip): ∀ᶠ x:ℝ in atTop,∀ b:ℝ, x/2≤b → (ledge x)+ (ledge x)*21^4 ≤ b * (q.linear/2 * temp x * outerMark x):=by
 let f:=q.linear; have hf:0<f:=q.tail_pos; have he:= ((park ((3:ℝ)/100)).add ((park ((3:ℝ)/100)).scale (21^4))).discounts (b:=1/20) (by norm_num) (div_pos hf (by norm_num:(0:ℝ)<4))
 filter_upwards [he,eventually_gt_atTop (0:ℝ)] with x p u β z
 let a(x:ℝ):=x^(-(1/2:ℝ)); let b:= outerMark x; have hx:b>0:= (shinyH x u).2.1; have hp: a x≤temp x:= by unfold a; rw [Real.rpow_neg u.le,←Real.sqrt_eq_rpow]; exact le_mul_of_one_le_right (by positivity) (Real.one_le_exp (sq_nonneg _))
 apply le_trans (b:=ledge x+21^4*ledge x) (le_of_eq (by ring)); apply le_trans ((le_abs_self _).trans p); have hz:temp x>0:= temp_pos u
 change f/4*x^(1/20:ℝ) ≤ β*(f/2*_ *b)
 calc _=(x/2)*(f/2* a x * b):=by
            rw [show x^(1/20:ℝ)=x*a x*b from ?_]; ring; unfold a b outerMark; nth_rw 2 [← Real.rpow_one x]; rw [←Real.rpow_add u,←Real.rpow_add u]; norm_num
      _ ≤ _:= by have hz:0≤β:= (half_pos u).le.trans z; have ht:0≤a x:=Real.rpow_nonneg u.le _; gcongr
lemma acrossM (R:Rules G)(J:ChartRatio G)(D:LocalRatio J): ∀ᶠ x:ℝ in atTop,scant x ≤ R.c ∧2*scant x<J.radius ∧ ∀ y:G.Color, ‖y‖≤2*scant x→ J.J y ≤ Real.exp ((1/12:ℝ)*oar x):=by
 let a:=J.radius/2; have ha:0<a:=half_pos D.patch; let v:=half_lt_self D.patch; obtain ⟨C,c,H⟩:= Sleigh.jacob D ha v
 have h:Paddled (-(2/5:ℝ)) scant:= park _; have hm:Tendsto scant atTop (𝓝 0):= h.lim (by norm_num)
 filter_upwards [hm.eventually (ge_mem_nhds R.radius),hm.eventually (ge_mem_nhds (half_pos ha)),(h.scale (2*C)).discounts (b:=-(1/500:ℝ)) (by norm_num) (by norm_num : (0:ℝ)<1/12)] with x z u r
 have hk:2*scant x ≤ a:=by linarith only [u]
 refine ⟨z,hk.trans_lt v,fun i g=>?_⟩
 have hp₀ : 2*C*scant x ≤ 1/12*oar x:= (le_abs_self _).trans r; apply le_trans _ (Real.add_one_le_exp _); linarith only [(abs_le.mp (H _ (g.trans hk))).2,hp₀,mul_le_mul_of_nonneg_left g c.le]
lemma fuelling (q:Clip)(L:Side)(D:LocalRatio J) (R:Rules G): ∀ᶠ x:ℝ in atTop,∀ w:ℕ,0<w→ starSpan x w L → ∀ (b:ℝ)(p:BudgetPoint), x/2 ≤ b → p.threshold=temp x → ArcChill J R q p w (height x) b (grain x) (ledge x) (scant x) ((1/12:ℝ)*oar x) (outerMark x) (ledge x) (grain x):=by
 filter_upwards [stamp_priced q, slab_priced q,neckElection, acrossM R J D, suitBlast L,parliament (G:=G) q,eventually_gt_atTop (0:ℝ)] with x hc ht hz ⟨hx,htp,hg⟩ v H x' w u h b p hb hp; refine ⟨H _ hp,v _ u h,hx,htp,hg,(by rw [hp]; exact ht _ hb),(by rw [hp]; exact hc _ hb),hp ▸ hz,(shinyH x x').2.2.1.le, mul_nonneg (by norm_num) (shinyH x x').2.2.2.le⟩
end clocks

end YM.Gleam