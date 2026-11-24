import YM.SU5.Regis.Archive
import YM.SU5.Thin.Press.Lilt
import YM.SU5.Thin.Glacier.Layer
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
open Sleigh Paddled
-- bigger tiles. nearest L-powers scaled
abbrev averge (x:ℝ):= x^(1/200:ℝ)
def starSpan (x:ℝ)(w:ℕ)(L:Side): Prop:= averge x ≤ w ∧ (w:ℝ) ≤ (2*L.val:ℝ)* averge x
abbrev outerMark (x:ℝ):=x^(-(45/100:ℝ))
abbrev scant (x:ℝ):= x^(-(2/5:ℝ))
abbrev ledge (x:ℝ):=x^(3/100:ℝ)
-- weak polynomial multiplied if needed for a given measure, concrete exponent big
abbrev grain (x:ℝ):= B x ^60
abbrev oar (x:ℝ):= x^(-(1/500:ℝ))
lemma shiny (x:ℝ)(p:0<x): 0<averge x:= Real.rpow_pos_of_pos p _
lemma shinyH (x:ℝ)(p:0<x): 0<scant x∧ 0< outerMark x∧ 0<ledge x∧ 0<oar x:=⟨Real.rpow_pos_of_pos p _,Real.rpow_pos_of_pos p _,Real.rpow_pos_of_pos p _,Real.rpow_pos_of_pos p _⟩ -- unused
lemma scan_earned (R:Rules G)(q:Clip)(p:0<η): Paddled (-(11/10:ℝ)) (fun x=> Δ₁ R q (scant x) (height x) η C):=by
 let t:=scant; let b:=height; let f(x):=(b x:ℝ)
 have hT: Paddled (-(2/5:ℝ)) t:= park _; have h₂:= hT.power 2
 have hF:Paddled (1/20:ℝ) f:=by simpa only [pow_one] using radpay (by norm_num : (0:ℝ)<1/20) 1
 have hz₀:Paddled (-(4/5:ℝ)) (fun x=> faceCutError R (t x)):=by unfold faceCutError; apply (h₂.scale _).agrees; norm_num
 have hw:Paddled (-(3/4:ℝ)) (fun x=> slotError R (b x) (t x)):=by unfold slotError; refine (hz₀.up (by norm_num : -(4/5:ℝ)≤ -(3/4:ℝ))).add (((hF.scale _).mul h₂).agrees (by norm_num))
 have hv:Paddled (-(1:ℝ)) (fun x=>trail η (b x)):=by apply singers; filter_upwards [tail_gone (G:=G) η p] with x h; rw [abs_of_pos (show 0<trail η (b x) from Real.exp_pos _),Real.rpow_neg_one]; exact h
 have hb:Paddled 0 (fun x=> 2+4*(2*t x)):= (lake 2).add (((hT.scale 2).scale 4).up (by norm_num))

 have hz:Paddled (-(3/4:ℝ)) (fun x=> acry R (t x) (b x) η C):= (hw.add ((hb.mul hv).up (by norm_num))).scale C
 unfold Δ₁; refine Paddled.add (( (((hz₀.mul ((hT.scale _).scale _)).scale q.direct)).up (by norm_num)).add ((hz.mul (((hT.scale _).scale _).scale C)).up (by norm_num))) ?_; simp_rw [div_eq_mul_inv,mul_comm _ ((2:ℝ)⁻¹)]
 exact ((( (((((hT.scale _).scale 4).mul hv)).scale C).power 2)).scale _).up (by norm_num) -- parentheses `4*(2*t*trail)`? Δ actual `(C*(4*(2*v)*trail...` parses `(4*(2*v))*trail` -> adjust
-- normalized
abbrev standardChip (q:Clip)(L:Side)(R:Rules G)(η C S x:ℝ):ℝ:=2*x*(C*temp x^3+C*temp x^4)+ S*temp x^2 + (Fintype.card PlaqAxes:ℝ)*(2*(x*Δ₁ R q (scant x) (height x) η C))
lemma chipFuel (L:Side)(k: Clip)(h: β ≤ 2*v)(e:p.threshold=temp v)(R:Rules G)(g:0 ≤ C)(f:0 ≤ v): taxΔ R k n p β (scant v) η C S (height v)≤ (standardChip k L R η C S v)*(Fintype.card (Site n):ℝ):=by
 have hv:= Δ_pos (q:=k) (R:=R) (m:=height v) (η:=η) (Real.rpow_nonneg f (-(2/5:ℝ))) g; let W:=Δ₁ R k (scant v) (height v) η C
 have hk:= Work.E04.temp_nonneg v
 unfold standardChip taxΔ CF.Graph.taxY; rw [show Fintype.card (Cell n)= Fintype.card (Site n)*Fintype.card PlaqAxes from Fintype.card_prod .., Nat.cast_mul, site_card,e]; push_cast
 let k:=Fintype.card PlaqAxes
 nlinarith only [mul_le_mul_of_nonneg_right h (show 0 ≤ (n.val:ℝ)^4*(C*temp v^3+C*temp v^4) by positivity),mul_le_mul_of_nonneg_right h (show 0 ≤ (n.val:ℝ)^4*(Fintype.card PlaqAxes:ℝ)* _ from mul_nonneg (by positivity) hv)]
lemma chipTreasury(q:Clip)(L:Side)(p:0<η)(g:0≤C)(R:Rules G)(S:ℝ): Paddled (-(1/10:ℝ)) (standardChip q L R η C S):=by
 have hp:Paddled 1 (fun x:ℝ=> x):= by simpa only [Real.rpow_one] using park 1
 have ht:Paddled (-(2/5:ℝ)) temp:=(tempay (by norm_num:(0:ℝ)<1/10)).agrees (by norm_num)
 apply Paddled.add _ (((hp.mul (scan_earned (C:=C) R q p)).scale 2|>.scale (Fintype.card PlaqAxes)).agrees (by norm_num)) -- maybe no unfold
 exact Paddled.add ((((hp.scale 2).mul (Paddled.add ((ht.power 3).scale C) ((((ht.power 4).scale C).up (by norm_num))))).up (by norm_num))) (((ht.power 2).scale S).up (by norm_num))
end clocks

end YM.Gleam