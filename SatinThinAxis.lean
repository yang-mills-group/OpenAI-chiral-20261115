import SatinThinHue

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
lemma acula (R:Rules G)(q:Clip) {η:ℝ} (t:0<η) (C:ℝ) : Worth.Pays (- 13/10) 0 0 (fun x=> Δ₁ R q (ageC x) (radiusB x) η C):=by
 let a:=ageC; let k:=r_age; let h(x:ℝ):=trail η (radiusB x); let D:= constant
 let F:=fun x=>faceCutError R (a x); have hx:Worth.Pays k 0 0 a:= whole ..; have hf:Worth.Pays (k*2) 0 0 F:=by
    unfold F faceCutError; apply Pays.scale; convert pot hx 2 using 1 <;> norm_num
 have hp:Worth.Pays (k*2) 0 0 (fun x=> a x ^ 2):=by convert pot hx 2 using 1 <;> norm_num
 have ht: Worth.Pays (-1) 0 0 h:=by
    simp_rw [h,trail,neg_mul]; exact damp η t _ _ _ -- dangerous `simp_rw h`
 have hh:Worth.Pays (k*2) 0 2 (fun x=> acry R (a x) (radiusB x) η C):=by
    let K:=slotError R; unfold acry; apply Pays.scale; refine plus ?_ ?_
    · unfold slotError; apply plus (merit hf (p:=0) (q:=2) (by simp [Earlier])); have hk:=times (Pays.scale (8*G.colorScale) rising) hp; simpa only [zero_add,add_zero] using hk
    have hb:=plus (constant 2) (merit (Pays.scale 4 (Pays.scale 2 hx)) (w:=0) (p:=0) (q:=0) (k:=by norm_num [Earlier,k,r_age])); exact merit (times hb ht) (by norm_num [Earlier,k,r_age])
 unfold Δ₁; apply plus
 · apply plus
   · apply merit (Pays.scale _ (times hf (Pays.scale 4 (Pays.scale 2 hx)))) (by norm_num [Earlier,k,r_age])
   apply merit (times hh (Pays.scale _ (Pays.scale 4 (Pays.scale 2 hx)))) (by norm_num [Earlier,k,r_age])
 simp_rw [div_eq_mul_inv _ (2:ℝ)]; exact merit (Pays.right _ (pot (Pays.scale _ (times (Pays.scale 4 (Pays.scale 2 hx)) ht)) 2)) (by norm_num [Earlier,k,r_age])

abbrev simpleRate (q:Clip)(R:Rules G)(η C S x:ℝ):ℝ:=2*x*(C*temp x^3+C*temp x^4)+ S*temp x^2 + (Fintype.card PlaqAxes:ℝ)*(2*(x*Δ₁ R q (ageC x) (radiusB x) η C))
lemma rate_aw (q:Clip)(R:Rules G)(hp:0<η)(S C:ℝ) : Worth.Pays (-3/10) 0 0 (simpleRate q R η C S):=by
 unfold simpleRate; apply plus; swap; · have hp:= Pays.scale (Fintype.card PlaqAxes :ℝ) (Pays.scale 2 (times Pays.height (acula R q hp C))); simp only [id_eq] at hp; convert hp using 1 <;> norm_num
 have ht: Worth.Pays (-1/2) 1 0 temp:= fix (whole ..) ((eventually_gt_atTop (0:ℝ)).mono fun _ hx=> thresh_eq hx)
 apply plus
 · have h3:= Pays.scale C (pot ht 3); have h4:=Pays.scale C (pot ht 4); have he:= times (Pays.scale 2 Pays.height) (plus h3 (merit h4 (by left; norm_num))); exact merit he (by norm_num [Earlier])
 apply merit (Pays.scale S (pot ht 2)) (by norm_num [Earlier])
lemma rate_long (q:Clip)(R:Rules G)(hp:0<η)(l:0≤C)(S:ℝ) : ∀ᶠ x:ℝ in atTop,∀ (p:BudgetPoint)(β:ℝ), β≤ 2*x→p.threshold=temp x→ ∀ n:Side,taxΔ R q n p β (ageC x) η C S (radiusB x) ≤ meterC x*(Fintype.card (Site n):ℝ):=by
 filter_upwards [leap (p:=0) (q:=0) (rate_aw q R hp S C) (Or.inl (by norm_num [r_meter] : (-3/10:ℝ)<r_meter)), eventually_gt_atTop (0:ℝ)] with x HX hh p β h e n
 apply le_trans ?_ (mul_le_mul_of_nonneg_right HX (Nat.cast_nonneg (Fintype.card (Site n)))) -- tune
 have ov :0 ≤ ageC x:=(coin_pos ..).le
 have hv:= Δ_pos (q:=q) (R:=R) (m:=radiusB x) (η:=η) ov l
 let W:=Δ₁ R q (ageC x) (radiusB x) η C
 have hk:= Work.E04.temp_nonneg x
 unfold simpleRate taxΔ CF.Graph.taxY; rw [show Fintype.card (Cell n)= Fintype.card (Site n)*Fintype.card PlaqAxes from Fintype.card_prod .., Nat.cast_mul, site_card,e]; push_cast
 nlinarith only [mul_le_mul_of_nonneg_right h (show 0 ≤ (n.val:ℝ)^4*(C*temp x^3+C*temp x^4) by positivity),mul_le_mul_of_nonneg_right h (show 0 ≤ (n.val:ℝ)^4*(Fintype.card PlaqAxes:ℝ)* _ from mul_nonneg (by positivity) hv)]
end YM.Gleam.Tempest
#print axioms YM.Gleam.Tempest.rate_long
