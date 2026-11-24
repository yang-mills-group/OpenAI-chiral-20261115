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
lemma votes (death a:ℝ)(n:Side) : rebateB death (Real.exp (-death)*(Fintype.card PlaqAxes:ℝ)) a n:=by
 -- variation of Hill.Crete.revenue
 let E:= Real.exp (-death); let W:= Real.exp a; let Q:= Fintype.card (Cell n)
 have he:∑ S:Finset (Cell n), Real.exp (a - death*S.card)= W * (E+1)^Q:=by
    unfold W; simp_rw [show ∀ b:ℕ, a - death*b=a+b*(-death) from fun b=>by ring, Real.exp_add,Real.exp_nat_mul,←mul_sum];rw [show (E+1)^Q=∑ S:Finset (Cell n),E^S.card from ?_]; exact (by simpa only [prod_const,card_univ,mul_one,prod_const_one,one_pow] using Fintype.prod_add (fun (_:Cell n)=>E) (fun _=>1))
 unfold rebateB; rw [he,Real.exp_add a]; apply mul_le_mul_of_nonneg_left _ (Real.exp_pos a).le; calc
 _ ≤ Real.exp E ^ Q := pow_le_pow_left₀ (by unfold E; positivity) (Real.add_one_le_exp _) _
 _ = _ := (Real.exp_nat_mul ..).symm
 _ = _ := by unfold Q; rw [show Fintype.card (Cell n) = _ from Fintype.card_prod (Site n) PlaqAxes]; push_cast; congr 1; unfold E; ring
lemma agenda_cost : ∀ᶠ x:ℝ in atTop,∀ n:Side, ∀ a:ℝ, rebateB (deathC x) (meterC x) a n:=by
 let F(x:ℝ):= Real.exp (-deathC x); have he:Worth.Pays r_age 0 0 F:=by unfold F deathC; simpa only [one_mul] using damp 1 zero_lt_one r_age 0 0
 filter_upwards [leap (p:=0) (q:=0) (Pays.right (Fintype.card PlaqAxes :ℝ) he) (Or.inl (by norm_num [r_meter,r_age]:r_age<r_meter))] with x hx n a
 exact (votes (deathC x) a n).trans (Real.exp_monotone (add_le_add_right (mul_le_mul_of_nonneg_right hx (Nat.cast_nonneg _)) _)) -- orientation rebateB unfolds?
lemma levy_width : Worth.Pays 0 0 2 (fun x=> (hallBill (radiusB x):ℝ)):=by
 unfold hallBill Sequest; push_cast; have ht:= merit (constant 4) (w:=0) (p:=0) (q:=2) (by simp [Earlier]); exact plus (plus rising ht) (plus rising ht)
lemma outside_reserve (L:Side) (v:ℝ)(D:LocalRatio J)(h:0≤v): ∀ᶠ x:ℝ in atTop, ∀ β:ℝ, x/2 ≤ β → β ≤ 2*x → let C:= descendCost J β v (healthC x); let H:= hallBill (radiusB x); ∀ w:ℕ, Odd w → respire x L w →
    H ≤ w/2 ∧ 4*C*(w:ℝ)^4≤gateC x∧ 4*C*(Regis.Head.coldBill H:ℝ) + deathC x ≤ droitC x ∧ 4*C*(largerBill w H) + Real.log 2 ≤ meterC x*(w:ℝ)^4:=by
 obtain ⟨A,hA,hX⟩:= margin_fee J D v h
 let X(x:ℝ):= A*(radiusB x) + (Fintype.card G.ColorIndex:ℝ)/2+healthC x
 let W(x:ℝ):= (L.val:ℝ)*((terrace x).val:ℝ)
 let H(x:ℝ):=(hallBill (radiusB x):ℝ)
 have he:Worth.Pays 0 1 0 X:= plus (merit (plus (Pays.scale _ rising) (merit (constant _) (w:=0) (p:=0) (q:=2) (by norm_num [Earlier]))) (by norm_num [Earlier])) (whole ..)
 have hv(x): 0≤X x:=by unfold X; have h:0≤healthC x:=(coin_pos ..).le; positivity
 let SX:= Pays.scale 4 he
 have hf: Worth.Pays 0 0 8 (fun x=> (Regis.Head.coldBill (hallBill (radiusB x)):ℝ)):=by
    unfold Regis.Head.coldBill; push_cast; convert pot (plus (plus levy_width levy_width) (merit (constant 1) (w:=0) (p:=0) (q:=2) (by norm_num [Earlier]))) 4 using 1 <;> norm_num
 have hw:Worth.Pays r_width 0 0 W:= Pays.scale (L.val:ℝ) terrace_size
 have hl:Worth.Pays 0 1 8 (fun x=>4* X x*(Regis.Head.coldBill (hallBill (radiusB x)):ℝ)+deathC x):=by
    apply plus; · simpa only [zero_add,add_zero] using times SX hf
    exact merit rising (by norm_num [Earlier]) -- fix
 have hp:Worth.Pays 0 1 2 (fun x=>4*X x*(8*H x)+Real.log 2):=by
    apply plus; · simpa only [zero_add,add_zero] using times SX (Pays.scale 8 levy_width)
    exact merit (constant _) (by norm_num [Earlier])
 filter_upwards [hX, leap (Pays.scale 2 levy_width) (Or.inl (by norm_num [r_width] : (0:ℝ)<r_width)) (p:=0) (q:=0), leap (times SX (pot hw 4)) (Or.inl (by norm_num [r_gate,r_width]: _ < r_gate)) (p:=0) (q:=0), leap (p:=3/2) (w:=0) (q:=0) hl (by norm_num [Earlier]), leap (p:=0) (w:=r_meter+r_width) (q:=0) hp (by norm_num [Earlier,r_meter,r_width])] with x h h0 b1 b2 a2 β v1 v2 C H' w t p
 have hy:0<(w:ℝ):= (Nat.cast_pos.mpr (terrace x).property).trans_le (Nat.cast_le.mpr p.1); have h1:widthC x ≤ (w:ℝ):= (terrace_mm x).trans (Nat.cast_le.mpr p.1); have hθ:2*H'≤ w:=Nat.cast_le (α:=ℝ).mp (by push_cast; exact h0.trans h1); have hθ': H'≤w/2:= Nat.le_div_iff_mul_le (k:=2) (by decide)|>.mpr (by rwa [mul_comm]) -- tune
 have hz:C≤ X x:= add_le_add_left (add_le_add_left (h _ v1 v2) _) _; have hl:(w:ℝ)≤ W x:= by unfold W; exact_mod_cast p.2
 refine ⟨hθ',?_ , ?_,?_⟩
 · apply le_trans _ b1; change _ ≤ 4 * X x * W x^4; have he:= hv x; gcongr
 · refine le_trans ?_ b2; change _ ≤ 4 * X x * _ +_; gcongr
 let w':ℝ:=w; let M:=meterC x; have hh:0 ≤ M:= (coin_pos ..).le
 have hg:4*X x*(8*H x) +Real.log 2≤ M*w':= le_trans (a2.trans_eq (show coin x (r_meter+r_width) 0 0=M*widthC x by unfold M meterC widthC; rw [coin_mul,zero_add])) (mul_le_mul_of_nonneg_left h1 hh)
 calc _ ≤ 4*X x*(largerBill w H')+Real.log 2:= by gcongr
      _ ≤ 4*X x * (8*H x*w'^3)+ Real.log 2*w'^3:=by
         have hp: 1≤ w':= Nat.one_le_cast.mpr (Nat.pos_of_ne_zero (by exact_mod_cast hy.ne')); apply add_le_add (mul_le_mul_of_nonneg_left (wall_cheap t hθ') (show (0:ℝ) ≤4*X x from mul_nonneg (by norm_num) (hv x))) (le_mul_of_one_le_right (Real.log_nonneg (by norm_num)) (one_le_pow₀ hp));
      _ ≤ _ := by change _ ≤ M*w'^4; nlinarith only [mul_le_mul_of_nonneg_right hg (pow_nonneg (show 0≤w' from hy.le) 3)]
end YM.Gleam.Tempest
#print axioms YM.Gleam.Tempest.agenda_cost
#print axioms YM.Gleam.Tempest.outside_reserve
