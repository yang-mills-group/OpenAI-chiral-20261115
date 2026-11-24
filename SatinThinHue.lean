import SatinThinCivil
import SatinThinRent

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
abbrev r_age :ℝ:=-(47/100)
abbrev ageC(x:ℝ) := coin x r_age 0 0
abbrev healthC(x:ℝ) := scaleY x
abbrev deathC(x:ℝ) :ℝ:= radiusB x
abbrev droitC(x:ℝ) := coin x 0 (3/2) 0
abbrev respire (x:ℝ)(L:Side)(w:ℕ): Prop:= (terrace x).val ≤ w ∧ w ≤ L.val*(terrace x).val

lemma flake_upper : ∀ᶠ x:ℝ in atTop,∀ (q':BudgetPoint) (β:ℝ), x/2≤ β → q'.threshold=temp x → droitC x ≤ β*unitDueS q q'/2:=by
 let A:= q.linear/8; have hs:0<A:=by unfold A; have h:=q.tail_pos; positivity
 filter_upwards [eventually_gt_atTop (0:ℝ),coin_budget (Or.inr (Or.inl (show (0:ℝ)=0 ∧ (3/2:ℝ)<2 from ⟨rfl,by norm_num⟩))) 1 A hs (c:=0) (f:=0)] with x hx h q' β hp hP
 let X:=temp x; let Y:=q'.threshold
 have ht: x* X^2=coin x 0 2 0:= by unfold X; rw [←thresh_eq hx,coin_pow]; nth_rw 1 [←coinY hx]; rw [coin_mul]; norm_num
 unfold droitC; rw [one_mul,←ht] at h; unfold A at h; unfold unitDueS; rw [hP]; unfold X at h; nlinarith only [h.le, mul_le_mul_of_nonneg_right hp (mul_nonneg q.tail_pos.le (sq_nonneg (temp x)))]
-- large allowance proof reuses same clock asymptotic, increasing coverage exponentially.
abbrev empress (q:Clip)(β x:ℝ):=β*(q.linear*temp x*shieldC x/2)/2
lemma rain_upper (q:Clip)(c:ℝ): ∀ᶠ x:ℝ in atTop,∀ β:ℝ, x/2≤β→ c*gateC x≤ empress q β x:=by
 let A:=q.linear/8; have hs:0<A:=(div_pos q.tail_pos (by norm_num)); let f:=1 + -(1/2:ℝ)+r_shield; have he:r_gate < f:= by norm_num [f,r_gate,r_shield]
 filter_upwards [eventually_gt_atTop (0:ℝ),coin_budget (b:=0) (c:=0) (e:=1) (f:=0) (Or.inl he) c A hs] with x hx h β v
 have hi:x* temp x * shieldC x = coin x f 1 0:=by unfold shieldC f; rw [←thresh_eq hx]; nth_rw 1 [←coinY hx]; rw [coin_mul,coin_mul]; norm_num
 unfold gateC; rw [←hi] at h; unfold empress; unfold A at h; nlinarith only [h.le, mul_le_mul_of_nonneg_right v (show 0 ≤ q.linear*temp x*shieldC x from mul_nonneg (mul_nonneg q.tail_pos.le (Work.E04.temp_nonneg _)) (coin_pos ..).le)]
lemma humid (L: Side): ∀ᶠ x:ℝ in atTop,∀ w:ℕ,respire x L w → suitedFee w (shieldC x) ≤ ageC x:=by
 let H(x:ℝ):=(L.val:ℝ)*(↑(terrace x).val:ℝ); let W(x:ℝ):=8*(H x)+1; have t:Worth.Pays r_width 0 0 H:= Pays.scale (L.val:ℝ) terrace_size
 have hu:= merit (constant 1) (p:=0) (q:=0) (Or.inl (by norm_num [r_width]: (0:ℝ)<r_width))
 have hz:= leap (times (plus (Pays.scale 8 t) hu) (times (Pays.scale 4 (whole r_shield 0 0)) (plus hu t))) (Or.inl (by norm_num [r_width,r_age,r_shield]: _ < r_age)) (p:=0) (q:=0)
 filter_upwards [hz] with x hx w hp
 let J:= healthC x; have hv:(w:ℝ) ≤ H x:= (Nat.cast_le (α:=ℝ).mpr hp.2).trans_eq (by unfold H; push_cast; rfl); unfold suitedFee; refine le_trans ?_ hx; have he:0 ≤ shieldC x:=(coin_pos ..).le; unfold shieldC; unfold H at *; gcongr

lemma level_s (q:Clip)(R:Rules G)(D:LocalRatio J)(L:Side): ∀ᶠ x:ℝ in atTop, ∀ w:ℕ, respire x L w→ ∀ (b:ℝ) (p:BudgetPoint) (κ k:ℝ), x/2≤ b → p.threshold=temp x → κ ≤ b*unitDueS q p/2 → k ≤ empress q b x → Accounts J R q p w (radiusB x) b (ageC x) (meterC x) (shieldC x) κ k (droitC x) (gateC x):=by
 have hX:Tendsto (ageC) atTop (𝓝 0):=coin_purchases (Or.inl (by norm_num [r_age]:r_age<0))
 obtain ⟨C,b,S,e,Z⟩:= SectorNext.Vacuum.ratio_measure_near J D
 filter_upwards [humid L, hX.eventually (gt_mem_nhds (show 0<R.c from R.radius)), hX.eventually (gt_mem_nhds (half_pos D.patch)), hX.eventually (gt_mem_nhds (half_pos e)), leap (Pays.scale (C*2) (whole r_age 0 0)) (p:=0) (q:=0) (Or.inl (by norm_num [r_meter,r_age]:r_age<r_meter)), flake_upper (q:=q), rain_upper q (21^4),clocks.parliament (G:=G) q,inner_shield] with x hV hp he hA v0 v1 v2 v3 v4 w t y p' μ v z h k hX'
 have hg:0≤ageC x:= (coin_pos ..).le; refine ⟨v3 _ h,hV _ t,h.symm ▸ v4.le,hp.le,by linarith only [he],fun j k=>?_, by linarith only [k,v1 p' y z h],?_,(coin_pos ..).le,(coin_pos ..).le⟩
 · have hh: ‖j‖≤S:=k.trans (by linarith only [hA]); let X:=ageC x; let m:=meterC x; have ht:C*(2*X)≤ m:=by rw [←mul_assoc]; exact v0
   exact le_trans (b:=m+1) (by nlinarith only [(abs_le.mp (Z j hh)).2,mul_le_mul_of_nonneg_left k b.le,ht]) (Real.add_one_le_exp _)
 unfold unitDueL; rw [h]; have hp:=(v2 y z); unfold empress at hp hX'; linarith only [hp,hX']
end YM.Gleam.Tempest
#print axioms YM.Gleam.Tempest.level_s
