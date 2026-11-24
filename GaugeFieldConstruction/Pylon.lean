import GaugeFieldConstruction.Thole
import GaugeFieldConstruction.Scone
/-! # Projection budgets for monomials on actual covariance space. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 25000
noncomputable section
namespace YM.Gleam.Guide
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix Module Regis Regis.Head ProbabilityTheory
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ:ℝ}{U:Config G n}{A:Support c}{o x z:Site n}{f m:ℕ} {X V D:Dir G n}{R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J: ChartRatio G}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)
open CF.BProof (coin coin_scale coin_mul coin_pow scaleY)
open CF.BProof.PricePort Gleam.clocks
open CF.Rue (FleetS shoreK)
open CF.Scree (pingS)
variable (s: Signed) {K:Support n}{W D':Flaws n}{E:T.Slice G}
local notation "Pz" x:max=> 2*Real.sqrt (2*x)*Pressure.temp x+1
abbrev Māt (x:ℝ):ℝ := Pz x
abbrev coos (x:ℝ):ℝ:=coin x 0 1 0
lemma temp_caps (x:ℝ)(v:0<x):Real.sqrt x*temp x=coos x:=by unfold temp coos coin; field_simp; simp
lemma coos_buy :∀ᶠ x:ℝ in atTop, coos x ≤ Māt x:=by
 filter_upwards [eventually_gt_atTop (0:ℝ)] with x p; unfold Māt; rw [← temp_caps x p]; have h : Real.sqrt x ≤ Real.sqrt (2*x):= Real.sqrt_le_sqrt (by linarith); nlinarith only [mul_le_mul_of_nonneg_right h (Work.E09.temp_pos p).le, mul_pos (Real.sqrt_pos.mpr p) (Work.E09.temp_pos p)]
lemma sqrt_fee : RunRate (1/2) 0 (fun x:ℝ=> Real.sqrt (2*x)):=by
 obtain ⟨d,h⟩:= ((RunRate.coins (1/2:ℝ) 0 0).cmul (Real.sqrt 2)); refine ⟨d,?_⟩; filter_upwards [eventually_gt_atTop (0:ℝ),h] with x p H
 change |Real.sqrt 2* Rrp (1/2) x| ≤ _ at H
 rw [Rrp_out _ x p, ← Real.sqrt_eq_rpow,← Real.sqrt_mul (by norm_num : (0:ℝ)≤2)] at H; exact H
lemma lensU : RunRate 0 1 Māt:= by
 let he:= sqrt_fee
 have hf : RunRate 0 1 (fun x=> 2*Real.sqrt (2*x)*temp x):=by convert (he.cmul 2).mul RunRate.temps using 1 <;> norm_num
 unfold Māt; exact hf.add ((RunRate.const 1).weaker (Or.inr ⟨rfl,zero_le_one⟩))
abbrev NovCut (x:ℝ) := Rrp (-3/8) x
lemma log_seed : ∀ᶠ x:ℝ in atTop, Real.log x ≤ coos x:=by
 -- use logs.PL
 simpa only [one_mul] using logPrice 0 0 CF.BProof.PL.log_y (w:=0) (d:=1) (c:=0) (by norm_num) one_pos
lemma lens_tail : RunRate (-1) 0 (fun x=> Real.exp ( -Māt x)):=by
 refine ⟨0,?_⟩; filter_upwards [coos_buy,log_seed,eventually_gt_atTop (0:ℝ)] with x v k p
 rw [abs_of_pos (Real.exp_pos _)]; apply (Real.exp_monotone (neg_le_neg (k.trans v))).trans_eq; change Real.exp _=Rrp (-1) x; rw [Real.exp_neg,Real.exp_log p,Rrp_out _ _ p,Real.rpow_neg p.le, Real.rpow_one]
variable (R)
lemma sunΔ (Q:Side)(c:ℕ): ∀ᶠ x:ℝ in atTop, suitCost Q x≤R.c ∧ Māt x ≥ 1 ∧ 0 ≤ suitCost Q x ∧ c ≤ clocks.height x ∧ ∀ b:ℝ,x/2≤ b→b≤2*x→Real.sqrt b* temp x+Real.sqrt b*slotError R c (suitCost Q x) ≤ Māt x ∧ Real.sqrt b*slotError R c (suitCost Q x) ≤ NovCut x:=by
 let V:=suitCost Q; let K:= Māt; let U(x):=slotError R c (V x); let Z(x):= Real.sqrt (2*x)*U x
 let v:= 8*gratuity-1/2
 have he:RunRate v 1 V:= tile_bill Q;
 have hg: RunRate ((2:ℕ)*v) (2*1) U:=by
    have hp(f:ℝ) : RunRate ((2:ℕ)*v) (2*1) (fun x=> f*V x^2):=by convert (he.pow 2).cmul f using 1 <;> push_cast <;> ring
    exact (hp _).add (hp _)
 have hz:RunRate (1/2+(2:ℕ)*v) (0+2*1) Z:= sqrt_fee.mul hg
 have hw : 1/2+(2:ℕ)*v<(-3/8):=by unfold v gratuity; norm_num
 filter_upwards [(he.tends (Or.inl (by unfold v gratuity; norm_num))).eventually (ge_mem_nhds R.radius),badge_ok,(hz.tends (Or.inl (lt_trans hw (by norm_num)))).eventually (ge_mem_nhds zero_lt_one),logPrice _ _ hz (w:=0) (c:= -3/8) (d:=0) (Or.inl hw) one_pos,eventually_gt_atTop 0,Work.E01.radiusB_tendsto.eventually_ge_atTop c] with x ht B hp z p t -- tune
 have h:0<temp x:=Work.E09.temp_pos p; have hv:0≤ badgeDust x:=h.le.trans B; have hh : 0≤tileN x:=(CF.BProof.coin_pos ..).le
 have hy:0 ≤ suitCost Q x:=by unfold suitCost; positivity
 have hh':0≤ U x:=by unfold U slotError faceCutError; change 0≤ (G.colorScale*16+R.C*4)* (suitCost Q x)^2+8*G.colorScale*(c:ℝ)*(suitCost Q x)^2; have ht:=R.positive; have hv:=G.colorScale_pos; positivity
 refine ⟨ht,le_add_of_nonneg_left (by positivity), hy,t, fun b v' l=>?_⟩
 have hr:=Real.sqrt_le_sqrt l
 have hx := (mul_le_mul_of_nonneg_right hr hh'); refine ⟨?_, hx.trans (show Z x≤ NovCut x from z.trans (le_of_eq (one_mul _)))⟩
 apply (add_le_add (mul_le_mul_of_nonneg_right hr h.le) (hx.trans hp)).trans; unfold Māt; linarith only [mul_nonneg (Real.sqrt_nonneg (2*x)) h.le]

end YM.Gleam.Guide
end
