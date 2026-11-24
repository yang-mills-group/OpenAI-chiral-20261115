import LusterS.Bruin
import Refrain.Shrift
import Refrain.Kernel
/-! # Sparse defect treatment under outer-threshold tree purchase -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.flexible false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Gleam.Luster
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ v' ν θ ω':ℝ}{U:Config G n}{A:Support c}{m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
variable {X Y:fieldDir G n 1}{D:Finset (Cell n)}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)(D':LocalRatio J)
namespace Almanac
open Grade
open CF.BProof
local notation "N" x:max=>height x -- clocks
open clocks
local notation "Xc" x:max=> ((x:ℝ)^(-tauA))
local notation "Yc" x:max=> ((x:ℝ)^(-yieldA))
abbrev canvas (A:ℝ)(x:ℝ):=hallBill (radiusB x) -- actually ℕ
def subsidyRa (A:ℝ)(x:ℝ):= 4*(A*(radiusB x:ℝ))*8*(hallBill (radiusB x):ℝ)+Real.log 2
lemma upward (A:ℝ)(x:ℝ)(p:0≤A): 0 ≤ subsidyRa A x:=by unfold subsidyRa; have he:=Real.log_nonneg (show (1:ℝ)≤2 by norm_num); positivity
lemma horizon_pl (A:ℝ): PL (fun x=>(canvas A x:ℝ))∧PL (subsidyRa A):=by
 let b:=radius_log
 unfold subsidyRa hallBill; push_cast
 let d:=b.add (PL.const 4); let e:=d.add d
 constructor; · unfold canvas hallBill Sequest; push_cast; exact e
 unfold Sequest; push_cast; exact (((((PL.const 4).mul ((PL.const A).mul b)).mul (PL.const 8)).mul e).add (PL.const _))
lemma plaster_area (A:ℝ)(p:0<A): ∀ᶠ x:ℝ in atTop,∀ w:Side,Odd w.val → cliffs x ≤ w.val → canvas A x≤ w.val/2 ∧ 4*(A*(radiusB x:ℝ))*(largerBill w.val (canvas A x):ℝ)+Real.log 2≤ x^(-(tauA/2))*(w.val:ℝ)^4 :=by
 let CA (x:ℝ):=canvas A x
 let a:=tauA/2
 have ha:0<a:=by norm_num [a,tauA]
 have he:= (((fromLog (horizon_pl A).1).scaleB (2:ℝ)).cost_p (b:=tauA) (by norm_num [tauA])); have hg:=((fromLog (horizon_pl A).2).cost_p ha)
 filter_upwards [he,hg,eventually_gt_atTop (0:ℝ)] with x h hg hx w hp hw
 let u:ℝ:=w.val
 have hu:(1:ℝ)≤u:=by unfold u; exact_mod_cast w.property
 have hf:glorio x≤ u:= (Nat.le_ceil _).trans ((Nat.cast_le (α:=ℝ)).mpr hw)
 have hc:(2:ℕ)*CA x ≤ w.val:=by
    have h':(2:ℝ)*(CA x:ℝ)≤glorio x:= (le_abs_self _).trans h
    have he: (2:ℝ)*(CA x:ℝ)≤(w.val:ℝ):=h'.trans hf
    exact_mod_cast he
 have hv:canvas A x≤w.val/2:=by change CA x≤_; omega
 refine ⟨hv,?_⟩
 have hr:=wall_cheap hp hv
 let t:ℝ:= A*(radiusB x:ℝ); have ht:0≤t:=by unfold t; positivity
 let b:= subsidyRa A x
 let m:=Real.log 2; have hm:0 ≤ m:=Real.log_nonneg (by norm_num)
 have hy: x^a≤ x^(-a)*u:=by
    refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left hf (Real.rpow_nonneg hx.le (-a)))
    unfold glorio; rw [← Real.rpow_add hx]; congr 1; unfold a; ring
 calc
    _ ≤ 4*t*(8*(canvas A x:ℝ)*u^3)+m:=by gcongr
    _ ≤ b*u^3:=by
       have hZ:= mul_le_mul_of_nonneg_left (one_le_pow₀ hu (n:=3)) hm; unfold b t m subsidyRa canvas at *; first|linarith only [hZ] -- b coef as above; check hZ type
    _ ≤ x^a*u^3:= mul_le_mul_of_nonneg_right ((le_abs_self _).trans hg) (by positivity)
    _ ≤ x^(-a)*(w.val:ℝ)^4:= (mul_le_mul_of_nonneg_right hy (by positivity:0≤u^3)).trans_eq (by unfold u; ring)

-- normalized tax all payments at target rate
abbrev frostRa (L:Side)(q:Clip)(R:Rules G)(η C S:ℝ)(x:ℝ):ℝ := 2*x*(C*temp x^3+C*temp x^4)+S*temp x^2 + (Fintype.card PlaqAxes:ℝ)*(2*x*Δ₁ R q (tuition L x) (radiusB x) η C)
lemma bill_land (L:Side)(k: Clip)(h: β ≤ 2*v)(e:p.threshold=temp v)(R:Rules G)(g:0 ≤ C)(f:0 < v)(hp:0≤tuition L v) : taxΔ R k n p β (tuition L v) η C S (radiusB v)≤ (frostRa L k R η C S v)*(Fintype.card (Site n):ℝ):=by
 have hv:= Δ_pos (q:=k) (R:=R) (m:=height v) (η:=η) hp g
 have hk:= Work.E04.temp_nonneg v
 unfold frostRa taxΔ CF.Graph.taxY; rw [show Fintype.card (Cell n)= Fintype.card (Site n)*Fintype.card PlaqAxes from Fintype.card_prod .., Nat.cast_mul, site_card,e]; push_cast
 nlinarith only [mul_le_mul_of_nonneg_right h (show 0 ≤ (n.val:ℝ)^4*(C*temp v^3+C*temp v^4) by positivity),mul_le_mul_of_nonneg_right h (show 0 ≤ (n.val:ℝ)^4*(Fintype.card PlaqAxes:ℝ)* _ from mul_nonneg (by positivity) hv)]
lemma frost_pr (L:Side)(k:Clip)(R:Rules G)(η C S:ℝ)(u:0<η):Grade (-1/5) (frostRa L k R η C S):=by
 let a:ℝ:= -1/5; have he:=temp_b
 have hv:= ((ΔGrade L R k η C u).mul x_id).scaleB (Fintype.card PlaqAxes*2:ℝ)
 have hT:= Grade.mul (x_id.scaleB 2) (((he.pwr 3).scaleB C).plus (((he.pwr 4).scaleB C).grow (by norm_num)))
 refine ((hT.grow (b:=a) (by norm_num [a])|>.plus (((he.pwr 2).scaleB S).grow (by norm_num [a]))).plus ?_)
 apply Grade.cash (hv.grow (b:=a) (by norm_num [a])); filter_upwards with x; apply le_of_eq; congr 1; change (Fintype.card PlaqAxes:ℝ)*(2*x*_)=(Fintype.card PlaqAxes*2:ℝ)*(_*id x); unfold id; ring
lemma snow_per: Grade (-1) (fun x=>Real.exp (-(radiusB x:ℝ))):=by have he:= trail_b (η:=1) (by norm_num); simp only [trail, neg_mul, one_mul] at he; exact he
lemma total_tax (L:Side)(R:Rules G)(q:Clip)(η C S:ℝ)(p:0<η): ∀ᶠ x:ℝ in atTop, frostRa L q R η C S x+4* Xc x + x^(-(tauA/2)) + Real.exp (-(radiusB x:ℝ))*(Fintype.card PlaqAxes:ℝ) ≤ Yc x:=by
 let a:= -(tauA/2)
 have hh:=((frost_pr L q R η C S p).grow (b:=a) (by norm_num [tauA,a]) |>.plus (((pitch (-tauA)).scaleB 4).grow (by norm_num [tauA,a]))|>.plus (pitch a) |>.plus ((snow_per.scaleB (Fintype.card PlaqAxes:ℝ)).grow (by norm_num [tauA,a])))
 filter_upwards [hh.cost_p (b:=-yieldA) (by norm_num [yieldA,tauA,a])] with x hp
 rw [mul_comm (Real.exp _)]
 exact (le_abs_self _).trans hp
end Almanac
end YM.Gleam.Luster
