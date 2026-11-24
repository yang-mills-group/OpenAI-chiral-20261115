import Risa.Leaves
import Risa.Clamp
import Risa.Aurora
import YM.SU5.Regis.Hospitality
import Taffeta.Stigma
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
namespace Risa
open Regis ProbabilityTheory
open _root_.YM.Regis.Head AnalyticBridge.VerifiedReset StressFlux Lattice.PlaqAxes Virgo
local notation "D1" => CF.Compass.decor
private lemma decorV(i:PlaqAxes): |((CF.Compass.decor i:ℤ):ℝ)|≤1:=by unfold CF.Compass.decor; split_ifs <;> norm_num
/-- s exponent cap -/
structure Hike where
 cost: ℝ
 safe: 0<cost
variable (Xh:Hike) (G)
local notation "χ"=> Xh.cost
-- real mark on normalized curls. 
def viaduct (y: Stitch→G.Color):ℝ:= (∑ i:PlaqAxes,(D1 i:ℝ)*clipQ Xh.cost (floret G i y))/2
abbrev ridges:ℕ:= Fintype.card PlaqAxes
local notation "Γ"=> (ridges:ℝ)
lemma fundF (y:Stitch→G.Color): |viaduct G Xh y|≤ Γ*χ^2:=by
 unfold viaduct; rw [abs_div,abs_of_pos (show (0:ℝ)<2 by norm_num)]; apply (div_le_self (abs_nonneg _) one_le_two).trans ((Finset.abs_sum_le_sum_abs ..).trans ?_); refine (sum_le_sum (g:=fun _=> χ^2) (fun i _=>?_)).trans ?_
 · rw [abs_mul,abs_of_nonneg (clip_pos _ Xh.safe _)]; exact (mul_le_of_le_one_left (clip_pos _ Xh.safe _) (decorV _)).trans (clip_le _ Xh.safe _)
 rw [sum_const,card_univ,nsmul_eq_mul]
-- use library Fintype h
abbrev τw :ℝ:= Γ*2*χ
lemma tracksF (y t:Stitch→G.Color): |viaduct G Xh y-viaduct G Xh t|≤ τw Xh*‖y-t‖:=by
 unfold viaduct; rw [← _root_.sub_div,abs_div,abs_of_pos (show (0:ℝ)<2 by norm_num)]; refine (div_le_self (abs_nonneg _) one_le_two).trans ?_
 rw [← sum_sub_distrib]
 refine (Finset.abs_sum_le_sum_abs ..).trans ?_
 refine (sum_le_sum (g:=fun _=> (2*χ)*‖y-t‖) (fun i _=>?_)).trans ?_
 · rw [←mul_sub_left_distrib,abs_mul]; refine (mul_le_of_le_one_left (abs_nonneg _) (decorV _)).trans ((clip_lift _ Xh.safe ..).trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg zero_le_two Xh.safe.le)))
   rw [floret_sub]; exact floret_bound ..
 rw [sum_const,card_univ,nsmul_eq_mul]; rw [show (Fintype.card PlaqAxes:ℝ)=(ridges:ℝ) from rfl]; unfold τw; exact Eq.le (by ring)
def posess: Etch G Stitch:=by
 refine {slot:= ringT G,
         f:=viaduct G Xh
         arc:= (ridges:ℝ)*Xh.cost^2
         bound:=fundF G Xh
         diff:= ?_
         favor:=⟨τw Xh,mul_nonneg (by unfold ridges; positivity) Xh.safe.le⟩
         steady:=LipschitzWith.of_dist_le_mul (fun y t=>by rw [dist_eq_norm,Real.norm_eq_abs,dist_eq_norm]; exact tracksF G Xh y t)
         move:=?_} -- placeholders solve via where? use `:=by refine {...}`
 · unfold viaduct; refine ContDiff.div_const ?_ 2; refine ContDiff.sum (fun i _=>contDiff_const.mul ?_); exact (clip_diff χ Xh.safe).comp (cblossom i)
 intro x y; unfold viaduct; simp_rw [floret_gauge]; unfold clipQ coil; simp
abbrev naked (y:PlaqAxes → G.Color):ℝ:= (∑ i:PlaqAxes, (CF.Compass.decor i:ℝ)* ‖y i‖^2)/2
-- sensor.F_
variable {G}
lemma exposed (t:Signed)(b:Site n)(x:Config G n)(θ:ℝ):(posess G Xh).palette θ t b x=(∑ i:PlaqAxes, (D1 i:ℝ)*clipQ χ (θ • AnalyticBridge.VerifiedReset.petals (pull t b x) 0 i))/2:=by
 unfold Etch.palette Etch.portrait; unfold posess viaduct; dsimp only; congr 1; refine sum_congr rfl fun i _=>?_
 let U:=pull t b x; let v:=fun a:Stitch=> (ringT G a).atSite U 0
 change _*clipQ χ (floret G i (θ • v))= _
 rw [floret_smul,leaves] -- need expose v
lemma thrill {φ:PlaqAxes→G.Color}(H:ℝ)(p:∀i,‖φ i‖≤H): |naked G φ|≤(ridges:ℝ)*H^2:=by
 unfold naked; rw [abs_div,abs_of_pos (show (0:ℝ)<2 by norm_num)]; refine (div_le_self (abs_nonneg _) one_le_two).trans ((Finset.abs_sum_le_sum_abs ..).trans ((sum_le_sum (g:=fun _=>H^2) ?_).trans ?_)); · intro i h; rw [abs_mul,abs_of_nonneg (sq_nonneg ‖φ i‖)]; exact (mul_le_of_le_one_left (sq_nonneg _) (decorV _)).trans (pow_le_pow_left₀ (norm_nonneg _) (p _) 2)
 rw [sum_const,card_univ,nsmul_eq_mul]
lemma expensed {φ:PlaqAxes→ G.Color}:
 |naked G φ - (∑ i:PlaqAxes,(D1 i:ℝ)*clipQ χ (φ i))/2|≤ χ⁻¹ ^ 2*(∑ i:PlaqAxes, ‖φ i‖^4):=by
 unfold naked; rw [← _root_.sub_div,abs_div,abs_of_pos (show (0:ℝ)<2 by norm_num)]; refine (div_le_self (abs_nonneg _) one_le_two).trans ?_
 rw [←sum_sub_distrib,mul_sum]
 exact (Finset.abs_sum_le_sum_abs ..).trans (sum_le_sum (fun i _=>by rw [←mul_sub_left_distrib,abs_mul]; exact (mul_le_of_le_one_left (abs_nonneg _) (decorV _)).trans (recoil _ Xh.safe _)))
end Risa
end YM.Gleam.Luster
