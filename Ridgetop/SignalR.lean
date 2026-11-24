import Ridgetop.Kinder
import Ridgetop.Xray
import YM.UVNext.FREE_STRESS_CERTIFICATE.Diagonal
import Risa.Cultural
import Compass.Prime
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Channels
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.flexible false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 305000
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
open _root_.YM.Regis.Head AnalyticBridge.VerifiedReset StressFlux Lattice.PlaqAxes Virgo _root_.YM.CF.Scree
namespace Ridgetop
open _root_.YM.Regis.Circuit _root_.YM.CF.Onyx _root_.YM.Stationary CF.Compass
local notation "b*"=> ((YM.basis (3:Axis)): Gaia)
def visible:ℂ:=∑ i:PlaqAxes,∑ j:PlaqAxes,(dye i:ℂ)*(dye j:ℂ)*(specter i j (-b*))^2
private lemma crisp (i j:PlaqAxes) : specter i j (-b*)= if i=j then (UVNext.FreeStress.coat (3:Axis) i:ℂ) else 0:=by
 have ht:b*≠0:=norm_pos_iff.mp (by rw [basis_norm]; exact one_pos)
 unfold specter; rw [YM.Maxwell.Bare.even ht,YM.UVNext.FreeStress.bare_diagonal]; split_ifs <;> simp
local notation "ℭ"=> UVNext.FreeStress.coat (3:Axis)
lemma visibility: visible ≠0:=by
 suffices H:0<visible.re from (fun h=> (ne_of_gt H) (show visible.re=0 from h ▸ rfl))
 unfold visible; simp_rw [crisp]
 have h(i:PlaqAxes) : (∑ j:PlaqAxes,(dye i:ℂ)*(dye j:ℂ)* (if i=j then (ℭ i:ℂ) else 0) ^2)= (dye i:ℂ)^2*(ℭ i:ℂ)^2:=by
   simp [ite_pow,mul_ite,eq_comm (a:=i),sq]
 simp_rw [h,← Complex.ofReal_pow,← Complex.ofReal_mul,← Complex.ofReal_sum, Complex.ofReal_re]
 -- witness p02. rg
 let i:PlaqAxes:=⟨(0,2),by decide⟩
 have he:dye i=1:=by unfold dye decor; rw [if_pos (by left; rfl)]; norm_num
 exact (lt_of_lt_of_le (show 0<(dye i)^2*(ℭ i)^2 from (mul_pos (sq_pos_of_ne_zero (he ▸ one_ne_zero)) (sq_pos_of_ne_zero (UVNext.FreeStress.coat_ne _ _)))) (Finset.single_le_sum (f:=fun i:PlaqAxes=> (dye i)^2*(ℭ i)^2) (fun _ _=>by positivity) (Finset.mem_univ _)))
noncomputable abbrev yoking(H:Bed)(z₁ z₂:Site n):ℂ:=∑ i:PlaqAxes,∑ j:PlaqAxes,(dye i:ℂ)*(dye j:ℂ)*(boreV H z₁ z₂ i j)^2
include B P L
lemma ofGeorge (u:G.ColorIndex)(hx:0<δ)(K:H.covered θ v)(p':0<θ)(hv: Floor H q n δ v)(hn:Even n.val)(z w':Cover) : yoking H (wrap n z) (wrap n w')=((sconeR H (wrap n z) (wrap n w'):ℝ):ℂ):=by
 unfold yoking sconeR; simp_rw [← buds B P L _ _ _ _ hx K p' hv u hn]; push_cast; rfl
omit B P L
variable {ν:ℕ→Side}{M:ℕ→Bed}{RR:ℕ→ℝ}{U₁ W₁:ℕ→ Cover} (Troll:Yard ν RR) (roL:Tendsto (fun d=>riseX (RR d) (U₁ d-W₁ d)) atTop (𝓝 (-b*)))
include Troll roL
lemma pulseLimit(K:∀ d,(M d).covered θ C)(p':0<θ)(h:0<C)(V:∀ d,Floor (M d) q (ν d) δ C) : Tendsto (fun d=>(RR d:ℂ)^8*yoking (M d) (wrap (ν d) (U₁ d)) (wrap (ν d) (W₁ d))) atTop (𝓝 visible):=by
 have h2: -b*≠0:=by rw [neg_ne_zero]; exact norm_pos_iff.mp (by rw [basis_norm]; exact one_pos)
 unfold visible yoking; simp_rw [Finset.mul_sum]
 refine tendsto_finsetSum _ fun i _=>tendsto_finsetSum _ fun j _=> ?_
 simp_rw [show ∀ z x:ℂ,z^8*((dye i:ℂ)*(dye j:ℂ)*x^2)= ((dye i:ℂ)*(dye j:ℂ))*(z^4*x)^2 from (fun z x=>by ring)]
 exact (((shin i j Troll roL h2 K p' h V).pow 2).const_mul _)
#print axioms visibility
#print axioms pulseLimit
end Ridgetop
end Risa
end YM.Gleam.Luster
