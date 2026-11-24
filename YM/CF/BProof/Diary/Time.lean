import YM.CF.BProof.Start.Sage
import YM.CF.Sere.Gilt
import YM.CF.Vale.Palm
/- Cost profiles fixed even before h. NPL dleaf. Quanta estimate; no growth in horizon. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Diary
open Function Filter NormedSpace Finset
open Lattice Tenant Lat Cube Skye RG Angular Wilson Rhythm Hero Mark Branch
open scoped Topology BigOperators Classical
open Push SectorNext SectorNext.Remainder.Scales Pressure Next.Scheduling.Clock
open Py Start
lemma pR : NAT Pressure.radiusB:= PL.ceil (PL.log_y.pow 2) (Eventually.of_forall fun y=>sq_nonneg _)
variable (L:Side)
lemma t_future : ∀ᶠ y:ℝ in atTop,0≤ Py.dleaf L y:=by
 unfold dleaf; filter_upwards; intro y; unfold temp Remainder.Scales.g Next.Scheduling.Clock.gap; positivity -- tune
lemma dleaf_p : NPL (Py.dleaf L):=by
 unfold dleaf; refine NPL.by_le (g:=thresh) (coin_n (a:= -1/2) (b:=1) (by norm_num) _) ?_; filter_upwards [eventually_gt_atTop (0:ℝ), (Remainder.Scales.year SU.group L).eventually_ge_atTop (1:ℝ)] with y h p; rw [thresh_eq h,abs_mul]; apply mul_le_of_le_one_left (abs_nonneg _); unfold Remainder.Scales.g Next.Scheduling.Clock.gap; rw [abs_of_nonneg (by positivity : 0≤ (Real.sqrt (Remainder.Scales.y SU.group L y))⁻¹)]; exact inv_le_one_of_one_le₀ ((by simpa using Real.sqrt_le_sqrt p))
end YM.CF.BProof.Diary
