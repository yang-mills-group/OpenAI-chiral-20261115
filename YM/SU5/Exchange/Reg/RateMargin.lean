import YM.SU5.Exchange.Reg.OnRoad
import YM.SU5.Exchange.Reg.Incidence
import YM.CF.BPress.Scale
noncomputable section
set_option maxHeartbeats 480000
set_option autoImplicit false
set_option synthInstance.maxSize 24000
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Chaff Gloss Maize Tye RP RP.Str Oise
namespace LocalLimit

namespace Preparation
open FullBill Window Marks
open Pitching Focus QuadClock
variable {P:Preparation}{F:(s:Side)→Scree.Loom s→Prop}(Y:Course P F)
local notation "tape" i:max=> (Y.voyage i)
private lemma smaller (R:Side) :
 ∀ᶠ x:ℝ in atTop, Real.exp (-(↑(radiusB x):ℝ)/2) ≤ dleaf R x / 1000 := by
 let A:= SU.group.slopeConstant*Real.log R.val
 filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 6, eventually_ge_atTop A, eventually_gt_atTop (0:ℝ), eventually_ge_atTop (5000:ℝ), (Scales.year SU.group R).eventually_gt_atTop 0] with x h v hx y t
 let l:=Real.log x; have hp: l^2 ≤ (radiusB x:ℝ):= Nat.le_ceil _
 have he:= Real.exp_monotone (show -(↑(radiusB x):ℝ)/2 ≤ -l-l from (by unfold l at *; nlinarith))
 have ht:Real.exp (-l-l)=x⁻¹*x⁻¹:=by simp only [sub_eq_add_neg,Real.exp_add,Real.exp_neg,l,Real.exp_log hx]
 apply he.trans; rw [ht]
 let q:=Scales.g SU.group R x; let r:=BPress.g x
 have hq:0<x+A:=t; have hv:q^2=(x+A)⁻¹:= BPress.gscale hq.le
 have hr:r^2=x⁻¹:= BPress.gscale hx.le
 have f:0<q:=BPress.g_pos hq; have g:0<r:=BPress.g_pos hx
 have k:r^2 ≤ 2*q^2:=by rw [hv,hr,←one_div,←div_eq_mul_inv]; rw [div_le_div_iff₀ hx hq]; linarith
 have w: r ≤ 2*q:=by nlinarith
 unfold dleaf; rw [BPress.temp_eq]; change _≤ q*(r*_)/1000
 have z:x⁻¹ ≤ q*r*2:=by rw [←hr]; nlinarith
 have z' : x⁻¹ ≤ 1/5000:=by rw [←one_div]; gcongr
 have hm := BPress.drift_one x
 have hl : r ≤ r*BPress.drift x:= le_mul_of_one_le_right g.le hm
 apply (mul_le_mul z z' (inv_nonneg.mpr hx.le) (by positivity)).trans; nlinarith [mul_le_mul_of_nonneg_left hl f.le]

structure RateStamp :Prop where
 hot : ∀ᶠ s:ℕ in atTop,∀ i k:ℕ,s<Y.uv k→ let Q:=RootBook Y i k s;
    Q.p.supportExponent=1 ∧ IncX primeU (head_L Q.F) (raiseRate Q.p) P.h 1 ∧
    ∃ v:Scree.Hub _ →ℝ,(∀ X, PressB Q.p X (head_L Q.F X) P.h (v X)) ∧
     ∀ x:Seat _,(∑ X:Scree.Hub _, if x∈X.val.2 then Ione.massPlus Q.p (10/(Q.p.B:ℝ)) X.val.2 (v X) else 0) ≤
       annual Q.p.B (dleaf P.R.L (hat P.R.L P.x s)/1000)

lemma EarningsRate.atMask (K:EarningsRate P.J Chi.canonical P.h P.N0 P.P)
    (p: ∀ i k, ((Y.voyage i).X k).Prepared P.P P.delay) : RateStamp Y := by
 constructor
 filter_upwards [onRoad Y p K, (turnover P).eventually (smaller P.R.L), (Work.E01.radiusB_tendsto.comp (turnover P)).eventually_ge_atTop 40] with s h0 t u i k w
 let Q:=RootBook Y i k s
 obtain ⟨y,z⟩:=h0 _ _ w
 have hh: Q.p=Y.meter.a s := (((Y.voyage i).X (Y.uv k)).pull.owns s w.le).width.symm
 have he:(Y.meter.a s).B=radiusB (hat P.R.L P.x s):=(Y.meter.boot s).2.1
 change Q.p.supportExponent = 1 ∧ IncX primeU (head_L Q.F) _ _ _ ∧ ∃ v:_,(∀ X,PressB Q.p X (head_L Q.F X) _ _) ∧ _
 rw [hh]
 refine ⟨(Y.meter.boot s).2.2.1, y, Ione.earnIncidence _ _ z y P.height ?_ (he.symm ▸ u)⟩
 rw [he]; exact t
end Preparation
end LocalLimit
end YM.CF.Py.Rate
