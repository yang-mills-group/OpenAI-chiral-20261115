import Anomaly.Rack.Huddle
import Anomaly.Ship.Harvey
import Anomaly.Ship.Stays
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
private lemma smoler (R:Side) :
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

open BScale Lor Vow Sour
abbrev stencilReserve (L:Side)(x:ℝ):= chi_f 6 * Ione.heatMark (radiusB x) (Ione.annual (radiusB x) (dleaf L x/1000))
lemma soilBudget (P:Patch) : sizeK P.L 2 (stencilReserve P.L):=by
 let T'(x):= taxIns (radiusB x); have hv:BoreP T':=(BoreP.still _).grip (BoreP.radius_c.self 10)
 have hp:sizeK P.L 2 (fun x=> Ione.annual (radiusB x) (dleaf P.L x/1000)):= by
    unfold Ione.annual; simp_rw [div_eq_mul_inv,mul_comm (dleaf _ _) (1000:ℝ)⁻¹]; refine (hv.creditK _).tint (((dev_R P).1.scale _|>.scale _).scale _) -- tune
 unfold stencilReserve heatMark
 exact (((hv.creditK P.L).tint (((hp.scale (Real.exp 16)).accrue hp).scale _)).scale _)
lemma soilScouts (L:RateStamp Y): ∀ᶠ s:ℕ in atTop,∀ i k:ℕ,s<Y.uv k→ let Q:=RootBook Y i k s;
 Sectoral Q.p P.J.n (scald Q.p (Ione.head_L Q.F)) P.h (Q.p.supportExponent+16/(Q.p.B:ℝ)) (stencilReserve P.R.L (hat P.R.L P.x s)):=by
 filter_upwards [L.hot,(turnover P).eventually (smoler P.R.L), (Work.E01.radiusB_tendsto.comp (turnover P)).eventually_ge_atTop 52] with s H x v i k w Q
 obtain ⟨p,t,e⟩:= H _ _ w; obtain ⟨u,g,υp,uQ,k'⟩ := p_meters Y i k s w
 let V:= dleaf P.R.L (hat P.R.L P.x s)/1000; let F:=Ione.annual (Q.p.B) V
 have ht:52≤Q.p.B:=u.symm ▸ v; have he:Real.exp (-(Q.p.B:ℝ)/2) ≤ V := u.symm ▸ x
 have hV:0 ≤ V:=(Real.exp_pos _).le.trans he
 have hw:1≤ taxIns Q.p.B:=by
    have g(x: Seat (P.Ctor (Y.ir i) s)):= placeExpense Q.p.B Q.p.B_pos x
    let A:Seat (P.Ctor (Y.ir i) s):= 0; refine le_trans ?_ (g A); rw [←Real.exp_zero]; refine (le_of_eq ?_).trans (Finset.single_le_sum (fun i _=> (Real.exp_pos _).le) (Finset.mem_univ A)); simp [separation_self]
 have hx := Ione.stayPay Q.p F _ P.height e t ht (show Real.exp (-(Q.p.B:ℝ)/2) ≤ F from he.trans (show V≤ F from ?goal)) -- order v before h! tune
 case goal=> exact le_trans (show V≤ Real.exp 1*((Real.exp 20+1)*V) from le_trans (le_mul_of_one_le_left hV (le_add_of_nonneg_left (Real.exp_pos _).le)) (le_mul_of_one_le_left (by positivity) (Real.one_le_exp zero_le_one))) (le_mul_of_one_le_left (by positivity) hw)
 obtain ⟨C,X,D⟩:= hx
 let A:=Ione.heatMark (Q.p.B) F
 have h0:0≤ A:= le_trans (sum_nonneg (fun i _=>?_ )) (D 0)
 · let T:= (show Sectoral Q.p P.J.n (scald Q.p _) P.h (Q.p.supportExponent+16/(Q.p.B:ℝ)) (chi_f Q.p.order*A) from scald_sells (P:=Q.p) _ X P.height _ A D h0); convert T using 1; unfold A F stencilReserve; rw [show Q.p.B= _ from u, show Q.p.order=_ from υp] -- tune wrong `_` accent
 · split; exact mul_nonneg (Real.exp_pos _).le (Roots.gradeE _ _ (X _) (zero_le_one.trans P.height)); exact le_rfl
end Preparation
end LocalLimit
end YM.CF.Py.Rate
