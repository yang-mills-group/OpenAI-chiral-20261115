import LusterS.Scrim
import Verses.Shade
import Verses.Sensor
import YM.CF.Muse.Sail
import CellQ.Tidal
import CellQ.Beam
import CellQ.MealK
import SatinIncome
import Verses.AnchorP
import CellQ.Donate
import Verses.Staging
import Verses.Sensor
import Verses.Billing
import Verses.Fusing
import LusterS.Husk
import YM.SU5.Velvet.Hemline
import Refrain.Seismic
import YM.SU5.Velvet.Viper
import YM.SU5.Velvet.Fronds
set_option autoImplicit false
set_option maxHeartbeats 320000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
variable {h z:ℝ}
open Buffered
open CF.Pannier.Damask
open YM.CF.Velvet
open Pannier
namespace Papal
local notation "ℶ" => hat P.R.L P.x
local notation "💠" => P.K.j
open CF.Papyrus.Franc Verses CF.Pannier.Chancel Checkers Flint Gleam Gleam.Luster Gleam.Luster.Almanac Grade Graph
local notation "pio"=> P.R.L
open CF.Window CF.Velvet CF.Pannier.Damask
set_option maxHeartbeats 800000

open Mew CF.Compass CF.Drift CF.Neon Py.Dyad Kona
attribute [-instance] instDecidableEqLex
open BProof CF.Refrain SectorNext.Remainder
-- roof debt.B. as X.Mon.
lemma mound {t:ℝ}{n:ℕ}(p:0≤t)(v:t≤1/2): (∑ i∈Ico 2 n, t^i)≤ 2*t^2:=by
 induction n with
 | zero=> simp; positivity
 | succ k ih=>
    by_cases h:2≤k
    swap; · rw [Ico_eq_empty_of_le (by omega),Finset.sum_empty]; positivity
    -- need leftover: use geometric cancellation
    let Z:ℝ:=∑ i∈Ico 2 (k+1),t^i
    have ht(k':ℕ)(hp:2≤k') : (1-t)*(∑ i∈Ico 2 k',t^i)=t^2 - t^k':=by
       induction k',hp using Nat.le_induction with
       | base=> simp
       | succ k h ih=> rw [Finset.sum_Ico_succ_top h,mul_add,ih,pow_succ]; ring
    have hh:=ht _ (h.trans (Nat.le_succ k)); change (1-t)*Z=_ at hh
    have he:0≤ Z:=sum_nonneg fun i _=> pow_nonneg p _
    change Z ≤ _
    nlinarith only [mul_le_mul_of_nonneg_right v he,hh, he, show 0≤t^k.succ from pow_nonneg p _]
lemma clocks_roof (b a:ℝ) :∀ᶠ s:ℕ in atTop,∀ i k:ℕ,s≤ Y.uv k → let Q:=gram Y s i k; let x:=ℶ s; let H:=allotΨ pio x; 4 ≤ Q.p.B∧ 1≤ H⁻¹ ∧ 0<H ∧
 ∀ (I:Type)[LinearOrder I][Fintype I], 3*dleaf pio x * sites (count Y s i) + roofPrice I (count Y s i) Q.p (a*H) (b*H) (H⁻¹:ℝ) + roofPrice I (count Y s i) Q.p (b*H) (b*H) (H⁻¹:ℝ) ≤ (|a|+|b|)*Fintype.card (PairKey I) + parcelF x* sites (count Y s i) :=by
 let f(i:ℝ):= allotΨ pio i
 let y(i:ℝ):= Scales.y SU.group pio i
 let R(i:ℝ):=dustbit 1 (radiusB i)
 have hp:∀ᶠ x:ℝ in atTop,R x ≤x ^(-4:ℝ):=by
    filter_upwards [eventually_ge_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_gt_atTop 101] with x h he
    have hh:=Nat.le_ceil (Real.log x^2); unfold R dustbit; rw [Real.rpow_def_of_pos (zero_lt_one.trans_le h)]
    apply Real.exp_monotone
    let z:=Real.log x; change z^2 ≤ (radiusB x:ℝ) at hh
    nlinarith only [pow_le_pow_left₀ (show 0≤z by linarith only [he]) (by nlinarith only [hh,he]: z ≤ (radiusB x:ℝ)) 2,he,hh]
 have hf:∀ᶠ x in atTop,0<f x ∧ f x≤1∧f x = (y x)⁻¹ ∧ y x≤ 2*x:=by
    let b:= SU.group.slopeConstant*Real.log P.R.L.val
    filter_upwards [(year SU.group pio).eventually_gt_atTop 1,eventually_ge_atTop b] with x h he
    have hh:= Scales.yg2 SU.group pio (zero_lt_one.trans h); have hx:0<y x:=zero_lt_one.trans h
    have hu:(Scales.g SU.group pio x)^2=(y x)⁻¹:=by field_simp; linarith only [hh]
    change 0<Scales.g _ _ _^2∧ Scales.g _ _ _^2≤1∧_
    rw [hu]; exact ⟨inv_pos.mpr hx,inv_le_one_of_one_le₀ h.le,hu,by unfold y Scales.y betaF; linarith only [he]⟩ -- after rw all? f still folded.Inst h
 have hg:YM.Gleam.Luster.Almanac.Grade (-1/2) (dleaf pio):=by
    unfold dleaf
    let g(x):=Scales.g SU.group pio x
    have he: Grade 0 g:= by
       apply YM.Gleam.Luster.Almanac.Grade.cash (YM.Gleam.Luster.Almanac.Grade.block 1); filter_upwards [(minute SU.group pio).eventually (ge_mem_nhds zero_lt_one),(year SU.group pio).eventually_gt_atTop 0] with i v e; unfold g; rw [abs_of_pos (Scales.gauge _ _ e),abs_one]; exact v
    simpa only [zero_add] using he.mul YM.Gleam.Luster.Almanac.Grade.temp_b
 let Z(x:ℝ):=(f x)⁻¹*R x
 have he:YM.Gleam.Luster.Almanac.Grade (-3) Z:=by
    have he:Grade 1 (fun x:ℝ=> (f x)⁻¹):=by
       apply YM.Gleam.Luster.Almanac.Grade.cash (YM.Gleam.Luster.Almanac.Grade.scaleB 2 YM.Gleam.Luster.Almanac.Grade.x_id); filter_upwards [eventually_ge_atTop (1:ℝ), hf] with i h p; rw [abs_of_nonneg (inv_pos.mpr p.1).le,p.2.2.1,inv_inv,abs_of_nonneg (show 0≤(2:ℝ)*id i from (by change 0≤ 2*i; linarith))]; exact p.2.2.2
    have ht:YM.Gleam.Luster.Almanac.Grade (-4) R:=by
       apply YM.Gleam.Luster.Almanac.Grade.cash (YM.Gleam.Luster.Almanac.Grade.pitch (-4)); filter_upwards [eventually_gt_atTop (0:ℝ),hp] with x h p; rw [abs_of_pos (show 0<R x from Real.exp_pos _)]; exact p.trans (le_abs_self _)
    convert! he.mul ht using 1; norm_num
 have hw := (hg.scaleB 3).plus (((he.pwr 2).scaleB (4*|b|)).grow (b:=-1/2) (by norm_num))
 filter_upwards [(turnover P).eventually hf,(turnover P).eventually ((he.roots (by norm_num)).eventually (ge_mem_nhds (show (0:ℝ)<1/2 by norm_num))), (turnover P).eventually (Work.E08.eventual_radiusB 4),(turnover P).eventually (hw.cost_p (b:=-claimV) (by norm_num [claimV,ratioV,tauA]))] with s ht hZ hr hW i k t Q x H
 have hq:Q.p=Y.meter.a s:=(prices_plot Y s i k t).1
 have hh:=Y.meter.boot s; have hE:Q.p.B=radiusB x:= by rw [hq,hh.2.1]
 rw [hE] -- p only once outside roofPrice?
 have hP:0<H:=ht.1
 refine ⟨hr,one_le_inv_iff₀.mpr ⟨hP,ht.2.1⟩,hP,fun I _ _=>?_⟩
 let N:ℝ:=Fintype.card (PairKey I); let n:= sites (count Y s i); have hn:0≤n:= zero_le_one.trans (sites_pos _)
 unfold roofPrice; rw [Complex.norm_real,Real.norm_of_nonneg (inv_pos.mpr hP).le, hE, show Q.p.supportExponent=1 from (by rw [hq,hh.2.2.1])]
 have hK(a:ℝ): H⁻¹*(a*H)=a:=by field_simp
 simp_rw [hK]
 let A:= ∑ j∈Ico 2 (Fintype.card (PairKey I)+1),Z x^j
 have hz0:0≤Z x:=mul_nonneg (inv_pos.mpr hP).le (Real.exp_pos _).le
 have ha: 0≤ A:=sum_nonneg fun i _=>pow_nonneg hz0 _; have hX:A ≤2*Z x^2:=mound hz0 hZ
 have hpz:3*dleaf pio x+4*|b| *Z x^2≤ parcelF x:=(le_abs_self _).trans hW
 have hk:n*(b*H)*A ≤ 2*n*(|b| *Z x^2):=(mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul (le_abs_self b) ht.2.1 hP.le (abs_nonneg _)) hn) ha).trans ((mul_le_mul_of_nonneg_left hX (by positivity:0≤n*(|b| *1))).trans_eq (by ring))
 have hf(t:ℝ):N*t≤N*|t|:=mul_le_mul_of_nonneg_left (le_abs_self _) (by unfold N; positivity)
 change 3*dleaf pio x*n+(N*a+n*(b*H)*A)+(N*b+n*(b*H)*A) ≤ (|a|+|b|)*N+parcelF x*n
 nlinarith only [hk,hf a,hf b,mul_le_mul_of_nonneg_right hpz hn]
end Papal
end LocalLimit
end Rate
end YM.CF.Py
