/- Compatibility lift, near-exact baseline YM/SU5/Thin/Cascade/Tinsel.lean with narrower imports omitting Vellum. No proof changes. -/
import YM.SU5.Thin.Cascade.Ost
import Bay.Deck.Flight
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
open scoped ComplexOrder
variable {N:Side}{K : Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
open YM.Gleam
open clocks
variable {L':Side}
namespace Papal
open CF.Rapids CF.Pannier.Damask CF.Pannier.Damask.VelvetC CF.Pannier.Chancel
open Graph Pannier
local notation "Ψ"=> P.R.L

open clocks Sleigh Paddled
variable (s i k:ℕ)
local notation "M"=> count Y s i
local notation "θA"=>levelQ P.W.C
local notation "θB"=>cashU P.W.C
local notation "X"=>hat Ψ P.x
local notation "Z"=>uniformDebit
local notation "μ" x:max=> radiusB x
abbrev pursue (C:ℝ)(b k:ℝ):= k*(180*45)*(b+b^2)*C + b^2*C -- k=(1+C₀)^2*(180)^2*flareUp(D)^2
abbrev permitF (C:ℝ)(k:ℝ)(w l:ℕ):= quake w l 1* (k*(45*6*C)+4*C)
-- exact expense separation
lemma fit_detail (q:ℝ)(V:Orbit (count Y s i))(C D θ:ℝ)(ℓ:ℕ):let j:= (1+C)^2*180^2*(flareUp D)^2; fit_fare Y V θ q C D ℓ = pursue θB q j*((count Y s i).val:ℝ)^4 + permitF θB j P.J.n ℓ * flakes θ V.1 :=by
 intro j; unfold fit_fare pursue j paintE pittance permitF storm quake; rw [Pic.units_t]; ring
lemma charge_fit(C D:ℝ)(p:0≤C)(v:0≤D) : ∀ᶠ s in atTop,∀ i:ℕ,let F:= hat Ψ P.x s;∀ W:Orbit (count Y s i),let g:= temp F/2; fit_fare Y W g (uniformDebit θA F) C D (height F) ≤ (oar F/2)*sites (count Y s i)+(clocks.grain F/2)*Pannier.flakes g W.1:=by -- namespace clocks succ
 let a:=(1+C)^2*180^2*(flareUp D)^2; let F(x:ℝ):= pursue θB (uniformDebit θA x) a; have hp:=debitFlow (level_p P.W.C); have h:Paddled (-(2/5:ℝ)) F:=by
    let f:= (Z θA); let W:=cashU P.W.C; let t:= (hp.power 2).up (by norm_num : -(2/5:ℝ)*(↑(2:ℕ):ℝ)≤ -(2/5:ℝ)); apply ((((hp.add t).scale (a*(180*45)*W)).add (t.scale W))).agree (Eventually.of_forall ?_); intro x; unfold F pursue; dsimp only; ring
 let u:=P.J.n; let t(x:ℝ):= (height x:ℝ); let b:= ((4*(( (u+4)*2+1:ℕ)^4 : ℕ)*180:ℕ):ℝ)*(a*(45*6*θB)+4* θB)
 have hb:0≤b:=by unfold b a; have hp:=cash_v P.W.C; positivity
 filter_upwards [(stage_slope P.V P.x).eventually (h.discounts (b:=-(1/500:ℝ)) (by norm_num) (by norm_num:(0:ℝ)<1/2)), (stage_slope P.V P.x).eventually ((tendsto_natCast_atTop_atTop (R:=ℝ)|>.comp Work.E01.radiusB_tendsto).eventually_ge_atTop (2*(1+b*3^4))), (stage_slope P.V P.x).eventually_gt_atTop 0] with s v u' ps i x W g
 rw [fit_detail]; apply add_le_add
 · apply le_trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans v) (show 0 ≤ ((count Y s i).val:ℝ)^4 from by positivity)); change (1/2:ℝ)* _*_≤ _; rw [show 1/2*(X s)^(-(1/500:ℝ))=oar x/2 from (by unfold oar x; ring)]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) (show _ ≤ ((More (count Y s i)).val:ℝ) from Nat.cast_le.mpr (Nat.le_mul_of_pos_right _ Nat.zero_lt_two)) _) (div_nonneg (shinyH x ps).2.2.2.le (by norm_num))
 apply mul_le_mul_of_nonneg_right _ (show 0 ≤ flakes g W.1 from Nat.cast_nonneg _)
 let V:=t x; have ht:2*(1+b*3^4) ≤ V:=u'; have hV:1 ≤ V:= by linarith only [hb,ht]
 change permitF θB a u (height x) ≤ V^60/2
 rw [show permitF θB a u (height x) = b *(V+V+1)^4 from (by unfold b permitF quake V t; push_cast; ring)]
 apply le_trans _ (div_le_div_of_nonneg_right (pow_le_pow_right₀ hV (show 5 ≤ (60:ℕ) by decide)) (by norm_num : 0 ≤(2:ℝ)))
 have hz: V+V+1≤3*V:=by linarith only [hV]
 refine le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (show 0≤V+V+1 by positivity) hz 4) hb) ?_; nlinarith only [mul_le_mul_of_nonneg_right ht (show 0≤ V^4 by positivity), show 0≤ V^4 by positivity]
end Papal
end LocalLimit
end Rate
end YM.CF.Py
