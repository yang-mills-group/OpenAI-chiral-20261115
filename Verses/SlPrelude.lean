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
abbrev parcelF (x:ℝ):=x^(-claimV)
set_option maxHeartbeats 1250000
variable {N:Side}
lemma sl_prelude (L:Side){a C K:ℝ}(v:0<C)(s0:0<K)(Uo:Loom N)(b₀ t:ℝ)(n:ℕ)(g:Skye.Roof N b₀ t n Uo)(F:ℝ)(Jm:Tulip.Male){δ:ℝ}(p:t≤δ)(ht:0≤t)(h:0<a)(hg:0<δ)(e:Sow 4 N a C δ)
    (T:Sparkle N t Jm 4) (w d:ℕ) (d₀:d=radiusB F)(hw:w ≤ wallsF L F){c:Side}(R':Lattice.Ratio c (More N))(s:R'.count.val=2*w+1)(hu:2*(w+1)<(More N).val)(r:ℕ)(hr:r+d+1=w)(hm:((2*w+1:ℕ):ℝ)^4-((2*r+1:ℕ):ℝ)^4 ≤ F^(-marginV)*((2*w+1:ℕ):ℝ)^4) (he':sax F≤b₀)(G:temp F ≤ sax F ∧ 0<temp F) (ψ:((K^2+1)*(C*2*180))*metro n (wallsF L F)≤(walls L F:ℝ)^4)(hx:(K*K+1)*180*orderT a C δ L F + ((K^2+1)*(C*2*180))* F^(-marginV) ≤ parcelF F):
    let Z:=spar 4 Jm (1:Pane N)
    IsStarProjection Z∧∀ y:Orbit N,let S:=spar 4 Jm (Uo y); ∃ l: Seat N→SU.E,let Q:= twist (tradew N l) S; IsStarProjection S ∧ condor S C ∧ (K*K+1)*entryBudget (Q-Z) ≤ parcelF F * sites N + ((walls L F:ℕ):ℝ)^4 * flakes (sax F) y.1:=by
 intro Z
 let f:= ((K^2+1)*(C*2*180))
 have hv(P':Pane N)(q:Guard P' t):IsStarProjection (spar 4 Jm P'):= T.projection _ q
 have hW:IsStarProjection Z:=hv _ (guard0 ht)
 refine ⟨hW,fun y=>?_⟩; intro V
 obtain ⟨l,cP⟩:= projector_charge (k:=0) g y d w r (sax F) (G.1.trans' G.2.le) he' hr R' s hu hm Jm h v hg e p
 let gz:= tradew N l
 have hp: twist gz V=spar 4 Jm (gauge l (Uo y)):= (T.covary (Uo y) l (g.paid y)).symm
 refine ⟨l,hv _ (g.paid y),e.daylight false Jm (Uo y) ((g.paid y).shrink p),?_⟩
 change (K*K+1)*entryBudget (twist gz V-Z)≤_; rw [hp]
 apply (mul_le_mul_of_nonneg_left cP (by nlinarith only [sq_nonneg K]:0≤K*K+1)).trans
 have hL:0≤ flakes (sax F) y.1:=by unfold flakes; positivity
 let b:= (2*Real.exp (-(a*d))+d*4*sticker w (sax F)/δ)*C
 let BA:= orderT a C δ L F; let nV:=sites N
 have hb: b ≤ BA:=by unfold b BA orderT; rw [d₀]; apply mul_le_mul_of_nonneg_right _ v.le; refine add_le_add_right (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (sticker_mono hw (G.2.trans_le G.1).le) (by positivity:0≤(radiusB F:ℝ)*4)) hg.le) _ -- left?_ defeq
 have hA:0≤BA:=by unfold BA orderT; have hp:=sticker_nonneg (wallsF L F) (G.2.trans_le G.1).le; positivity
 have hl:((N.val:ℝ)^4)≤ nV:=by unfold nV sites; push_cast; exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.le_mul_of_pos_right N.val two_pos) _
 have he :(((More N).val:ℝ)^4)=nV:=rfl
 let D:=flakes (sax F) y.1
 have hx : (K*K+1)*180*BA+f*F^(-marginV) ≤ parcelF F:= hx
 let X:=K*K+1; have hf:0 < f:=by unfold f; positivity
 change X*(b*(180*(N.val:ℝ)^4)+(2*C*180)*(F^(-marginV)*((More N).val:ℝ)^4+ metro n w *D))≤_
 rw [he]; have h0:= (mul_le_mul_of_nonneg_left (metro_mono n hw) hf.le).trans ψ
 rw [show f=X*(2*C*180) from (by unfold f X; ring)] at h0 hx hf
 have ht:b*(180*(N.val:ℝ)^4)≤ BA*(180*nV):=mul_le_mul hb (mul_le_mul_of_nonneg_left hl (by norm_num)) (by positivity) hA
 change _≤parcelF F*nV + _*D; nlinarith only [mul_le_mul_of_nonneg_right h0 hL, mul_le_mul_of_nonneg_right hx (show 0≤nV from (zero_le_one.trans (sites_pos _))),mul_le_mul_of_nonneg_left ht (show 0≤X from by unfold X; nlinarith only [sq_nonneg K])]
end Papal
end LocalLimit
end Rate
end YM.CF.Py
