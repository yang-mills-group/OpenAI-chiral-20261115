import Anomaly.Basis.Torus
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate.BScale
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
open Eire Girt
open VolumeRate
variable {n : Side}
open BScale Vow.TreasuryFog Sour Roots Exa Vow Rive Mew Stax Swell Porticus QuadClock Ione.Clock Moto Neon Taxi Lor
open Oise Buffered
variable {a b c v d s f x w y u h:ℝ}{k m:ℕ}{P:BudgetPoint}
lemma coatPow_pos (P:BudgetPoint): 0 ≤ 1+2*Moto.peka_H P.power :=by unfold Moto.peka_H Hove.κP Haro.ξP; have h:= Hove.mpe true; have hv:= Hove.mpe false; unfold Hove.pruneQ; positivity
lemma primaZoo (g:0≤v)(t:0<d)(s:0≤b) : 0≤ αlife a d v∧ 0≤ stemLoan a b d v∧ 0≤ flightLoan a b d v∧ 0≤ scanLoan a b d v∧ 0≤ lowLoan a b d v∧ 0≤ lowScan a b d v:=by
 have he:0≤Haro.horn:=zero_le_one.trans Haro.p0
 unfold αlife stemLoan flightLoan scanLoan lowScan lowLoan; simp_rw [stemLoan,scanLoan,stemLoan,αlife,νt,levPrice,feeSprig,feeRise]; exact ⟨by positivity,by positivity,by positivity,by positivity,by positivity,by positivity⟩
-- monotone in last arg when contraction. post quote eventually uniform
lemma full_book (g:0≤v)(t:0<d)(s':0≤ b)(w:0 ≤ x)(u:x≤ y)(T:s≤ c) :0≤fullEarn P a b d v k m h s x ∧ fullEarn P a b d v k m h s x ≤ fullEarn P a b d v k m h c y :=by
 obtain ⟨g₁,_,g₂,g₃,g₄,g₅⟩:= primaZoo (a:=a+a) g t s'; have hx:= (primaZoo (a:=a) g t s').1
 have he(u z m':ℝ) (p:0 ≤ u) (t:s≤ z) (h:u≤ m'): cashPoncho u s m ≤ cashPoncho m' z m:=by have hw:=p.trans h; unfold cashPoncho; gcongr
 have hr(v:ℝ)(w:0 ≤ v):spill_F P k m v a s h≤ spill_F P k m v a c h:=by unfold spill_F reefCost frostδ; gcongr
 constructor
 · unfold fullEarn cashPoncho vaporB spill_F reefCost frostδ; positivity
 -- addition induction factors
 unfold fullEarn; have hu:reefCost m P s h ≤ reefCost m P c h:=by unfold reefCost; gcongr
 refine add_le_add (add_le_add (add_le_add (he _ c _ ?_ T le_rfl) (add_le_add (he _ c _ ?_ T le_rfl) (hr _ g₂))) (add_le_add (he _ c _ w T u) (add_le_add (he _ c _ ?_ T (add_le_add_right u _)) (hr _ g₃)))) ?_
 · unfold vaporB; positivity
 · unfold vaporB; positivity
 · unfold vaporB; positivity
 exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right hu g₄) (mul_le_mul_of_nonneg_right hu g₃)) (mul_le_mul_of_nonneg_right hu g₅)
lemma chill_book (g:0≤v)(t:0<d)(s':0≤b)(w':0≤x)(u':x≤ y)(T:s≤ c)(z n:ℝ)(hw:0 ≤ z)(hv:z≤ n)(hs:0<w)(hu:0<f) :0 ≤ thinEarn z P a b d v k m h s f w x ∧ thinEarn z P a b d v k m h s f w x ≤ thinEarn n P a b d v k m h c f w y:=by
 obtain ⟨g₁,_,g₂,g₃,g₄,g₅⟩:=primaZoo (a:=a+a) g t s'
 let A:=flightLoan (a+a) b d v; let D:=scanLoan (a+a) b d v
 let Q:=fireCost P k h A a f w; let Y:=fireTall P k h D a x f w; let Y':= fireTall P k h D a y f w; have htQ:0 ≤ Q:=by unfold Q fireCost frostδ Porticus.Φσ; change 0≤ _; have H:0 ≤ A:=g₂; have hp:= P.threshold_pos; positivity
 have htY:0 ≤ Y:=by unfold Y fireTall frostδ Φσ; have H:0 ≤ D:=g₃; have hp:= P.threshold_pos; positivity
 have hz:= P.threshold_pos; have htY' : Y ≤ Y':=by unfold Y Y' fireTall; gcongr
 have hc:= Real.exp_pos (P.supportExponent*↑(axleCap m))
 let T':= reserveT P.power P.order P.B (P.B:ℝ)⁻¹; have he:0 ≤ T':=by unfold T' reserveT coin_n stilK; positivity
 have hp(t z):0 ≤ spillCost P k m t a z h:=mul_nonneg he (abs_nonneg _)
 let F(x:ℝ):=cashPoncho x P.supportExponent m
 have hw'(t:ℝ)(k:0 ≤ t):0 ≤ F t:=mul_nonneg k hc.le
 have hF {x y:ℝ}(t:x≤y):F x≤F y:=mul_le_mul_of_nonneg_right t hc.le
 have h'(u:ℝ)(w:0 ≤ u): spillCost P k m u a s h ≤ spillCost P k m u a c h:=by
    refine mul_le_mul_of_nonneg_left ?_ he; rw [abs_of_nonneg (show 0≤ spill_F P k m u a s h from by unfold spill_F reefCost frostδ; positivity),abs_of_nonneg (show 0≤ spill_F P k m u a c h from by unfold spill_F reefCost frostδ; positivity)]; unfold spill_F reefCost frostδ; gcongr
 exact ⟨add_nonneg (add_nonneg (hw' _ (mul_nonneg hw htQ)) (hp A s)) (add_nonneg (hw' _ (mul_nonneg hw htY)) (hp D s)), add_le_add (add_le_add (hF (mul_le_mul_of_nonneg_right hv htQ)) (h' A g₂)) (add_le_add (hF (mul_le_mul hv htY' htY (hw.trans hv))) (h' D g₃))⟩
abbrev recoilPoint (b k m n:ℕ):ℝ:= (1+(((axleCap k)*(4*b+2)+2*b :ℕ):ℝ))^n
abbrev recoilLens (b k m n:ℕ):ℝ:= recoilPoint b k m n *Jet.composeCost m (m.factorial) (recoilPoint b k m n)
lemma steerPost(x:Seat n): 0 ≤ seam_m m P x ∧ seam_m m P x ≤ recoilLens P.B m P.order P.power:=by
 unfold seam_m; refine ⟨Vow.health_f .., ?_⟩
 have hp: surgeL P (grooveB m P x) P.B ≤ recoilPoint P.B m P.order P.power:=by
    unfold surgeL recoilPoint; gcongr -- nat coercions exact?
    push_cast; gcongr; exact_mod_cast pricedCap m x P
 unfold Vow.fareX Nor.liftR Jet.composeCost recoilLens Jet.composeCost; rw [mul_one]; gcongr -- automatically Hp?
-- constant when measure at L.K.6.2
abbrev projectionConstant(n:ℕ):= (1+2*Moto.peka_H n)
end YM.CF.Py.Rate.BScale
