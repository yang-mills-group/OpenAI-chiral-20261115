import YM.CF.DPress.Act.Weight
import YM.CF.DPress.Act.Twin
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Py.Kay
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
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Siete PhysicalNext.JointLoad.Heir Vow
open AnalyticBridge.VerifiedReset
open DPress DPress.Fees Finance Rosy
open scoped YM.CF.Mew
open Oise Larch  Bake
variable
 {N P B:Side}{S:StepData (Domain N B) (Domain P B)}{G:Ratio (mid N B) (mid P B)}{K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group} {d:ℝ} {V:Grace K R L} {U:Grasp V.U B d}{W:GivenX V U}
 {x:ℝ}{C:Tew W}{β:ℝ}{b:ℝ}{O:Shore0} {Q:Maud x C G S}
 {P_:Campus C}
open Sour Tap Heath Tutor Docket Resident Campus Flight Moral Rosy
open Arco WagesC
open UVNext.PricedKernels Work.F03 WilsonStartup
namespace Act
open Harvester WagesC Urban
namespace Silo
variable {A:Harvester P_}{ξ:ℝ→ℝ}(T: Silo A ξ Q O) (Wν : Blend (mid N B) A.μ) (α:ℝ)
local notation "vΠ"=> mid N B
local notation "vℓ"=> Q.X.p
variable (E:Lobby Q O β)(p: HonestL E)(t:Can Q P_ O.δ α)
local notation "Up'"=> U
open Rue Iva Lilt
-- from standard mentor $e_K. Q.E angle tags.Eₚ
abbrev Hrel(β:ℝ):= T.p.X' β -- β +canoe; slip=0.
abbrev packed := T.ΞK E p
abbrev cook := T.Hrel β
abbrev hand (v:ℝ):Prop:= ∀ V:Orbit (mid N B),FleetS (vℓ).threshold V.1→ exponentL Q.X.p (EHat T α E p) V.1=(Taxi.moldV (mid N B) v + Taxi.moldV (mid N B) (enerS_K (T.p.X' β) (T.Δa α E p) V))+ exponentL Q.X.p (B0 T α E p) V.1+fuelV Q.X.p (truce Q.X.p Q.X.path Q.X.funds R.L.val (EHat T α E p) T.p.Tp) V
include t p
private lemma holdings : ∃ v:ℝ, hand T α E p v:= (Field.terms T.p A T.Y _ (T.ηw α E p t) (T.p.X' β).beta).2.2.2.2.2.2
abbrev δs := Classical.choose (holdings T α E p t)
abbrev eventL := T.p.c₀ E+T.δs α E p t
variable (b:Orbit (mid N B)) (Λ:FleetS Q.X.p.threshold b.1)
local notation "Θ'" => enerS_K (T.p.X' β) (T.Δa α E p) b
abbrev πH(V:Orbit (mid N B)):= Wν.Φ (h:=Q.X.p.threshold) α V.1
local notation "πΩ"=> πH (Q:=Q) Wν α b
local notation "QF"=> Taxi.moldV (mid N B)
local notation "Le'"=> (T.eventL α E p t)
local notation "EV"=> Tenant.quota
local notation "EL"=> exponentL Q.X.p
local notation "FL"=> fuelV Q.X.p
omit t p
private lemma combine (d0 r0 z0 x y e Pm U s L:Cipher (mid N B))(h:r0 + e=x+y+Pm+U) : d0+r0+z0=((d0+x+y)-(e+s+L)+(Pm+s))+(z0+U+L):=by have ht:r0=x+y+Pm+U-e:= eq_sub_of_add_eq h; rw [ht]; abel
include Λ T p t
lemma row : coldE Q.X.p (FeeD Q.X.p (EmptyD (T.ΞK E p))) b = (Taxi.moldV (mid N B) (T.eventL α E p t+enerS_K (T.p.X' β) (T.Δa α E p) b-πH (Q:=Q) Wν α b)+ exponentL Q.X.p (R0 T Wν α E p) b.1)+fuelV Q.X.p (A0 T Wν α E p) b:=by
 have ht:coldE Q.X.p (FeeD Q.X.p (EmptyD (T.ΞK E p))) b=Taxi.moldV (mid N B) (T.p.c₀ E)+(EL) (before T E p) b.1+(FL) (Θt T E) b:= ((Urban.pick T.p T.u E p).post rfl).sell b Λ -- owed_E definitional? inspect
 let Y:= T.EHat α E p; have hp:(EL) Y b.1=(QF) (T.δs α E p t)+(QF) (Θ')+(EL) (B0 T α E p) b.1+(FL) (truce Q.X.p Q.X.path Q.X.funds R.L.val Y T.p.Tp) b:= Classical.choose_spec (holdings T α E p t) b Λ
 have he: (QF) (πΩ) = EL (αLan α+ Wν.Sα α) b.1+(FL) (Wν.Zα α) b:= Wν.finances Q.X.p α b Λ
 rw [map_sub,map_add,he,R0, eventL, map_add, A0,Larch.ripe_H Q.X.p b (B0 T α E p) (Wν.Sα α),Larch.ripe_H Q.X.p b (αLan α) (Wν.Sα α),Vow.toast,Vow.toast,ht]; unfold Y EHat at hp; rw [Larch.ripe_H Q.X.p b] at hp
 exact combine _ _ _ _ _ _ _ _ _ _ hp
abbrev priceGas (v:Orbit (mid N B)):= Palot.hGas (flags Q.X.p.threshold v.1) (keyL Q.X.p (packed T E p) (EmptyD (packed T E p)) v)
lemma gainΦ : priceGas T E p b = Real.exp (T.eventL α E p t+ enerS_K (T.Hrel β) (T.Δa α E p) b-πH (Q:=Q) Wν α b) • (exp (exponentL Q.X.p (T.R0 Wν α E p) b.1)* fueled Q.X.p (Kplus T Wν α E p) b):=by
 obtain ⟨g,v,y⟩:= (T.chips Wν α E p t).amen C.uB; unfold priceGas; rw [asterT v (show 0≤ Q.X.p.supportExponent+1 from add_nonneg Q.X.p.exponent_pos.le zero_le_one) y zero_lt_one C.uB b Λ _ (T.row Wν α E p t b Λ).symm]; let p0:=Le'+Θ'-πΩ; let a:=exponentL Q.X.p (T.R0 Wν α E p) b.1; let K:=fueled Q.X.p (T.Kplus Wν α E p) b; letI :NormedAlgebra ℚ (Cipher (mid N B)):=NormedAlgebra.restrictScalars ℚ ℝ _; change exp (owed_E (mid N B) p0+a)*K= Real.exp p0 •(exp a*K); rw [exp_add,owed_E,←thim_v,←Iva.yeaH,←Complex.ofReal_exp,thim_v]; unfold Lilt.thim; rw [smul_mul_assoc,one_mul,smul_mul_assoc] -- adapt
omit t p Λ T
end Silo
end Act
end YM.CF.Py.Kay
