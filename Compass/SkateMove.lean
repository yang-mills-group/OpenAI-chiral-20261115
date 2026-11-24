import Compass.OrderPrice
import Compass.Rose
import YM.CF.Ione.Mesh
import Compass.EchoCoeff
import YM.CF.Moto.Pin
import YM.CF.Tale.Halo
import YM.CF.Beau.Ray
import YM.CF.Hope.Log
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Compass
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Next.Foundations StressFlux AnalyticBridge.VerifiedReset Push.Local
open Taxi
open Vow
local notation "G₅"=> SU.group
open Moto Ione
variable (p:Scree.Hub n)(P:BudgetPoint)(s:Sweep n)(F:InkD n)(u:Anchored s.s)
local notation "ZL"=> moveHub s p
local notation "o"=>p.val.1
local notation "o0"=>(ZL).val.1
lemma pane_tax(s:Sweep n)(X:Cipher n): Pastry.pane (suit_Y s X) = Spire.payZ s (Pastry.pane X):=by
 let l:= detX s.s; let d:= Dwell n; let p:=s.charge; let U:= praise s
 let Y:Dough d:= ⟨windX (p.xor l) X.val,Wtrans _ (fineShape X)⟩; change Pastry.pane (Pastry.fold U Y)=_; rw [center_b]; change crumb (windX (p.xor l) X.val) ∅=cSignX (p.xor l) (Pastry.pane X); cases p.xor l<;> rfl
lemma life_T(s:Sweep n)(F:InkD n): Taxi.lifeH (step_F s F)=Spire.payZ s⁻¹ ∘ lifeH F ∘ flashA s:=funext fun v=> pane_tax ..
open StressFlux
variable {ρ:ℂ→L[ℝ]ℝ}(Wn:PressB P (moveHub s p) F h c)(E:0≤h)
local notation "δ"=>AnalyticBridge.VerifiedReset.dirS
include u Wn E
set_option maxHeartbeats 750000 in
lemma roll_P (pv:s.charge=false)(hw: Nonwrapping (ZL).val.2 o0)(hn:4 ≤ (More n).val)(B D:PlaqAxes):
    let z:=(tooth o0 P F) B D
    (tooth o P (step_F s F)) (PlaqAxes.rotate s.s B) (PlaqAxes.rotate s.s D)=(δ s.s B*δ s.s D) • Spire.payZ s⁻¹ z := by
 -- missing h Nonwrapping! add
 intro z
 let aℓ:= (δ s.s B*δ s.s D)
 let f:= lifeH F
 let ρg:=Ione.cast_B (Spire.wageZ s⁻¹)
 let F_:=step_F s F
 let b:= (assembly n).embed s.b
 have hc :flashA s=Lattice.pull s.s b:=funext fun v=>by rw [Skye.revoke,pv]; rfl
 have hi:affine s.s b o0=o:=by rw [←sitA]; exact (boxA s).apply_symm_apply _
 have t(ρ:ℂ→L[ℝ]ℝ): ρ ((tooth o P (step_F s F)) (PlaqAxes.rotate s.s B) (PlaqAxes.rotate s.s D))=ρ (aℓ • Spire.payZ s⁻¹ z):=by
    rw [cym P _ p (pullPressR P s p u Wn E) E ρ]
    have hv(ℓ:ℂ): ρ (aℓ • Spire.payZ s⁻¹ ℓ)=aℓ*(ρ.comp ρg ℓ):=by rw [map_smul]; change _ * ρ (Spire.payZ _ _) = _ * ρ _; exact congrArg (aℓ * ρ ·) (castT (Spire.wageZ s⁻¹) ℓ).symm
    rw [hv, cym P _ _ Wn E]
    let f0:= (ρ.comp ρg) ∘ f
    have he: ρ ∘ lifeH F_= f0 ∘ Lattice.pull s.s b:=by rw [show lifeH F_=Spire.payZ s⁻¹ ∘lifeH F ∘ flashA s from life_T s F,hc]; funext v; change ρ (Spire.payZ _ (f _)) = ρ (ρg _); exact congrArg (ρ ·) (castT (Spire.wageZ s⁻¹) _).symm
    rw [he,←hi, AnalyticBridge.VerifiedReset.rotateCoeff s.s b _ Thera.yet_one (cashR F ZL Wn E (ρ.comp ρg) _ le_rfl).regular hw hn B D]; unfold aℓ; ring
 exact Complex.ext (t Complex.reCLM) (t Complex.imCLM)
#print axioms roll_P
#check roll_P
end YM.CF.Compass
