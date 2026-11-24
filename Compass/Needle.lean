import Compass.SkateMove
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
open StressFlux
variable (hw:PressB P (moveHub s p) F h c)(hv:0≤h)
local notation "δ"=>AnalyticBridge.VerifiedReset.dirS
abbrev echox {n:Side}:Sweep n:=⟨1,0,true⟩
local notation "sw"=> (echox:Sweep n)
lemma thorn(n:Side): boxA (echox (n:=n))= Equiv.refl _:= Equiv.ext fun i=>by rw [sitA]; change affine 1 ((assembly n).root 0) _=_; rw [map_zero]; simp [affine]
lemma song(p:Scree.Hub n): moveHub sw p=p:=by
 refine Subtype.ext (Prod.ext ?_ ?_)
 · change (boxA (echox (n:=n))).symm _=_; rw [thorn]; rfl
 change Finset.map (boxA (echox (n:=n))).symm.toEmbedding _=_; rw [thorn]; ext; simp
include hv
set_option maxHeartbeats 720000 in
lemma echo_P (Z':PressB P p F h c)(B D:PlaqAxes):
    tooth o P (step_F sw F) B D=Spire.payZ sw⁻¹ (tooth o P F B D) := by
 let f:= lifeH F
 let ρg:=Ione.cast_B (Spire.wageZ sw⁻¹)
 have hc :flashA sw=Reef.echo:=funext fun v=>by rw [Skye.revoke]; change polarT true ∘ Lattice.pull 1 ((assembly n).root 0) v= _; rw [map_zero,pull_id]; rfl
 have t(ρ:ℂ→L[ℝ]ℝ): ρ (tooth o P (step_F sw F) B D)=ρ (Spire.payZ sw⁻¹ (tooth o P F B D)):=by
    rw [cym P _ p (pullPressR P sw p Anchored.one ((song p).symm ▸ Z') hv) hv ρ]
    have hl(ℓ:ℂ): ρ (Spire.payZ sw⁻¹ ℓ)=(ρ.comp ρg ℓ):=congrArg (ρ ·) (castT (Spire.wageZ sw⁻¹) ℓ).symm
    rw [hl, cym P _ _ Z' hv]
    let f0:= (ρ.comp ρg) ∘ f
    have he: ρ ∘ lifeH (step_F sw F)= f0 ∘ Reef.echo:=by rw [life_T sw F,hc]; funext i; exact hl _
    rw [he, coeffEcho o p.val.2 _ (cashR F p Z' hv (ρ.comp ρg) _ le_rfl).regular B D]
 exact Complex.ext (t Complex.reCLM) (t Complex.imCLM)
omit hv
lemma yard (s t:Sweep n) : step_F s (step_F t F)=step_F (s*t) F:=by funext v; simp only [step_F,comp_apply,Spire.lights,Ione.moon_Y,mul_inv_rev]
private lemma pay_smul (x:Sweep n)(W:ℂ)(a:ℝ):Spire.payZ x (a • W)= a • Spire.payZ x W:=by unfold Spire.payZ Scroll.cSignX; split; simp only [Complex.real_smul]; simp; rfl
include u hw hv
lemma sombr (hx:Nonwrapping (ZL).val.2 o0)(hn:4 ≤ (More n).val)(B D:PlaqAxes):
    tooth o P (step_F s F) (PlaqAxes.rotate s.s B) (PlaqAxes.rotate s.s D)=(δ s.s B*δ s.s D) • Spire.payZ s⁻¹ (tooth o0 P F B D) := by
 rcases z:s.charge with _|_
 · exact roll_P p P s F u hw hv z hx hn B D
 let t:Sweep n:=⟨s.s,s.b,false⟩; have ht:sw*t=s:=by
    change Sweep.mk (1*_) (0+(1:Signed).act _) _=s; rw [one_mul,Signed.act_one,zero_add]; cases s; congr; exact z.symm
 have hQ: ZL=moveHub t p:= by refine Subtype.ext (Prod.ext rfl rfl) -- boxA ignores charge.
 rw [show step_F s F=step_F sw (step_F t F) from ht ▸ (yard F sw t).symm, echo_P p P _ hv (pullPressR P t p u (hQ ▸ hw) hv),show s.s=t.s from rfl, roll_P p P t F u (hQ ▸ hw) hv rfl (hQ ▸ hx) hn] 
 rw [pay_smul]; congr 1
 have hT (q:Sweep n):sw*q=q*sw:=by rcases q with ⟨v,t,w⟩; change Sweep.mk (1*v) (0+(1:Signed).act _) _=Sweep.mk (v*1) (t+v.act 0) _; simp
 rw [warX sw⁻¹ t⁻¹, show sw⁻¹*t⁻¹=s⁻¹ from by rw [←ht,hT,mul_inv_rev]]; rfl
end YM.CF.Compass
