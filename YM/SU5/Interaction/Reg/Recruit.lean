import SatinThinPlaza
import YM.SU5.Interaction.Reg.Staff
import YM.SU5.Interaction.Reg.Earnings

/-! (124) on the actual R_s in these path consultations (s < n_k).
Do not depend on witnesses of a second course. Proof script adapts sky_Line. -/
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
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
local notation "Coord" i:max k:max=> (tape i).X (Y.uv k)
variable {Pay ξC Γϕ:ℝ}{n u:ℕ}{Tξ:Hove.Grant P.K.j 2}
open BScale
local notation "xt" => hat P.R.L P.x
local notation "v" s:max => Y.meter.a s
local notation "F₁" s:max i:max k:max => (RootBook Y i k s).F
local notation "F₂" s:max i:max k:max => (RootBook Y i k s).p
local notation "XΔ" s:max => fittedCharge (v s) P.R.L (xt s)
variable (h : estimatorFlux P) (pT:∀ i k, ((Y.voyage i).X k).Prepared P.P P.delay)

structure Recruitment (P:Preparation){F:(s:Side)→Scree.Loom s→Prop}(Y:Course P F) : Prop where
  covers : ∀ᶠ s in atTop, ∀ i k, s < Y.uv k →
    (RootBook Y i k s).p = Y.meter.a s ∧
    (RootBook Y i k s).p.order = 6 ∧ (RootBook Y i k s).p.power = 2 ∧ (RootBook Y i k s).p.B = radiusB (hat P.R.L P.x s) ∧
    (RootBook Y i k s).p.threshold = temp (hat P.R.L P.x s) ∧ (RootBook Y i k s).p.supportExponent = 1 ∧
    IncX (fun _ => False) (head_L (RootBook Y i k s).F) (ups (RootBook Y i k s).p) P.h 1 ∧
    LocalHead (RootBook Y i k s).p (1+10/((RootBook Y i k s).p.B:ℝ)) (RootBook Y i k s).F P.h (fittedCharge (RootBook Y i k s).p P.R.L (hat P.R.L P.x s))

include h pT
lemma revenueRange : Recruitment P Y := by
 constructor
 filter_upwards [(turnover P).eventually h,(turnover P).eventually (normalizedRate P.R.L)] with s qq hp i k hi
 let m₀:= Y.ir i; let m:= mesh m₀ P.R.L s; let n₁:= mesh m₀ P.R.L (s+1); let Y' := Y.voyage i; let D:=Coord i k; let ρ:= Actual Y.meter Y'.funds Y'.CapeT (gaugeFreq P (Y.tile*P.M)) (Y.uv k)
 let K:= ρ.toSpine.address s
 obtain ⟨p,b,h,g⟩:= pT i (Y.uv k)
 have hk:=h.toRealQ; let Zq:= ρ; have hh:ρ.active P.P b s=ρ.gram P.P b s:= p.success P.H hk s hi (p.paysStep P.H h s hi)
 let hv:= p.request s hi
 let E:= qq m n₁ K (Y.meter.a s) (Y.meter.a (s+1)) hv (b.read (s+1)).re (ρ.chargeLevel P.P b (s+1)) (hat_step s ▸ (p.beta_ok P.H hk _ hi).2) (p.flow (p.charged P.H hk _ hi))
 let S:=(RootBook Y i k s).p; have c0:S=Y.meter.a s:= (D.pull.owns s hi.le).width.symm
 have e :IncX (fun _=>False) (head_L (F₁ s i k)) (ups S) P.h 1:= by
    rw [c0]; unfold RootBook; rw [g.gramZ]; rw [←hh]; exact E
 let z:= (D.pull.note s hi.le)
 have d':IncX (fun _=>False) (head_L (F₁ s i k)) S P.h (dleaf P.R.L (xt s)):= onlyPositive z.buoy
 have hS: S.supportExponent=1:= by rw [c0]; exact hv.boot.exponent
 refine ⟨c0, (congrArg BudgetPoint.order c0).trans hv.boot.order, (congrArg BudgetPoint.power c0).trans hv.boot.power, (congrArg BudgetPoint.B c0).trans hv.boot.B, (congrArg BudgetPoint.threshold c0).trans hv.boot.threshold,hS,e,?_⟩
 change LocalHead S _ _ _ _; rw [←hS]; exact hp _ S (c0.symm ▸ hv.boot.B) _ _ (zero_le_one.trans P.height) d' e
end Preparation
end LocalLimit
end YM.CF.Py.Rate
