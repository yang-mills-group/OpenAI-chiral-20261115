import Merino.Dais.Reception
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Dais
open YM.CF.QuadClock
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew Waxy Roots Rive Oise


open Py.Rate Py.Rate.LocalLimit Py.Rate.LocalLimit.Preparation
open Pitching Pitching.Focus Fief

open Buffered Afterglow Tower.VacuumSelection
variable (P:Spine)(s i k:ℕ)

local notation "X"=>LedgerM P s i k
local notation "Y"=>LedgerM P (s+1) i k
local notation "x"=>scaleM P s
local notation "L"=>P.par.R.L
local notation "Pp"=>P.par
local notation "g"=>climbRatio P s i
local notation "σ"=>staircase P s i k
local notation "NN"=>RegNum P s i
local notation "Nf"=>RegNum P (s+1) i
local notation "cf"=>Chi.canonical
local notation "Xp"=> XP P s i k
local notation "Cf"=>cipherK P.par.J.n
local notation "Mo"=> LoomM P s i
local notation "Mm"=> LoomM P (s+1) i
local notation "Qf"=> Corolla.cur L
local notation "b"=> (3*dleaf L x)
local notation "h"=>P.par.h
variable (p:Bolts)
variable (A: ArmorK)(Γϕ:ℝ)(Mc:ℕ) (Z W V1 Kf:ℝ→ℝ)
local notation "C"=>colorsPhi L Γϕ x
variable (u f:ℕ)
local notation "v"=> Corolla.cur L f (scaleM P (s+1))


variable {I:Type}[LinearOrder I][Fintype I]
variable (O:Observatory (climbRatio P s i) (LedgerM P s i k).p)
     (K:Cusp (RegNum P s i))(Ca:ArcΦ→ℝ→ℝ)
variable (o:I→Site (RegNum P s i))

open Brooch
local notation "r"=> heel g ∘ o
local notation "tick" => priceTick P

abbrev Chiffon (D:Key I→RegBudget Nf)(F:Key I→ForceBudget Nf):Prop:=
 Glissade g X Y o P.par.V P.par.U σ Mo Mm Xp cf P.par.J.d h (V1 x) (Kf x) (W x)
   A.delta A.f0 A.g0 A.g1 A.g2 (b+C) C (Z x)
   (crown (Y).F D) (crown (Y).K F)
   (fun _=>0) (fun _=>v) O K Ca Cf Mc


variable {P s i k A Γϕ Mc Z W V1 Kf u f O K Ca}
lemma Stride.liftStep
 (a:Stride P s i k A Γϕ Mc Z W V1 Kf f u O K Ca)
 {D:Key I→RegBudget Nf}{F:Key I→ForceBudget Nf}
 (y:GapN o (X).p.B (L).val Mc)
 {q:I→Sour.Firing Nf}
 (l:Corolla.Fit Y r L v u q h D F):
 Chiffon P s i k A Γϕ Mc Z W V1 Kf f O K Ca o D F:=by
 have he:scaleM P (s+1)=x+Vale.billX L:=hat_step _
 have y₁:=a.scale
 exact engagements a.jet
    (latched g X Y _ _ _ l y
       (he ▸ y₁.step.1.le) (he ▸ y₁.request)
       (he ▸ y₁.seams) a.funding.hush a.base)
    (zero_le_one.trans a.funding.toe)


variable {p}{α δ:ℝ}

/-- Reception at any of the original posed layouts; apply whether or
 not one also wants the Mitre bill for subuses. -/
lemma cavalcade (a:Stride P s i k A Γϕ Mc Z W V1 Kf f u O K Ca)
 (l:Coin.Worthy P (s+1) i k p f u α δ)
 (y:GapN o (X).p.B (L).val Mc)
 (p₁:Force_M (Y).p.B (node∘r) u)
 {o₀:I→Site Nf}(d:∀j:I, Dress P (s+1) i k p tick (o₀ j))
 (t:I→Sweep Nf)(p₂:∀j,inReach (Y).p ((r) j) (t j) (d j).y):
 let e:= Coin.trophy P p (s+1) i k d t
 ∃ (T:I→Sour.Bag Nf) (V:I→Swell.phy Nf)
    (D:Key I→RegBudget Nf) (F:Key I→ForceBudget Nf),
   (∀ j,Office P.par.U Y Mm P.par.J.n h α δ ((r) j) (e j) (V j) (T j)) ∧
    Corolla.Fit Y r L v u (Corolla.flowerSum T) h D F ∧
    earnsRoot P.par.U Y Mm r e D F ∧
    Chiffon P s i k A Γϕ Mc Z W V1 Kf f O K Ca o D F:=by
 obtain ⟨T,V,D,F,b',j,j'⟩:=(Gifts.earns _ _ _ _ _ l.gift r p₁ d t p₂).cloth
 exact ⟨T,V,D,F,b',j,j', Stride.liftStep o a y j⟩
end YM.CF.Merino.Dais

