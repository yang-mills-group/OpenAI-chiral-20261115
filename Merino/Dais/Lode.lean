import Merino.Dais.Call
import Merino.Dais.Fabric
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

variable {o:I→Site (RegNum P s i)}

open Corolla

/-- At an admitted stage (or even upper plate if provisioned), with an extra
 100 powers in the chip payment, prove (52), as a zero-core issuance.
This applies at ANY Worthy / Fall including inside Dais. -/
lemma minor
 {D:Key I→RegBudget NN}{K:Key I→ForceBudget NN}
 {y:I→Sour.Firing NN}
 (r:s ≤ P.run.uv k)
 (t:Fit X o L (cur L (f+100) x) u y h D K)
 (j:I):
 Exclusive (X).p (o j) h (cur L f x) (νTip D j):=by
 have hp:(X).p=P.run.meter.a s:=(Papal.prices_plot P.run s i k r).1
 have g₀:(P.run.meter.a s).B=radiusB x:=by
   exact (P.run.meter.boot s).2.1
 apply isolated X o (X).p t rfl (zero_le_one.trans P.par.height)
 change laceBoost (X).p*cur L (f+100) x ≤ cur L f x
 unfold laceBoost
 rw [hp,g₀]
 have ht:BPress.lscale x=1+(radiusB x:ℝ):=rfl
 have hp: 0 < BPress.lscale x:=zero_lt_one.trans_le (BPress.lscale_one _)
 apply le_of_eq
 simp only [←ht,cur,pow_add]
 field_simp


end YM.CF.Merino.Dais
