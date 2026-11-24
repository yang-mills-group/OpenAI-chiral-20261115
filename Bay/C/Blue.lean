import Bay.C.Glow
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Bay.C
open QuadClock
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



open Rate LocalLimit Preparation Pitching Focus 
set_option maxRecDepth 3500
set_option synthInstance.maxHeartbeats 160000
local notation "VΔ"=>Buffered.Afterglow.Tower.VacuumSelection.Spine


open HullF

variable {N:Side}{p:BudgetPoint}{s:Sweep N}
 {I J:Type}[LinearOrder I][Fintype I][LinearOrder J][Fintype J]
 {r:I→Site N}{r':J→Site N}
 {e:Key I→Cusp N}{e':Key J→Cusp N}

private lemma spinsBoth (h:∀x v,River (fun z=> heat_P p e z x v))
 (f:∀x v,River (fun z=>heat_P p e' z x v))
 (i:I)(j:J)(m:∀t:ℝ,|t|≤1→
   MirrorBill N p s (e (realKey i t)) (e' (realKey j t))):
  Fρ s (feeTip p e' j)=feeTip p e i:=by
 have a:(1:ℝ) • feeTip p e' j=feeTip p e' j:=one_smul ..
 rw[←a]
 apply turnG 
 intro x z
 apply turnAxis s i j (fun y=>heat_P p e y x z) 
  (fun y=>heat_P p e' y (moldA s x) (yellA s z)) (h _ _) (f _ _) 1
 intro t y
 rw[mul_one]
 have a:MirrorBill N p s (e 0) (e' 0):=by 
    simpa only [realKey,Complex.ofReal_zero,Mew.centre] using m 0 (by simp)
 exact (congrArg₂ (·-·) ((m _ y).wax x z) (a.wax x z)).trans (map_sub ..).symm

namespace HullF
variable {w:HullF}{b:Rib w.P}{M M':ℕ}{g g':Outfit}{t t':ℕ}{a:w.Apron}

variable {r0:I→Site w.home}{r1:J→Site w.home}
 {T:I→SealV w.sea}{V:J→SealV w.sea}
 {E:Key I→RegBudget w.sea}{F:Key I→ForceBudget w.sea}
 {E':Key J→RegBudget w.sea}{F':Key J→ForceBudget w.sea}
 {m n:ℕ}
 {o:Ignition r0}{o':Ignition r1}

lemma lapis
 (c:w.scene b M)
 (u:ShipF w b M g t a r0 T E F m o)
 (v:ShipF w b M' g' t' a r1 V E' F' n o')
 (i:I)(j:J)
 (s:Sweep w.home)
 (p:Slide (reSweep w.G s) (twinB E F i) (twinB E' F' j)):
 Fρ s (feeTip w.X.p o'.Fv j)=feeTip w.X.p o.Fv i:=by
 apply spinsBoth u.sail.table v.sail.table i j
 intro z e
 let S:= reSweep w.G s
 refine a.Be.flies s _ _ _ _ _ _ (u.sail.source _ (realKey_mem i z e))
    (v.sail.source _ (realKey_mem j z e)) ?_ ?_
 · have ha:w.Ey E 0=w.Y.F:= u.pink.buy.rail.1
   have hb:w.Ey E' 0=w.Y.F:=v.pink.buy.rail.1
   rw[u.pink.north _ _ e,v.pink.north _ _ e,ha,hb,(u.tips i).1,(v.tips j).1]
   exact (AstroFunding.stillE c S).add S (p.1.smul S z)

 have ha:w.Fy F 0=w.Y.K:=u.pink.buy.rail.2.2
 have hb:w.Fy F' 0=w.Y.K:=v.pink.buy.rail.2.2
 rw[u.pink.south _ _ e,v.pink.south _ _ e,ha,hb,(u.tips i).2,(v.tips j).2]
 exact (AstroFunding.stillF c S).add S (p.2.smul S z)

