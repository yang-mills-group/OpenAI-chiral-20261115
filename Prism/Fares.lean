import Taffeta.Silk
import YM.SU5.FiniteGaugeData.Pannier.Sketch
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
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
open Ione Beau Haro Cascade Fief VolumeRate
open Roots Buffered LocalLimit LocalLimit.Papal Dyad Dyad.Keeping Mew Compass Drift
attribute [-instance] instDecidableEqLex
set_option quotPrecheck false
namespace Decaf
variable {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}(V:Grace K R L){e h:ℝ}{m B:Side}{P:Grasp V.U B e}(W:GivenX V P)
-- normalize by representative $(s), don't retain gaussian. Den.R throttle. earn
lemma coarseTicket {I:Type}[LinearOrder I][Fintype I](o:I → Site (mid m B))(T:Log I (mid m B))(X:GramM (mid m B)) {cost q α b:ℝ}(hx:Clinic o T 1 h α q X R.L (soot b)) (hp:Graph.Ledger h cost cost (levelQ W.C) (cashU W.C) X)(v:Key (PairKey I))(hv:v∈ Mew.hill (PairKey I))(ht:0≤q) : Graph.Ledger h (cost+q) (cost+q) (levelQ W.C) (cashU W.C) (markedB T X v):=by
 obtain ⟨hs,hV⟩:=hx.span v (Mew.hill_i.mp hv)
 refine ⟨Larch.add_v _ _ _ hp.reg hs, ?_, union_F _ hp.force hV,hp.field⟩
 obtain ⟨⟨j,g,p⟩,f⟩:=hp.slip
 exact ⟨⟨j,g,fun i=> (p i).trans (le_add_of_nonneg_right ht)⟩,f⟩

local notation "Sm"=> mid m B
lemma coarseBill {I:Type}[LinearOrder I][Fintype I](o:I → Site (mid m B))(T:Log I (mid m B))(X:GramM (mid m B)) {cost Ux q a b y:ℝ}{G:Scree.Loom Sm}(n l:ℕ)(hy:Roof Sm Ux e n G)(hpP:P.roundZ ≤ (Sm).val)(hh:1 ≤ h)(hx:Clinic o T 1 h a q X R.L (soot b))(ι:X.path=V.L.path l)(ζ:X.funds=K.top.clip)(he:matchedX y X.beta)(hY:0 ≤ y)(hp:Graph.Ledger h cost cost (levelQ W.C) (cashU W.C) X)(v:Key (PairKey I))(hv:v∈ Mew.hill (PairKey I))(ht:0 ≤ q)(x:Orbit Sm): ‖Graph.recX P (markedB T X v) G x‖≤ Real.exp (earnings W X.p (2*y) (cost+q) * sites Sm):=by
  let K':= markedB T X v
  have he':K'.path.Bounds K'.funds K.top.width K.top.paths V.W.bar:=by change X.path.Bounds X.funds K.top.width _ _; rw [ι,ζ]; exact V.L.mood l  -- unknown ?
  have hb:0 ≤ K'.beta:= (div_nonneg hY (by norm_num)).trans he.1
  let eT:=coarseTicket V W o T X (α:=a) (q:=q) hx hp v hv ht
  have H:= Window.extensive_price  K' G hy P hpP eT he' (level_p _).le hh (cash_v _) hb x
  rw [←Real.exp_add] at H
  apply H.trans; apply Real.exp_monotone; refine (add_le_add_left (tax_price V Sm (p:=X.p) he.2) (Window.flagBill Sm (cost+q) (cost+q) (cashU W.C))).trans_eq ?_
  rw [Window.flagBill_eq]; unfold earnings sites; dsimp only [More]; push_cast; ring

#print axioms coarseBill
end Decaf
end YM.CF.Py.Rate
end
