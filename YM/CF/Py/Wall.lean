import YM.CF.Py.Quota
import YM.CF.Py.Month
set_option autoImplicit false
set_option maxHeartbeats 1050000
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
variable {M C:Side}(U:Grasp V.U B d)(W:GivenX V U)(J:Robes M V W)
local notation "NC"=> mesh (C*M) R.L
lemma size_q(P B W: Side) :P.val ≤ (mid (P*W) B).val:=by
 change P.val ≤ P.val*W.val*2*B.val
 apply le_trans (le_trans (Nat.le_mul_of_pos_right _ W.property) (Nat.le_mul_of_pos_right _ two_pos)) (Nat.le_mul_of_pos_right _ B.property)
-- use stable expressions after rewriting epoch Loom tape lengths
structure RocketV (C:Side)(N:Side)(U:Grasp V.U B d)(W:GivenX V U)(J:Robes M V W)(A:Scree.Loom (mid C B))(G:Ratio (mid C B) (mid N B))(q:Chi) :Prop where
 paid:Roof _ J.k J.roomX J.n A
 size: J.h≤(mid C B).val
 pose:∀ (F:Forest (ratio G))(Z:Pane (mid N B))(U:Orbit (mid C B)), JointB G (seine G F q J.d Z (A U), A U) J.roomX
variable (q:Chi)
private lemma gown(K:Side)(n t:Side)(x:n=K*M)(u:J.h ≤ K.val)(g:t=K*R.L*M)(G:Ratio (mid n B) (mid t B))(hp:G.count=R.L): ∃ A:Scree.Loom (mid n B), RocketV V _ _ U W J A G q:=by
 subst n t
 exact ⟨J.rack _ u,J.roof _ u,u.trans (size_q K B M),fun t Z V=> J.tick u (le_trans u (Nat.le_mul_of_pos_right _ R.L.property)) G hp q Z t V⟩
lemma form_t(VH:J.h ≤ C.val)(i:ℕ): ∃ A:Scree.Loom (cell (C*M) B R.L i), RocketV V (mesh (C*M) R.L i) (mesh (C*M) R.L (i+1)) U W J A (apt (C*M) B R.L i) q:=by
 refine gown V U W J q (mesh C R.L i) _ _ (Month.ruler ..) (Grace.Robes.stretch J VH _) ?_ _ rfl
 rw [Month.ruler, mesh_succ]
variable {A0:Scree.Loom (mid N B)}
lemma rig(H:RocketV V N P U W J A0 G q)(A:Scree.Loom (mid P B))(u:Roof _ J.k J.roomX J.n A) (Y:GramM (mid P B))(x:InterestX W.C _ Y.J)(h:G.count=R.L) (w:Girt.Ward Y): Nonempty (Girt.BaseL U G Y A0 A q J.d) :=by
 let k:=H.paid; have hp : Roof _ J.k d J.n A0:= {k with paid:=fun i=>(k.paid i).shrink J.hr.le}; have hx:Roof _ J.k d J.n A:= {u with paid:=fun i=>(u.paid i).shrink J.hr.le}; have ht:=H.size
 refine ⟨⟨W.pearl,V.note,h,W.health, ?_, J.gran.trans ht, ?_,⟨_,_,_,_,Stake.tollX V W x⟩,⟨_,_,_,hp,hx⟩, ⟨J.hv,J.knot⟩,fun i j v=> ?_, w ⟩⟩
 · have he:= V.L.lobby; have hh:=R.order_cut; omega
 · obtain ⟨n,p,a,f,x,l,z⟩:= J.seed; exact ⟨n,p,a,f,x,l.trans ht,z⟩
 let p:= H.pose i j v; exact ⟨p.fg.shrink J.hr.le,p.cg.shrink J.hr.le,fun u=>(p.follow u).trans J.hr.le⟩
end YM.CF.Py
