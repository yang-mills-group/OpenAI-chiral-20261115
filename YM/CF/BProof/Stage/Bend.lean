import YM.CF.BProof.Ribs.Ripe
import YM.CF.BProof.Stage.Twoy
import YM.CF.BProof.Stage.Age
import YM.CF.BProof.Stage.Foam
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
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Footprint Jade Py
open YM.CF.Floral Ione Haro Beau Oise Larch Lilt Vow
open scoped YM.CF.Mew
namespace Cupboard
variable {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}{V:Grace K R L}{N P B:Side}{d x:ℝ}{U:Grasp V.U B d}{W:GivenX V U}{G:Ratio (mid N B) (mid P B)}{S:StepData (Domain N B) (Domain P B)}{T:Tube SU.group S}{G₀:Scree.Loom (mid N B)}{G₁:Scree.Loom (mid P B)}{q:Chi}{e a h γ w:ℝ}{order power:ℕ}{X:GramM (mid N B)}{Y:GramM (mid P B)}
variable {C:Chamber V U W x order power h q e} (D:BasisSt C G T G₀ G₁ X Y a γ w)
namespace BasisSt
variable {D}{i j:D.Asset}{k:ℝ} (m:Matching D i j k)
namespace Matching
local notation "Ω"=> disk (limit k C.δ)
local notation "Yζ" z:max=> m.above z
local notation "P_" z:max=> D.shelter (m.above z)
include m
private lemma ψ {E:Type}[NormedAddCommGroup E][NormedSpace ℂ E](k:ℝ)(x y:E): SubHol (disk k) fun z=>x+(z:ℂ) • y:=⟨_,(differentiableOn_const x).add (differentiableOn_id.smul (differentiableOn_const y)),fun _=>rfl⟩
lemma swell_R (X:Scree.Hub (mid P B))(v:Pane (mid P B)):SubHol (disk (limit k C.δ)) fun z=>(m.above z).val.F X v := ψ m _ _ _
lemma swell_K (X:Force (mid P B))(v:Orbit (mid P B)):SubHol (disk (limit k C.δ)) fun z=>(m.above z).val.K X v := ψ m _ _ _
lemma run_U (T:D.tot)(i':Aura (mid N B))(v:Orbit (mid N B)):SubHol (disk (limit k C.δ)) (fun z=>(D.shelter (m.above z)).Up T i' v):=by
 let X0(z:Ω):=m.above z; let T1(z:Ω):= D.shelter (X0 z)
 have ht(z:Ω):= ((D.shelter (m.above z)).μ.quiet T i').toLullT -- `quiet` args
 exact Oise.reck_cΩ (H:=D.hatH i) (H₀:=Y) (H₁:=D.near i.val) (β:=i.val.βx) V (fun z=> (X0 z).val.F) 0 (fun z=> (X0 z).val.K) (fun z=> (X0 z).val.v) (swell_R m) (fun i v=> SubHol.constant _) (swell_K m) D.M (fun z=> D.fromH (X0 z)) (fun z=> D.finger (X0 z)) D.P_ D.ht T i' (fun z=> (T1 z).Up T i') (fun z=>(D.ageH (X0 z)).1) ht isOpen_ball (⟨0,d0 m.gt_one⟩ : Ω) v -- ABI
lemma run_F (t:Youth N P B)(U':Pane (mid N B)):SubHol Ω (fun z=>(P_ z).ink t U'):=by
 let u:= D.shelter i
 let A:=Hearth.colt_Ω (H₁:=D.near i.val) (H₀:=D.next i.val) (H:=D.hatH i) V D.M C.corset u.Ω C.C C.Xp C.Jp t U'
 let f(z:Ω):= (P_ z).ink t U'; let G(z:Ω):= actionZ (D.next (m.above z).val) t.1 1
 have hψ:SubHol Ω G:=by unfold G actionZ; split; exact m.swell_R ..; exact SubHol.constant _
 have he(z:Ω):f z=A (G z):=by
    dsimp only [f,Cert.ink]; rw [show (P_ z).Ω=u.Ω from Subtype.ext ((P_ z).p.trans u.p.symm)]; rfl
 change SubHol Ω f; rw [funext he]; exact hψ.linear A
lemma run_T (Tp:Ids (mid N B)) (i':Scree.Hub (mid N B))(v):SubHol (disk (limit k C.δ)) fun z=> (P_ z).Ty Tp i' v:= Hearth.mont_hol (H:=D.hatH i) Tp (fun z=> (P_ z).ink) (run_F m) (fun z=> (P_ z).Up) (run_U m) i' v
lemma run_Q (X:Aura (mid N B))(A:Support (Domain N B))(v):SubHol (disk (limit k C.δ)) fun z=> (P_ z).Qc X A v:= Hearth.soot_hol _ (run_F m) X A v
lemma run_B (X:Aura (mid N B))(A:Support (Domain N B))(v):SubHol (disk (limit k C.δ)) fun z=> (P_ z).Bs X A v:=by unfold Cert.Bs cone_f; simp_rw [Finset.sum_apply]; exact SubHol.sum _ fun _ _=> run_U m _ _ _
lemma run_Y (X:Aura (mid N B))(v):SubHol (disk (limit k C.δ)) fun z=> (P_ z).E0 X v:=by unfold Cert.E0 old_Q; simp_rw [Finset.sum_apply]; exact SubHol.sum _ fun _ _=> run_U m _ _ _
lemma grantB {E:Type}[NormedAddCommGroup E][NormedSpace ℂ E](F:D.Asset→ E)(p:SubHol (disk (limit k C.δ)) (fun z=>F (m.above z))): Hol (disk (limit k C.δ)) (fun z=>F (m.along z)):= p.font _ fun z=>congrArg F (m.at_Ω z)
end Matching
end BasisSt
end Cupboard
end YM.CF.Py
