import YM.CF.DPress.Mant.Legacy
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
 {x:ℝ}{C:Tew W}{β:ℝ}{t:Yds (mid P B)}{v:ℂ}{b:ℝ}{O:Shore0} {Q:Maud x C G S}(m:Penny Q O)
 {J:Type}[TopologicalSpace J][FirstCountableTopology J][Nonempty J] (Gm:J→ℝ)(E:∀ i:J,Lobby Q O (Gm i)) (Y:Pony x C O)
open Oise Salt
-- pointwise version optional.suff `Families` might need weaker in leverage true engine T.steps? defaults use Point from Duty. Check.
structure Families : Prop where
 chin : Continuous Gm
 E0 : Tone_u (fun v=>(E v).F0.1) Q.Y.p
 K0 : Tone_v (fun v=>(E v).F0.2) Q.Y.p
variable {Gm E}(f:Families Gm E)
namespace Penny
include f Y
lemma lightP(i:σn S (C.width x)) (Xq:Aura (mid N B))(V':Orbit (mid N B)): Continuous fun k=> m.Uφ (E k) i Xq V':=by
 exact light_c (H:=m.Hm) (H₁:=Q.X) (H₀:=Q.Y) V _ _ (fun _=>0) _ (fun v=>(E v).J) f.E0 (fun _ _ _=> continuous_const) f.K0 (fun v=> yearp Y (E v).τ) m.M (fun i=>(E i).Base) (fun i=>(E i).FendX m) m.PP m.ht f.chin (fun i=>(E i).looks m) i Xq _ (fun i=>((m.gro_p (E i)).quiet _ _).toLullT) V'
lemma BpK : PointK (fun i=>m.BP (E i)):= by intro i D η; simp_rw [BP,cone_f,Finset.sum_apply]; exact continuous_finsetSum _ (fun k _=> lightP m Y f k i η) -- arg order Y? f implicit
lemma oldε : PointF (fun i=>m.old (E i)):= by intro i D; simp_rw [old,old_Q,Finset.sum_apply]; exact continuous_finsetSum _ (fun k _=> lightP m Y f k i D) -- arg order.
lemma εPt : PointF (n:=mid N B) (fun i=>m.EP (E i)):=by intro X D; simp only [EP,nixV]; exact BpK m Y f X ∅ D
lemma theft : Beau.LampF (fun i=>m.TL Y (E i))∧ PointK (fun i=>m.QL Y (E i)) := lobe_p (R:=R) (H₀:=Q.Y) (H₁:=Q.X) (H:=m.Hm) V Gm _ (fun _=>0) _ (fun v=>(E v).J) f.E0 (fun _ _ _=> continuous_const) m.M C.D_ m.arch C.C' C.s C.Jp C.r _ (lightP m Y f) m.Tp _ _ (fun z=> m.nft Y (E z)) -- infer Zo from lunar age
lemma huB : PointK (fun i=>m.Kb Y (E i)) ∧ Beau.LampF (fun i=>m.Rb Y (E i)):=by
 let F(i):=m.EP (E i); let G(i):=m.old (E i); let U(i):= m.TL Y (E i); let S'(i):=m.QL Y (E i); choose Ψ _ _ _ A _ fZ u _ _ _ _ _ using fun i=>(m.budget (E i)).1.keep; let η:J:=Classical.arbitrary _
 have hg: ∀ i: J, Ready Palot.stern Q.X.p.B (A i) (Q.X.p.supportExponent+1+1) O.s 1 (degreePrice Q.X.p.B O.s 1):=fZ
 exact off_u Q.X.p F G m.Tp U S' (m.oldε Y f) (m.εPt Y f) A C.uB hg u (ready_pos _ _ (fZ η)|>.le) (fZ η).2.2.2.1 (m.theft Y f).2 (m.theft Y f).1 -- order
end Penny
end YM.CF.Py.Kay
