import YM.CF.Pso.Taxes
import YM.CF.BProof.Stage.Lips
import YM.CF.Pso.Coor
import YM.CF.BProof.Stage.Pipe
import YM.CF.Song.Pads
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
variable {A:Type}[TopologicalSpace A]
structure Rhodes (ρ:A→ D.Asset):Prop where
 F : Tone_u (fun i=> (ρ i).val.F) Y.p
 K : Tone_v (fun i=> (ρ i).val.K) Y.p
 β : Continuous fun i=> (ρ i).val.βx
-- continuous physical variations as Grow grants
variable [Nonempty A][FirstCountableTopology A]{φ:A→ D.Asset}(H:Rhodes (D:=D) φ)
local notation "R'" i:max=> (D.shelter (φ i))
namespace Rhodes
include H
open Bake Rue
lemma stem (z:D.tot)(i:Aura (mid N B))(v:Orbit (mid N B)) : Continuous (fun t:A=> (R' t).Up z i v):=by
 let Z(t:A):=(φ t).val
 let W(t):=D.shelter (φ t)
 -- explicitly typed predicate to use equalities
 let Xo:= fun t=> (Z t).βx
 let Fo:= fun t=> (Z t).F; let Zo:= fun t=> (Z t).K; let Jo:=fun t=> (Z t).v
 let E(c c':ℝ):Prop:= ∀ t:A, let Y':= colour Y (Z t); let X':=prelim X (Xo t) c c'; LookZ V (Xm:=X') (Xu:=Y') D.M (D.finger (φ t)) (D.fromH (φ t)) D.P_ D.ht D.tag C.zv ((tolQ X.p).supportExponent+1) ∧ LullT V C.F C.Z (X:=X') (Y:=Y') D.M D.P_ D.ht (D.finger (φ t)) (D.fromH (φ t)) z (Stilo.beamH i.val) ((W t).Up z i)
 have he: E a γ := fun t=> ⟨(D.ageH (φ t)).1, ((W t).μ.quiet z i).toLullT⟩
 have hv:E D.H.ang D.H.fee:=by rw [D.land,D.raise]; exact he
 exact Oise.light_c (H₀:=Y) (H₁:=X) (H:=D.H) V Xo Fo 0 Zo Jo H.F (fun _ _ _=>continuous_const) H.K (fun i=> C.posβ _ (φ i).property.year) D.M (fun i=> D.fromH (φ i)) (fun i=>D.finger (φ i)) D.P_ D.ht H.β (fun c=>(hv c).1) z i (fun t=> ((W t).Up z i)) (fun u=>(hv u).2) v
lemma step_T (Tp:Ids (mid N B)) : LampF (fun t:A=> (R' t).Tx Tp) ∧ PointK (fun t:A=> (R' t).Qc):=by
 -- lobe_p with Eq specialized via same technique
 let Z(t:A):=(φ t).val; let i0:= Classical.arbitrary A; let q0:= (R' i0).Ω
 let F(t:A):= (R' t).Up; let TF(t:A):=(R' t).Tx Tp; let Q(t:A):=(R' t).Qc
 let E(c c':ℝ):Prop := ∀ t:A, Lunar (H:=D.hatH (φ t)) (Uφ:=F t) (Y:=colour Y (Z t)) (X:=prelim X (Z t).βx c c') V D.M C.corset q0 C.C C.Xp C.Jp Tp (TF t) (Q t)
 have he: E a γ:=by intro t; rw [show q0=(R' t).Ω from Subtype.ext ((R' i0).p.trans (R' t).p.symm)]; exact (R' t).lunar_age Tp
 have hv:E D.H.ang D.H.fee:=by rw [D.land,D.raise]; exact he
 exact Oise.lobe_p (H₁:=X) (H₀:=Y) (H:=D.H) V (fun t=> (Z t).βx) (fun t=> (Z t).F) 0 (fun t=>(Z t).K) (fun t=> (Z t).v) H.F (fun _ _ _=>continuous_const) D.M C.corset q0 C.C C.Xp C.Jp C.coming F H.stem Tp TF Q hv
lemma cost_B : PointK (fun t:A=> (R' t).Bs):=by intro i t v; unfold Cert.Bs cone_f; simp_rw [Finset.sum_apply]; exact continuous_finsetSum _ (fun j _=>H.stem j i v)
lemma work_T (Tp:Ids (mid N B)): LampF (fun i:A=>(R' i).Rb Tp) ∧ PointK (fun i:A=> (R' i).Kb Tp):=by
 let F(t:A):=(R' t).Eb; let E(t:A):=(R' t).E0
 have hs:PointF F:=fun i u=> H.cost_B i ∅ u; have ht:PointF E:=by intro i u; unfold E Cert.E0 old_Q; simp_rw [Finset.sum_apply]; exact continuous_finsetSum _ (fun j _=> H.stem j i u)
 choose G R Ls C0 A0 T U0 W Wc wS hm hw ν y using fun i:A=> (R' i).mist.keep; let v:= U0 (Classical.arbitrary A)
 have h:= off_u X.p F E Tp (fun t:A=> (R' t).Tx Tp) (fun t:A=> (R' t).Qc) ht hs A0 C.hP U0 W (ready_pos _ _ v|>.le) v.2.2.2.1 (H.step_T Tp).2 (H.step_T Tp).1
 exact ⟨h.2,h.1⟩
end Rhodes
end BasisSt
end Cupboard
end YM.CF.Py
