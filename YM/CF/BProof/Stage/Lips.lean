import YM.CF.BProof.Stage.Rays
import YM.CF.BProof.Ribs.Blink
import YM.CF.BProof.Stage.Bend
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
local notation "ε"=> (4*k/C.δ)
local notation "A₀"=> (D.shelter i)
local notation "A₁"=> (D.shelter j)
open Bake Rue
include m
-- leave constants for projection uses
lemma Matching.lips0 (p:Course G Y K.j R.L.val i.val)(q:Course G Y K.j R.L.val j.val)(Tp:Ids (mid N B)): Books X.p ((D.shelter j).Rb Tp-(D.shelter i).Rb Tp) h (wren_K order power*(ε * C.Φ false+rise_K order power w * C.θ k)+ reserveT power order (radiusB x) 1*(6*ε*C.Lp))∧ Heats X.p h (X.p.supportExponent+1+1) ((D.shelter j).Kb Tp-(D.shelter i).Kb Tp) (pack_Q order * (ε*C.ym w)+2*ε*C.Lp):=by
 obtain ⟨u0,f0,X0⟩:= (A₀).lunar_real Tp p; obtain ⟨u1,f1,X1⟩:= (A₁).lunar_real Tp q
 obtain ⟨_,_,B,Q,T,E⟩:= m.relief Tp
 have hz: Books X.p ((A₁).Tx Tp-(A₀).Tx Tp) h (ε*C.Φ false+rise_K order power w*C.θ k):=by unfold Cert.Tx; rw [show (A₁).Ty Tp+(A₁).Tc - ((A₀).Ty Tp+(A₀).Tc) = ((A₁).Ty Tp-(A₀).Ty Tp)+((A₁).Tc-(A₀).Tc) from (by abel)]; exact Books.plus B (m.chord p.1 q.1)
 have he:= (A₀).freeform Tp p.2; have hh:=(A₁).freeform Tp q.2
 have ht:= regular_xray X.p Tp C.hP f1 f0 hh.2.1 he.2.1 hh.2.2 he.2.2 hz E; rw [D.b.down.hK,D.b.down.order,D.b.fee] at ht
 have hv:= heats_xray X.p C.hP u1 u0 Q T; rw [D.b.down.order] at hv; exact ⟨ht,hv⟩
omit m
private lemma blank {t:ℝ}(p:0≤t) (k:D.Asset):ShiftQ Y.p h t (Parcel.mk k.val.βx 0 0 0 : Parcel (mid P B)) :=by
 let f:= Vale.lye (fun _: Sweep (mid P B)=>False) Y.p h; exact ⟨Books.mono f.1 p, Pressed.mono f.2 p⟩
private lemma ink_off (R':D.Cert i)(p:i.val.F=0):R'.ink=0:=by
 funext j v; unfold Cert.ink; have ht: actionZ (colour Y i.val) j.1 =0:=by
    unfold actionZ; split; · exact congrFun p _
    · rfl -- tune
 rw [ht]; exact map_zero _
private lemma Ty_off (R':D.Cert i)(Tp:Ids (mid N B))(p:i.val.F=0):R'.Ty Tp=0:=by
 unfold Cert.Ty; rw [ink_off R' p]; exact Hearth.mont_0 (H:=D.hatH i) R'.Up Tp fun j c=> Oise.veil_wane (H₁:=D.near i.val) (H₀:=D.next i.val) V D.M (D.fromH i) (D.finger i) D.P_ D.ht p rfl j (beamH c.val) ((R'.μ.quiet (subtK S j) c).toLullT)
lemma green (R':D.Asset)(u: 0 < k) (s:k≤C.δ/4)(p: Course G Y K.j R.L.val R'.val)(v:ShiftQ Y.p h k R'.val)(Tp:Ids (mid N B)): Books X.p ((D.shelter R').Rb Tp) h (wren_K order power*( (4*k/C.δ) * C.Φ false+rise_K order power w * C.θ k)+ reserveT power order (radiusB x) 1*(6*C.Lp)):=by
 let A:= D.shelter R'; let i': D.Asset := ⟨⟨R'.val.βx,0,0,0⟩, R'.property.year, blank C.ful.le R', fun i _ _=> Beau.none_q _⟩; let Q':=D.shelter i'
 have he:Matching D i' R' k:=⟨rfl,blank ((half_pos C.ful).le) R',by change Books _ (R'.val.F-0) _ _; rw [sub_zero]; exact v.reg, by change Pressed _ (R'.val.K-0) _ _; rw [sub_zero]; exact v.force,u,s⟩
 have ht:= (he.relief Tp).2.2.1; rw [Ty_off Q' Tp rfl,sub_zero] at ht
 have hx:= (A.glory Tp).1; have hh:= A.hmono_x p.1 v.reg; have hT:= (A.lunar_real Tp p).2.1; have hz:= cup_R X.p _ (Books.plus ht hh) hT (zero_le_one.trans C.hP)
 obtain ⟨f,g,u⟩:= A.freeform Tp p.2; obtain ⟨t,v,Xb⟩:= beauty.mp f; have hr:= Ione.addT X.p hz (worth_R X.p (A.cash Tp) Tp g u (zero_le_one.trans C.hP) v Xb); rw [D.b.down.order,D.b.down.hK,D.b.fee] at hr; exact ⟨hr.weight,fun _ v=> v.elim⟩
end BasisSt
end Cupboard
end YM.CF.Py
