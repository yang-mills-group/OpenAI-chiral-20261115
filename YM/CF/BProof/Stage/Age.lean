import YM.CF.BProof.Stage.Market
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
variable (i:D.Asset)
-- define canon Luma pieces for complex page
variable {i D}
namespace Cert
variable (R':BasisSt.Cert D i) -- local explicit for fields
local notation "U!"=> (D.next i.val)
local notation "Xz"=> (D.near i.val)
local notation "Ht"=> (D.hatH i)
open Bake Rue
abbrev Paid :Prop:= ∀ t:Youth N P B,∀ i':Pane (mid N B),(R'.ink t i').val=cars_P t.2.2.1 t.2.2.2 i' (glasp (H:=D.hatH i) (Y:=colour Y i.val) (X:=prelim X i.val.βx a γ) V D.M C.corset R'.Ω C.C C.Xp C.Jp t)
local notation "Cz"=> forge_P (H:=D.hatH i) (Y:=colour Y i.val) (X:=prelim X i.val.βx a γ) V D.M C.corset R'.Ω C.C C.Xp C.Jp
variable (Tp: Ids (mid N B))
-- put only weak qualifications
lemma glory : Paid R' ∧ Books X.p (R'.Ty Tp) h (C.Φ false) ∧ Heats X.p h (X.p.supportExponent+1+1) R'.Qc (C.ym w) :=by
 obtain ⟨κ,pκ⟩:= D.manna i i.property.cost.reg
 obtain ⟨Qx,Qv,Fq⟩:= Pig.sail_t V (H₀:=D.next i.val) (H₁:=D.near i.val) (M_:=D.M)
 obtain ⟨B1,B2,Tκ,qh,Lw⟩:= (R'.yield κ pκ Tp).yield
 let DF:= C.Hf*(S.patch.L.val:ℝ)^4 * C.δ+C.Df
 obtain ⟨Fv,Q0,A,t,u,v,Wp,-,-⟩:= (orbit_Vb V C.F C.Z (D.hx i) D.M (D.finger i) (D.terra i).1 (D.fromH i) _ _ D.h0 D.h1 C.room C.pond C.w0 C.wv C.wq D.P_ D.Tc D.ht C.corset R'.Ω R'.p Qx Qv Fq h C.C C.Xp C.Jp C.hP R'.μ κ pκ.power C.GG Tp B1 B2 Tκ DF Lw).pay
 have q:Fv=R'.ink := by funext j v; exact Hearth.colt_work (H₁:=Xz) (H₀:=D.next i.val) V D.M C.corset R'.Ω C.C C.Xp C.Jp j Fv t v
 subst Fv
 have hB:=year_c (X:=Xz) (Y:=D.next i.val) (Uφ:=R'.Up) V D.M C.corset R'.Ω h C.C C.Xp C.Jp C.hP κ Tp B1 B2 Tκ DF Lw R'.ink t
 have heΔ:DF=C.Φ false:= by unfold DF; rw [D.l_eq]
 refine ⟨t,?_ ,?_⟩
 · rw [Hearth.mont_eq (H₁:=Xz) (H₀:=D.next i.val) V D.M C.corset R'.Ω C.C C.Xp C.Jp R'.ink t R'.Up Tp] at hB
   rw [heΔ] at hB; exact hB
 rw [Hearth.heat_eq (H₁:=Xz) (H₀:=D.next i.val) V D.M C.corset R'.Ω C.C C.Xp C.Jp R'.ink t] at Wp; subst Q0
 refine Heats.iff_anuk.mpr ⟨A,u,fun o=>?_⟩; let W':= shine_C (C.wide+300) (X.p.supportExponent+1+1)*(tet_B (C.wide+300) X.p.B * GvC order h (miteV X.p.B X.p.order X.p.power 1 C.zv) DF (ball_v (cirQ x):ℝ))
 have he: W'= C.ym w:=by unfold W' Chamber.ym pay_Z; rw [D.b.down.hK,D.b.down.order,D.b.fee,D.b.bill,heΔ]
 exact (show tallB _ _ _ o ≤ W' from v o).trans_eq he
lemma pays: Paid R':=(R'.glory (Classical.arbitrary _)).1
lemma hmono_x (p:Copper Y.p R.L.val K.j i.val.F Y.J.M){t:ℝ}(v:Books Y.p i.val.F h t) : Books X.p R'.Tc h (rise_K order power w * C.θ t):=by
 obtain ⟨κ,pκ⟩:= D.manna i v
 obtain ⟨Qx,Qv,Fq⟩:= Pig.sail_t V (H₀:=D.next i.val) (H₁:=D.near i.val) (M_:=D.M)
 let L(z:Bool):= grow_P V (D.hx i) D.M (D.fromH i) C.htA C.corset R'.Ω R'.p Qx Qv Fq h C.C t C.Xp C.Jp C.hP κ z C.pW pκ (D.code_w i p) C.ζ C.hv D.hZ C.uZ
 have W':= post_P V C.F C.Z (D.hx i) D.M (D.finger i) C.corset R'.Ω R'.p Qx Qv Fq h C.C C.Xp C.Jp C.hP κ pκ.power C.GG R'.ink R'.pays _ L
 rw [Hearth.car_eq (H₁:=Xz) (H₀:=D.next i.val) V D.M C.corset R'.Ω C.C C.Xp C.Jp R'.ink R'.pays] at W'
 change Books X.p (Hearth.city_car R'.ink x) h (rise_K order power w * C.θ t); have he:rise_K order power w * C.θ t=rise_K order power X.p.supportExponent * C.θ t:=by rw [D.b.bill]
 rw [he]; exact W'
end Cert
end BasisSt
end Cupboard
end YM.CF.Py
