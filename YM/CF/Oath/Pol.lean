import YM.CF.Oath.Kinks
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
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
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
open Eire.Dress Yaw PetalP Feu Feu.Corset Haro
variable {r K0:ℕ}{ι:Type}[Fintype ι][DecidableEq ι]{f c:Type}[Fintype f][LinearOrder f][Fintype c][LinearOrder c]
local notation "κ"=> (Scree.mid P B)
local notation "Kx"=> (Scree.mid N B)
local notation "hT"=> (LeanV f)
local notation "Zx"=> LeanV c
local notation "BF"=> (Eire.Ride S)
local notation "Fm"=> (LeanV (Single κ))
local notation "CM"=> (LeanV (Single Kx))
-- Exact resolve PH.Wick all shares.SupportX both senses. 
variable (p q: Single (mid P B))(Tg:Rill.Arch G t)(W: Meter TailB G t)(Y:Meter Grave G t)(g_: Odd G.count.val)(t':0<t)(kR:ℕ)
local notation "ρ"=> Support (Domain P B)
local notation "V'"=> Support (Domain N B)
local notation "PX" b:max a:max=> (twigExt (b,a))
local notation "β"=> bring t' Tg
local notation "Xm"=> cala G S g_ t t' W Y Tg kR
section
-- compress exact payload.Open endpoints retarget sym late.PA independent Ω. input record choices static.
variable (F':InkD (mid P B))(Zr:Rill.Arch G t)(PO:Scree.Hub (mid P B))(T_:Pane (mid P B))(O:Crowd (Site (Domain N B)))(Rt:Support (Domain N B))
abbrev crownM (Q:Eire.Ride S)(v:Prism.Rock (mid P B))(w:Prism.Rock (mid P B)):=∑ a:SU.Slot,∑ b:SU.Slot, frostM (S:=S) (v,a) (w,b) Tg Y t' kR Q (orbitPH (F' T_) (v,a) (w,b))
abbrev current (J:Finset ((Support (Domain P B))×(Support (Domain P B))))(X:Support (Domain P B))(Sx:Eire.Ride S):=∑ r∈hue_I X,∑ t∈hue_I X, ancient J F' W t' r t kR Sx Tg T_
variable (P0:BudgetPoint)(hp: PressB P0 PO F' d e)
include hp g_
local notation "Ω"=> (Stilo.beamH Rt)
local notation "PQ"=> orbitPH (F' T_)
local notation "Ax"=> perm_p (Wheat (camp PO.val.2))
local notation "ιX"=> Track (Ride S) (FC CM)
local notation "ιP"=> LeanV (Single (mid P B))
local notation "lyr"=> lyTerm Tg W t' kR
lemma winH (J:Finset ((Support (Domain P B))× Support (Domain P B)))(O:Ride S): (Feu.Corset.lump Ax (fun i=> Pastry.crumb (F' T_).val i) Xm O Rt)=
   ((∑ r∈hue_I PO.val.2,∑ t∈hue_I PO.val.2,crownM (S:=S) Tg Y t' kR F' T_ Ω r t) O)+(current (S:=S) Tg W t' kR F' T_ (univ \ J) PO.val.2 Ω O)+ (current (S:=S) Tg W t' kR F' T_ J PO.val.2 Ω O):=by
 rw [craneS PO.val.2 O (Xm) Rt F' T_ PO P0 hp]
 let Q:=PO.val.2; let u:=hue_I Q; let Y':=Xm
 have hx(r' s:Prism.Rock (mid P B)) : ∑ a:SU.Slot,∑ b:SU.Slot,ranks ([(true,(r',a)),(false,(s,b))]) (show Ride S from Ω) (PQ (r',a) (s,b)) Y' = crownM (S:=S) Tg Y t' kR F' T_ Ω r' s+ ancient (S:=S) (univ \ J) F' W t' r' s kR Ω Tg T_ + ancient (S:=S) J F' W t' r' s kR Ω Tg T_ :=by
    have hp: ∑ a:SU.Slot,∑ b:SU.Slot,pileP (S:=S) (r',a) (s,b) Tg W t' kR (PQ (r',a) (s,b)) Ω= ancient (S:=S) univ F' W t' r' s kR Ω Tg T_:=by
       unfold pileP; rw [ancient,Fintype.sum_prod_type (fun p:Support (Domain P B) × Support (Domain P B)=> curbY (S:=S) (primeY (S:=S) kR p.1 p.2 Ω) (fun r t=>lyric G t' W F' p.1 p.2 r' s r t T_ Tg))]; let Q(x y):ιX:= lyTerm Tg W t' kR r' s F' T_ (show Ride S from Ω) x y
       apply Eq.trans (_: _=∑ x:ρ,∑ y:ρ,Q x y)
       · refine sum_congr rfl (fun i _=> sum_congr rfl (fun j _=> pict_r Tg W t' kR r' s F' T_ Ω i j)) -- bullet might reversed
       unfold Q lyTerm; simp_rw [sum_comm (s:=(univ:Finset SU.Slot)) (t:= (univ:Finset (Support (Domain P B))))]
    unfold Y'; simp_rw [kicks, sum_add_distrib,hp,add_assoc]; rw [crownM]; congr 1; unfold ancient; exact (sum_sdiff (subset_univ _)).symm -- tune
 let F(v:Prism.Rock κ):= ∑ s∈u,crownM Tg Y t' kR F' T_ (show Ride S from Ω) v s
 unfold current; simp_rw [Finset.sum_apply]; rw [←sum_add_distrib,←sum_add_distrib]; apply sum_congr rfl; intro i p; rw [←sum_add_distrib, ←sum_add_distrib]; apply sum_congr rfl; intro j p; have ht:=congrFun (hx i j) O; simp only [Finset.sum_apply,Pi.add_apply] at ht; exact ht
end
end YM.CF.Oath
