import YM.CF.Oath.Kick
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
variable (a0 b0:SU.Slot)(P1 P2:Rock (mid P B))
abbrev lyTerm (Y':InkD (mid P B))(U':Pane (mid P B))(K₀:Eire.Ride S)(X Y:Support (Domain P B)):=∑ a:SU.Slot,∑ b:SU.Slot,lockP (P1,a) (P2,b) Tg W t' kR X Y K₀ (orbitPH (Y' U') (P1,a) (P2,b))
abbrev lineY (a b:Rock (mid N B))(F:Op SU.Slot): FC CM:=∑ i:SU.Slot,∑ j:SU.Slot,F i j • gateY (a,i) (b,j)
abbrev curbY (Z:Eire.Ride S)(F:Rock (mid N B)→ Rock (mid N B)→Op SU.Slot):Track (Ride S) (FC CM):= Pi.single Z (∑ a:Rock (mid N B),∑ b:Rock (mid N B),lineY a b (F a b))
variable (Y':InkD (mid P B))(U':Pane (mid P B))(K₀:Eire.Ride S)(X Y'':Support (Domain P B))(X_: Meter TailB G t)
local notation "ζ_r"=> (K₀⊔mark_l S kR X ⊔mark_l S kR Y'')
include t'
set_option maxHeartbeats 430000 in
lemma pict_r : lyTerm Tg W t' kR P1 P2 Y' U' K₀ X Y''= curbY (K₀⊔mark_l S kR X⊔mark_l S kR Y'') (fun a b=>lyric G t' W Y' X Y'' P1 P2 a b U' Tg):=by
 funext i; unfold lyTerm lockP curbY; simp only [Finset.sum_apply,Pi.single_apply]; split_ifs; swap; · simp
 let Z(a b:SU.Slot):=orbitPH (Y' U') (P1,a) (P2,b); let L:=fyL G true W β X; let Q:=fyL G false W β Y''
 let H (v w:Single (mid N B))(p q:SU.Slot):ℂ:= (star (L P1 v.1 p v.2))*Z p q*Q P2 w.1 q w.2
 let S'(p q:SU.Slot)(v w:Single (mid N B)):= H v w p q • gateY v w
 unfold legM; simp_rw [sum_mul_sum, Finset.smul_sum]
 have he (a b:SU.Slot)(v w: Single (mid N B)) : Z a b • ((barO Tg W t' true (P1,a) v X) • put ((true,v): LeanV _) * ((barO Tg W t' false (P2,b) w Y'') • put (false,w)))= S' a b v w:=by
    rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul,smul_smul]; unfold S' H; congr 1; change Z a b * star (L P1 v.1 a v.2) * Q P2 w.1 b w.2 = _; rw [mul_comm (Z a b)] -- tune
 let A(v w:Single (mid N B)):=∑ p:SU.Slot, ∑ q:SU.Slot,S' p q v w
 have hx(v w:Single (mid N B)): ∑ p:SU.Slot,∑ q:SU.Slot,H v w p q=lyric G t' W Y' X Y'' P1 P2 v.1 w.1 U' Tg v.2 w.2:=by
    unfold lyric; rw [Matrix.mul_apply]; simp_rw [Matrix.mul_apply, Finset.sum_mul]; rw [sum_comm]; refine sum_congr rfl fun i _=>sum_congr rfl fun j _=>?_ ; rfl
 have hp(v w:Single (mid N B)): A v w=(lyric G t' W Y' X Y'' P1 P2 v.1 w.1 U' Tg v.2 w.2) • gateY v w:=by unfold A S'; rw [←hx]; simp_rw [sum_smul]
 simp_rw [show ∀ v w:SU.Slot,orbitPH (Y' U') (P1,v) (P2,w)=Z v w from fun _ _=>rfl, he]; calc
    _ = ∑ v:Single (mid N B),∑ w:Single (mid N B),A v w:=by unfold A; simp_rw [sum_comm (s:= (univ:Finset SU.Slot)) (t:= (univ:Finset (Single (mid N B))))]
    _ = _:=by rw [Fintype.sum_prod_type]; apply sum_congr rfl; intro a _; simp_rw [Fintype.sum_prod_type (fun b:Single (mid N B)=>_)] -- tune maybe loops
              rw [sum_comm]; -- likely outer binder.RHS tune
              refine sum_congr rfl fun b _=>sum_congr rfl fun i _=>sum_congr rfl fun j _=>hp (a,i) (b,j)
end
end YM.CF.Oath
