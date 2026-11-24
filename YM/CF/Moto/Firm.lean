import YM.CF.Moto.Trail
import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Weigh
import YM.CF.Moto.Plot
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Moto
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
variable {d e η tW z g b c AW B':ℝ} {j k k' m n l:ℕ}
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
local notation "CM"=> LeanV (Single Kx)
open Hove Oath
local notation "QΦ"=> Rock Kx
open Hove Haro Taxi
local notation "θn"=> (mid N B)
variable (U: InkD (mid N B)) (Φ:Scree.Hub (mid N B)) (o:Site (mid N B))(t:Φ.val.1=node o)(P₀:BudgetPoint)(hx:PressB P₀ Φ U v z) (w:1≤v)
variable (A:ℝ)(ht:DayT P₀.order A)(uA:0≤A)
local notation "KP"=> Φrap (mid N B) o 10
local notation "Hq"=> (KP)
local notation "TP"=> plateZ (node o) P₀ (tooth (Φ.val.1) P₀ U)
local notation "TU"=> crest_G P₀ o U
local notation "TΦ"=> crest_Y o U
local notation "QΨ"=> (jetsL o (orbitPH (U 1)))
variable (GG:Oath.Gala P₀.power P₀.order 100 x 3)(hz:1 ≤ radiusB x)(hv: P₀.threshold=temp x)(hK:20 < (More (mid N B)).val)(hk:3 ≤ (mid N B).val)(pK:1 ≤ P₀.power)
local notation "Vcφ"=> deck_K P₀.order P₀.power 10
local notation "Z0"=> crest_G P₀ o U
local notation "Z1"=> crest_Y o U
local notation "T_"=> (Z0+Z1)
local notation "Ψc"=> Taxi.lifeH U 1
-- build pressure.L. at new basis preserving weight4 on halo(++ FIXED). caloric
local notation "PΨ"=> cone_G P₀ o U
local notation "kΛ"=> (Φ.val.2 ∪ (KP).val.2)
local notation "Λξ"=> KP
local notation "ΩΦ"=> Ωbox o Φ 10
open Vow Bake Lilt Larch Rue
abbrev scrollY(K:Dome): InkD (mid N B):=pay_Y (N:=N) (B:=B) (spring_V K o)
local notation "Hook"=> (Φrap (mid N B) o 10)
local notation "s_"=> node o
local notation "S0"=> spring_V
local notation "HP"=> Haro.orbitPH
lemma spenG(G V:Skate): plateZ (node o) P₀ (G+V)= plateZ (node o) P₀ G+plateZ (node o) P₀ V:=by
 let p:=P₀; let H(i:Skate):=plateZ s_ P₀ i; have hk(t:Pane (mid N B)) : kerP s_ P₀ (G+V) t=kerP s_ P₀ G t +kerP s_ P₀ V t:=by
    unfold kerP; simp_rw [Pi.add_apply]; unfold AnalyticBridge.VerifiedReset.counter AnalyticBridge.VerifiedReset.quad; simp_rw [Complex.add_re,Complex.add_im,add_div,add_mul, sum_add_distrib,add_div,Complex.ofReal_add]; ring
 funext i; apply Subtype.ext; unfold plateZ; rw [hk]; change (_+_) • (1:FC (LeanV (Single (mid N B))))=_; rw [add_smul]; rfl
lemma spenZ: plateZ s_ P₀ 0=0:=by
 funext i; apply Subtype.ext; rw [plateZ]; unfold kerP AnalyticBridge.VerifiedReset.counter AnalyticBridge.VerifiedReset.quad; simp only [Pi.zero_apply,Complex.zero_re,Complex.zero_im,_root_.zero_div,zero_mul,sum_const_zero,Complex.ofReal_zero,add_zero]; unfold Pastry.hollow; dsimp only; rw [zero_smul]; rfl -- tune
lemma φ_add(P Q: Op (Single (mid N B))) : pay_Y (N:=N) (B:=B) (P+Q)= pay_Y P+pay_Y Q:=by
 funext v; apply Subtype.ext; let i:= v; let Bx:=Prism.Rock (mid N B); change cashF _ i=cashF P i+cashF Q i; unfold cashF; simp_rw [←sum_add_distrib]; exact sum_congr rfl fun j _=>sum_congr rfl fun z _=>by
    unfold cars_P Haro.taxi; rw [show boxM (P+Q) j z=boxM P j z+boxM Q j z from rfl, add_mul]; unfold lineY; simp only [Matrix.add_apply,add_smul,sum_add_distrib]
lemma κput(L J:Dome): spring_V (L+J) o=spring_V L o+ spring_V J o:=by
 let g(x y:Site (mid N B))(P):= bud_k o x y P; have hp(x y:Site (mid N B))(u v:Tap.Pal): bud_k o x y (u+v)=g x y u+g x y v:=by ext i j; change (if _ then _ else _)= _; simp only [g, bud_k,seed_k, Matrix.of_apply, Matrix.add_apply,smul_add]; split <;> simp
 unfold spring_V; simp only [Prod.fst_add,Prod.snd_add,Pi.add_apply,hp] -- tune Prod lemma
 -- distribute.S
 simp only [Finset.sum_sub_distrib,sum_add_distrib,g]; abel
lemma κzero:spring_V (0:Dome) o=0:=by
 have ht:= κput o 0 0; rw [zero_add] at ht; exact add_left_cancel (show spring_V 0 o+_=spring_V 0 o+_ from ht.symm.trans (add_zero _).symm)
lemma sent(l q:Dome): scrollY o (l+q)= scrollY o l+scrollY o q:=by unfold scrollY; rw [κput,φ_add]
lemma term_0: scrollY o 0=0:=by
 have ht:= sent o 0 0; rw [zero_add] at ht; exact add_left_cancel (by change scrollY o 0+ _= _+(_ : InkD _); rw [←ht,add_zero]) -- tune
lemma Sperm {ι:Type*}[DecidableEq ι](W:Finset ι)(V:ι→Dome): scrollY o (∑ i∈W,V i)=∑ i∈W,scrollY o (V i):=by
 induction W using Finset.induction with
 | empty=> simp_rw [sum_empty]; exact term_0 o
 | insert i s z u=> rw [sum_insert z,sum_insert z,sent,u]
lemma permG {ι:Type*}[DecidableEq ι](W:Finset ι)(V:ι→Skate): plateZ (node o) P₀ (∑ i∈W,V i)=∑ i∈W,plateZ (node o) P₀ (V i):=by
 induction W using Finset.induction with
 | empty=> simp_rw [sum_empty]; exact spenZ ..
 | insert i s z u=> rw [sum_insert z,sum_insert z,spenG,u]
end YM.CF.Moto
