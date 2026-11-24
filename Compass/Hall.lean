import Compass.Spokes
import Compass.Poetry
import Compass.Reynolds
import Compass.Bullion
import YM.CF.Neon.Ten
import Compass.Hubs
import YM.CF.Ione.Jost
import Compass.Lode
import YM.CF.Brood.Tips
import YM.CF.Coal.Vice
import YM.CF.Moto.Band
import YM.CF.Moto.Kearn
import Compass.Jazz
import Compass.Needle
import Compass.Sloop
import YM.Push.LOCAL_SPLITTING.Orientation
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Compass
open Py
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
-- certify.WAGES off all granted tasks
variable {u Hh pK qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Moto
open Vow Lilt Larch Bake Rue
open Prism Hove Oise
variable {Nq:Side}
open Ione
open scoped Mew
local notation "Ck"=> carriers Nq
open Neon

abbrev pecs (s:staff Nq)(F:Copy Nq):=turn_V s.val F
abbrev pad{E:Type*}[AddCommGroup E][Module ℝ E](o:Site Nq)(x:E)(V:staff Nq→E→ₗ[ℝ]E):= meanX orbitT V taxK o x
abbrev share (i y:Site Nq):ℝ:= ((frames orbitT i y).card:ℝ)⁻¹ -- implicit Nq staff? 
abbrev taxN (i y:Site Nq)(v:staff Nq):ℝ:=share i y*taxK v
lemma pool(n:Site Nq)(x:ℂ)(z: Site Nq)(s:staff Nq):castPay s (pad n x castPay (orbitT s z))=taxK s • pad n x castPay z:=reyn _ _ _ n z camaraderie seal_t propK (fun i=> (prop1 i).2) x s -- order args #
lemma pools(n z:Site Nq)(s:staff Nq):
   (∀ (E:RegBudget Nq),backing s (pad n E backing (orbitT s z))=taxK s • pad n E backing z) ∧
    ∀ K:Cusp Nq,cuspan s (pad n K cuspan (orbitT s z))=taxK s • pad n K cuspan z:=by
 constructor
 · exact fun E=> reyn _ _ _ n z camaraderie port_θ propK (fun i=> (prop1 i).2) E s
 exact fun K=> reyn _ _ _ n z camaraderie agenda propK (fun i=>(prop1 i).2) K s
variable {E:Type*}[AddCommGroup E][Module ℝ E](W:E)(V:staff Nq→E→ₗ[ℝ]E)(n i:Site Nq)
lemma framesTo : ∑ j∈frames orbitT n i,taxN n i j • V j W=pad n W V i:=by
 unfold pad meanX; simp only; rw [Finset.smul_sum]; simp_rw [smul_smul]
lemma shares_pos:0<share n i:=inv_pos.mpr (Nat.cast_pos.mpr (card_pos.mpr (transits i n)))
lemma sumshares:∑ j∈frames orbitT n i, |taxN n i j|=1:=by
 simp_rw [taxN,abs_mul,abs_of_pos (shares_pos n i),show ∀ j:staff Nq, |taxK j|=1 from fun j=>(prop1 j).1]; rw [Finset.sum_const, nsmul_eq_mul,mul_one]; exact mul_inv_cancel₀ ((inv_pos.mp (shares_pos n i)).ne')
lemma union_frames(z:Site Nq→E)(D:staff Nq→E)(p:∀ j∈frames orbitT n i,D j=taxK j • z i): (∑ j∈frames orbitT n i,taxN n i j • D j)=z i:=by
 rw [Finset.sum_congr rfl (g:=fun j=>share n i • z i) (fun j t=> by rw [taxN,p j t,smul_smul,mul_assoc,(prop1 j).2,mul_one]),sum_const,←Nat.cast_smul_eq_nsmul ℝ, smul_smul,mul_inv_cancel₀ ((inv_pos.mp (shares_pos n i)).ne'), one_smul]
variable (o:Site (mid N B))(X0:Cusp (mid N B))(z0:ℂ)(V0:RegBudget (mid N B))(M0:ArcΦ)(Q:BudgetPoint)(h Eμ Kμ Cμ:ℝ)
abbrev approve (M0:ArcΦ)(o i:Site Nq):ArcΦ:=∑ j∈frames orbitT o i,taxN o i j • tiltA j.val M0
variable (F1:Site (mid N B)→ Copy (mid N B))
lemma padEngine (L:ℕ)(u:Ice L o Q h Eμ Kμ Cμ (F1 o) V0 X0 z0 M0)(h':1≤h)(y:Site (mid N B))(v:∀ (s:staff (mid N B)),orbitT s y=o→ pecs s (F1 o)=taxK s • F1 y)(g:4≤(More (mid N B)).val)(z:∀ i:Scree.Hub (mid N B),chose L Q i→ Nonwrapping i.val.2 i.val.1):
  Ice L y Q h (duty_Q Q.order Q.power * Eμ) (strive_E Q.order * Kμ) Cμ (F1 y) (pad o V0 backing y) (pad o X0 cuspan y) (pad o z0 castPay y) (approve M0 o y):=by
 let VA:= staff (mid N B); let p(s:VA):=orbitT s y=o; have hu(s:VA)(e:p s):Ice L (inspire s.val y) Q h Eμ Kμ Cμ (F1 o) V0 X0 z0 M0:=e.symm ▸ u -- ▸ rewrites F1 o
 have hp(s:VA)(t:s∈frames orbitT o y):= turnBullion h s.val s.property y Q L Eμ Kμ Cμ (F1 o) V0 X0 z0 M0 (hu _ (mem_filter.mp t).2) h' g z
 have hq:= verses Q (fun s:VA=> pecs s (F1 o)) (fun s:VA=>backing s V0) (fun s:VA=>cuspan s X0) (fun s:VA=>Spire.payZ s.val⁻¹ z0) (fun s:VA=> tiltA s.val M0) h (duty_Q Q.order Q.power * Eμ) (strive_E Q.order * Kμ) Cμ y L (frames orbitT o y) hp (zero_le_one.trans h') (taxN o y)
 -- challenge β reducible let. redefine using z'. use wage_t anticipated to replace function E entry via hand proof
 have eq : (fun s:VA=>Spire.payZ s.val⁻¹ z0)=(fun s=>castPay s z0):=funext fun s=>(wage_t s z0).symm
 have hz (s:VA)(t:s∈frames orbitT o y) :=v s (mem_filter.mp t).2
 have hvq:= union_frames o y F1 _ hz
 rw [sumshares] at hq
 simp only [one_mul] at hq
 rw [framesTo,framesTo,hvq] at hq
 have hd:(∑ s∈frames orbitT o y,taxN o y s • Spire.payZ s.val⁻¹ z0)=pad o z0 castPay y:= (sum_congr rfl (fun i _=> congrArg (fun t=>taxN o y i • (t:ℂ)) (Eq.symm (wage_t i z0)))).trans (framesTo ..)
 replace hq:= hq; -- dsimp.unfold? match
 rw [hd] at hq; exact hq
#check turnBullion
#check reyn
#check union_frames
end YM.CF.Compass
