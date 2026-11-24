import Merino.Dais.Climb
import Merino.Dais.Steps
import Merino.Coin.Spoils
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Dais
open YM.CF.QuadClock
open Neon
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew Waxy Roots Rive Oise


open Py.Rate Py.Rate.LocalLimit Py.Rate.LocalLimit.Preparation
open Pitching Pitching.Focus Fief

open Buffered Afterglow Tower.VacuumSelection
variable (P:Spine)(s i k:ℕ)

abbrev climbRatio := apt (P.run.ir i) P.par.block P.par.R.L s
abbrev staircase:= Stem P.run i k s
abbrev XP:=(((P.run.voyage i).X (P.run.uv k)).wave s).val
abbrev liftCoat
 (Pay kc G:ℝ)(Tξ:Hove.Grant P.par.K.j 2)(n:ℕ):=
 works_X (K:=P.par.K) Tξ n 6 5 HI Pay kc G

local notation "X"=>LedgerM P s i k
local notation "Y"=>LedgerM P (s+1) i k
local notation "x"=>scaleM P s
local notation "L"=>P.par.R.L
local notation "Pp"=>P.par
local notation "g"=>climbRatio P s i
local notation "σ"=>staircase P s i k
local notation "NN"=>RegNum P s i
local notation "Nf"=>RegNum P (s+1) i
local notation "cf"=>Chi.canonical
local notation "Xp"=> XP P s i k
local notation "Cf"=>cipherK P.par.J.n
local notation "Mo"=> LoomM P s i
local notation "Mm"=> LoomM P (s+1) i
local notation "Qf"=> Corolla.cur L
local notation "b"=> (3*dleaf L x)
local notation "h"=>P.par.h
variable (p:Bolts)
variable (A: ArmorK)(Γϕ:ℝ)(Mc:ℕ) (Z W V1 Kf:ℝ→ℝ)
local notation "C"=>colorsPhi L Γϕ x
variable (u f:ℕ)
local notation "v"=> Corolla.cur L f (scaleM P (s+1))


/-- Live stage for all consultations at given tuning-load. -/
structure Stride (f u:ℕ)
 (O:Observatory g (X).p)(K:Cusp NN)(Ca:ArcΦ→ℝ→ℝ):Prop where
 scale: StairBills P.par.R f x u Γϕ (W x)
 base: Arc_r Y h b b b
 funding: AstroFunding P.par.V P.par.U g σ Mo Mm X Y Xp cf P.par.J.d h (V1 x) (Kf x) (W x)
   A.delta A.f0 A.g0 A.g1 A.g2 (b+C) C (Z x) Cf Mc
 jet: OrbitJet P.par.V P.par.U g σ Mo Mm X Y Xp cf P.par.J.d h (V1 x) (Kf x) (W x)
   A.delta A.f0 A.g0 A.g1 A.g2 (b+C) C (Z x) O K Ca Cf Mc


lemma arc_r (r:Capsule P.par.R x)(a:s < P.run.uv k):
 Arc_r Y h b b b:=by
 obtain ⟨_,_,_,_,H⟩:=Papal.prices_plot P.run (s+1) i k a
 rw [hat_step] at H
 have ht:=show dleaf L (x+Vale.billX L) ≤ b from r.lower.trans
    (le_mul_of_one_le_left r.high.le (by norm_num))
 exact ⟨Provides.liftE h Y _ _ H.reg ht,Provides.liftE h Y _ _ H.slip ht,
    Provides.liftQ h Y _ _ H.force ht⟩

/-- Daily. -/
structure Arrival (f u:ℕ) (a c:ℝ): Prop where
 prizes: ∃ O K Ca,Stride P s i k A Γϕ Mc Z W V1 Kf f u O K Ca
 worth: Coin.Worthy P (s+1) i k p f u a c


section invitations
def Cotillion (P:Spine)(p:Bolts)(Mc:ℕ): Prop:=
 ∃ (F D:ℝ→ℝ) (Pay kc Γf:ℝ) (T:Hove.Grant P.par.K.j 2) (n:ℕ)
   (Z W V1 Kf:ℝ→ℝ), BPress.NPL F∧ BPress.NPL D∧
    Sweepcraft P.run T Pay kc Γf n Mc ∧ BladeQ P.par.R Z W V1 Kf ∧
    let A:=liftCoat P Pay kc Γf T n
    ∀ f u:ℕ,∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,
      ∀ k:ℕ, admitM P (s+1) i k→
      Arrival P s i k p A Γf Mc Z W V1 Kf f u
      (|F (scaleM P (s+1))|) (|D (scaleM P (s+1))| * Qprice P (s+1))

lemma hosted {C0:P.Register}{z:P.Spectrum0 3} (d:Gala P C0 z Mc)
 (r:Coin.Windfall P p):Cotillion P p Mc:=by
 obtain ⟨Pay,kc,Γf,T,n,a'⟩:=d.forward
 obtain ⟨Z,W,V1,Kf,H,go⟩:=a'.scene
 obtain ⟨F,D,v1,v2,e⟩:=r
 refine ⟨F,D,Pay,kc,Γf,T,n,Z,W,V1,Kf,v1,v2,a',H,?_⟩
 dsimp only
 intro y m
 have post:=(turnover P.par).eventually (stairBills _ y m Γf P.par.V W H.high)
 have t:=later (e y m)
 filter_upwards [t,go,post] with a r v' j
 filter_upwards [r,v'] with i c w k hit
 have l:a<P.run.uv k:=lt_trans (Nat.lt_succ_self _) hit.2
 have bill:=w k l
 obtain ⟨O,K,Ca,V⟩:=bill.trust
 exact ⟨⟨O,K,Ca,j,arc_r P a i k j.height l,bill,V⟩,c k hit⟩
end invitations
end YM.CF.Merino.Dais
