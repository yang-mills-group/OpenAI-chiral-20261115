import Organdy.Backlit
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
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
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
open Tapestry Advance Papyrus Papyrus.Franc
variable {n:Side}
open Py.Rate.Pannier CF.Pannier Chancel Rous Pressure Worth Worth.Pays Graph
/-! # Sparse projection resulting state & compass; holder price use ANY such solid mover at this height below purchase. -/

open Regis Lamour.Bridge Organdy Organdy.Optic
namespace Bazaar
open Larva (Chip Domaine dint)

open Papal Celeste Clock Hookah Rake Cliplet
local notation "θx" s:max=>hat P.R.L P.x s
local notation "N" s:max i:max=> (Journey.side Y i s)
local notation "ℰ" s:max=> meterC (θx s)
set_option linter.unusedVariables false
set_option maxRecDepth 4000
variable {v b ζ:ℝ}
 (Z:∀ᶠ s in atTop,∀ᶠ i in atTop,∀ k:ℕ,(Y.voyage i).kick ≤ k → s≤Y.uv k→ ShelterCost v Y s i k)
 (c:0<ζ)
include Z c
omit Z c

-- Product with reflected scalar across gauge plane at -d on e₃.
def plateM(W:Pane n→ℂ) (x:ℝ):Buffered.Mark n:=
  fun U=> ((x:ℂ)* W U.1) • 1
def planeM(W:Pane n→ℂ)(x:ℝ)(d:ℕ):Buffered.Mark n:=
  let F:=plateM W x
  reflMark timeAxis (-(d:ℤ)) F * F

lemma markPlane (W:Pane n→ℂ)(x:ℝ)(d:ℕ):
 planeM W x d = markPair x W (Optic.ice _ (2*d)):=by
 have hx:wrap (More n) (2 • ((-(d:ℤ)) • step timeAxis)) = Optic.ice _ (2*d):= by
   rw [Optic.ice, neg_smul, natCast_zsmul, map_nsmul, map_neg, map_nsmul,wrap_step,smul_neg,mul_smul]
 funext U
 change Fock.theta (carR timeAxis (-(d:ℤ)) n) ((x*W (fling timeAxis (-(d:ℤ)) n U.1)) • 1) * ((x*W U.1) • (1:FC (Single n))) = cistern x W (Optic.ice _ (2*d)) 1 0 U.1 • (1:FC (Single n))
 simp only [theta_smul, theta_one,fling_eq,hx,
   cistern,wares, mul_smul_comm,mul_one,Complex.star_def]
 have p:∀ o:Pane n,Lattice.pull 1 0 o=o:= fun o=>pull_id _
 simp only [p,one_mul,affine,Signed.act_one, add_zero, ←mul_smul]

lemma var_mark (x y:ℝ) (W:Pane n→ℂ)(z:Site (More n)):
  markPair (x*y) W z=(x^2:ℂ) • markPair y W z:=by
 funext U
 simp only [markPair,Pi.smul_apply]
 rw [←mul_smul]
 unfold Optic.cistern Optic.wares
 push_cast
 simp only [map_mul,Complex.conj_ofReal]
 congr 1
 ring
def distanceP (d:ℕ):ℝ:=(d:ℝ)/2
def reach (x:ℝ)(d:ℕ):Prop:=
  let w:=webX x
  w^99/2 ≤ distanceP d ∧ distanceP d≤ 2*w^101
structure Policy (C:ℝ)(s i k:ℕ)(W:Pane (N s i)→ℂ):Prop where
  grant : matchedX (θx s) (RootBook Y i k s).beta
  plan (d:ℕ):reach (θx s) d →
     ∀ u β:ℝ,(θx s)/2 ≤ β →
      C*(u/(β*(distanceP d)^4))^2 ≤ (Journey.compass Y i k s (planeM W u d)).re
abbrev gleamδ (δ:ℝ):= Optic.premium Optic.argent δ / (8*4^8)

variable {s i k:ℕ}
lemma worthVar (z:Site (More (N s i)))(u x:ℝ)(W:Pane (N s i) →ℂ):
 (Journey.compass Y i k s (markPair (u*x) W z)).re =
    (u^2)*(Journey.compass Y i k s (markPair x W z)).re:=by
 unfold Journey.compass
 rw [var_mark,mark_smul,mul_div_assoc,← Complex.ofReal_pow,Complex.re_ofReal_mul]

lemma equalBudget {r β u x δ:ℝ}
    (a:0<x)(b:0<δ)(q:x/2≤β)(p:0<r):
   (gleamδ δ * (u/(β*r^4))^2) * (4*r)^8 ≤
     (u/x)^2*(Optic.premium Optic.argent δ / 2):=by
 have v:0<x/2:=half_pos a
 have t':u^2 /(β^2)≤ u^2/((x/2)^2):=by gcongr
 rw [gleamδ]
 calc
   _ = u^2/(β^2)*(Optic.premium Optic.argent δ / 8) := by field_simp
   _ ≤ u^2/((x/2)^2)*(Optic.premium Optic.argent δ/8):=
      mul_le_mul_of_nonneg_right t' (by have j:=premium_pos argent_pos b; positivity)
   _ = _:= by field_simp; ring

variable (H:Real.exp 1≤ P.x)
include Z H c
lemma banking {δ:ℝ}(d:0<δ) :
   ∀ᶠ s in atTop, ∀ᶠ i in atTop, ∀ᶠ k in atTop,
     let x:=θx s; let w:=webX x; ∀ (l:ℕ), (l:ℝ)≤w → ∀(W:Pane (N s i)→ℂ)
       (A:Organdy.Ink (Chip (More (N s i)))),
       Domaine l ζ (temp x) (stow x) b W A → δ ≤dint A →
       Policy Y (gleamδ δ) s i k W :=by
 filter_upwards [backlit (b:=b) Y Z c H d,(turnover P).eventually (aisleWide 8),
   (turnover P).eventually (eventually_gt_atTop 0)] with s p a ax
 filter_upwards [p] with i g
 filter_upwards [g,ferry_later Y s i] with k h m x w l t W A E v
 refine ⟨(Papal.prices_plot Y s i k m.enters).2.2.2.1,
    fun r j u β L=>?_⟩

 have y:4*distanceP r = ((2*r:ℕ):ℝ):=by unfold distanceP;push_cast;ring

 obtain ⟨q1,q2⟩:=j
 have w1:0<w:=lt_of_lt_of_le (by norm_num) a.gw

 have y': 0<distanceP r:=(half_pos (pow_pos w1 _)).trans_le q1
 have k':=h l t W A E v (2*r) (show Plait w (2*r) from by
    constructor
    · rw [←y];linarith only [y',q1]

    rw [←y,show (102:ℕ)=1+101 from rfl,pow_add,pow_one]
    linarith only [q2, mul_le_mul_of_nonneg_right (show 8≤w from a.gw) (pow_pos w1 101).le])
 let z:=Optic.ice (More (N s i)) (2*r)
 have kk:(Optic.premium Optic.argent δ)/2≤
     (4*distanceP r)^8*(Journey.compass Y i k s (markPair x W z)).re:=by rw [y]; exact k'
 rw [markPlane, show u=u/x*x from (div_mul_cancel₀ u ax.ne').symm]
 rw [worthVar Y z,div_mul_cancel₀ _ ax.ne']
 apply (mul_le_mul_iff_left₀ (pow_pos (show 0<4*distanceP r by positivity) 8)).mp
 exact (equalBudget ax d L y').trans ((mul_le_mul_of_nonneg_left kk (sq_nonneg _)).trans_eq (by ring))
