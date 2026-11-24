import Velour.Wadding.Tapes
import Velour.Wadding.Violet
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 1250000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set

namespace Spine
open _root_.YM.CF.Buffered.Afterglow.Hierarchy
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Sesame.FlakeNight
open FirstWindows FirstWindows.Chambers FirstWindows.LightBudget

open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set

open _root_.YM.SatinEdge.RealSheet Boundary Probe

open YM.Velour

variable {P:Spine}{K:P.Register}{c r:ℕ→ℕ}{x:P.Spectrum0 3}
local notation "ξ"=> P.advocate 3 x 3
local notation "ω"=> P.colorZero 3 ξ
local notation "σ"=> P.physicalEnergy 3 ξ
local notation "π'"=> P.wealth 3 ξ
local notation "ℋ"=> P.ColorHil 3 ξ
local notation "G"=> P.ManyF 3 ξ
local notation "ℰ"=> P.seasons 3 ξ
local notation "C"=> Lead.Clan
variable {R:P.Ellis 3 x}{i₀:ℕ}{F U:SampleDose}{A:ℕ→P.Apron}{n:ℕ→ℕ}{w:C→Prism}
    {V: ∀ j : Axis, List Axis → ℝ → P.ColorHil j (P.advocate 3 x j)}
    {g h : ℕ} {X : P.HandleWith x c r A n}
variable {realY : C → Test4 →L[ℂ] P.ManyF 3 (P.advocate 3 x 3)}{Z:C→C→Boundary.Distn E4}
local notation "𝓕₄"=> M4Furnish P K c r x R i₀ F U A n w V g h X realY Z
local notation "𝓑"=> P.Bobbin 3 ξ
local notation "D"=> (ℰ).muslin
local notation "Ω"=> P.firstTulle 3 ξ
local notation "θ"=> P.detects 3 ξ
local notation "Q"=> P.bobQuote 3 ξ
local notation "γ"=> P.ThinVelour x A c r n w
local notation "Λ"=> P.profilesZ x V w


lemma star_flounce (P:Spine)(j:Axis)(x:P.Spectrum0 j)(l r d:ℝ)(T:(P.ManyF j x).Op)
    (F:SampleDose)(y:P.ManyF j x):
 star (P.flounce j x d l r T F) y=
    ∫p,(F.val p:ℂ) • P.cartage j x p
      ((((P.seasons j x).pad (r-p j-d) (p j-l-d) (star T))
        ((P.cartage j x (-p)) y))):=by
 let W:=P.cartage j x
 let H':=P.ManyF j x
 let Z':Vantage→(P.ManyF j x).space:=
    fun p=>W p
      (((P.seasons j x).pad (r-p j-d) (p j-l-d) (star T))
        (W (-p) y))
 have hp:Continuous Z':=by
    simp_rw [Z',pad_val,mul_apply_eq_comp]
    exact P.caravan _ _ _ _ continuous_id
      (vet_heat _ (by fun_prop)
        ((star T).continuous.comp
          (vet_heat _ (by fun_prop)
           (P.caravan j x _ _ continuous_neg continuous_const))))
 have hz:=velvet_integrable F hp

 apply ext_inner_left ℂ
 intro v
 change _=inner ℂ v (∫p,(F.val p:ℂ) • Z' p)
 rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right,P.flounce_act]
 rw [←integral_inner hz]
 rw [← inner_conj_symm] -- ?
 rw [←integral_inner (velvet_integrable F (P.cloaked_cont j x d l r T v)),←integral_conj]
 refine integral_congr_ae (Eventually.of_forall fun p=>?_ )
 have e: Z' p=star (P.cloaked j x d l r T p) y:=by
    rw [cloaked,star_mul,star_mul,star_pad,ContinuousLinearMap.star_eq_adjoint (P.cartage j x _),
       ContinuousLinearMap.star_eq_adjoint (P.cartage j x _),P.cart_reverses,P.cart_reverses, neg_neg]
    rfl
 beta_reduce
 rw [inner_conj_symm,e, inner_smul_left, inner_smul_right,
     ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right, Complex.conj_ofReal]

namespace M4Furnish
variable (u:M4Furnish P K c r x R i₀ F U A n w V g h X realY Z)(e:P.ThinVelour x A c r n w)
local notation "E"=> (ℰ).E
local notation "𝓦"=> P.cartage 3 ξ
local notation "ς"=> P.heaven 3 ξ
local notation "Β"=> u.violet e

def redGold (a:C): (G).Op:= P.bobbinEu 3 ξ (-3) 0 F 1 (Β a).windBack
def greenGold (a:C): (G).Op:= P.bobbinEu 3 ξ 0 3 U 1 (Β a)


include u
lemma corners :
 Corners 3 (-3) 0 F 1 ∧ Corners 3 0 3 U 1:=by
 constructor
 · intro y p
   have q : -2<y 3 ∧ y 3< -1 :=u.boxF p (3:Axis) (Set.mem_univ _)
   constructor <;> linarith only [q]
 intro y p
 have q:1<y 3 ∧ y 3<2:=u.boxU p (3:Axis) (Set.mem_univ _)
 constructor <;> linarith only [q]

lemma green_paid (a:C):
 u.greenGold e a ς=DoseTravel.beam G U (P.laterProfile x V w 1 a):=by
 rw [greenGold,bobbinEu, P.flounce_act]
 apply integral_congr_ae
 refine Eventually.of_forall fun p=>?_
 change _=(U.val p:ℂ) • _
 by_cases r:U.val p=0
 · simp [r]
 simp_rw [cloaked,pad_val,mul_apply_eq_comp,P.cart_empty, P.heaven_hot]
 have b:= (u.corners.2 p (subset_closure r)).1
 simp only [sub_zero] at b
 rw [show ς=(Ω).val by rfl,u.pay_origin e a 1 one_pos]
 rw [laterProfile,max_eq_right b,
    (u.lab.armada.energy a).2.1 1 _ zero_lt_one b]
 norm_num

lemma red_paid (a:C):
 star (u.redGold e a) ς=DoseTravel.beam G F (P.earlierProfile x V w 1 a):=by
 rw [redGold,bobbinEu,P.star_flounce]
 apply integral_congr_ae
 refine Eventually.of_forall fun p=>?_
 beta_reduce
 change _=(F.val p:ℂ) • _
 by_cases r:F.val p=0
 · simp [r]
 rw [←(Β a).backward one_pos, star_star]
 simp_rw [pad_val,mul_apply_eq_comp,P.cart_empty, P.heaven_hot]
 have b:= (u.corners.1 p (subset_closure r)).2
 rw [show ς=(Ω).val by rfl,u.pay_origin e a 1 one_pos]
 simp only [zero_sub] at b ⊢
 rw [earlierProfile,max_eq_right b,
    (u.lab.armada.energy a).2.1 1 _ zero_lt_one b]
 norm_num

lemma jewels_paid (a b:C):
 inner ℂ ς ((u.redGold e a * u.greenGold e b) ς)=P.readPrism x V w 1 F U a b:=by
 rw [mul_apply_eq_comp, ←ContinuousLinearMap.adjoint_inner_left,
   ←ContinuousLinearMap.star_eq_adjoint,u.green_paid,u.red_paid e]
 rfl

#print axioms jewels_paid
end M4Furnish
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

