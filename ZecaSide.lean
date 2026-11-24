import ZecaSparks
import ZecaSlip
import SatinThinQuizPair
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 400000
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
namespace Spine
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets

variable (P:Spine) (x:P.Spectrum0 3)


local notation "ξ"=>P.advocate 3 x 3
local notation "S"=>P.seasons 3 ξ
local notation "G"=>P.ManyF 3 ξ
local notation "ε"=>P.physicalEnergy 3 ξ
local notation "Ω"=>P.heaven 3 ξ
local notation "ν"=>P.nv 3 ξ
local notation "E"=>(P.seasons 3 ξ).E
open Hierarchy.Seld.Zeca
open Hierarchy.Seld (parabola M)

open DoseTravel Set

variable (A:ℕ→P.Apron) (c r n:ℕ→ℕ) (w:Lead.Clan→Prism)
 (V : ∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))(g h:ℕ)
 (T:P.HandleWith x c r A n)(R:P.ThinArmada x A c r n w T V g h)(J:P.Ellis 3 x)


variable (D:Cilium P x)
 (b:∀i, P.Lustre 3 (P.advocate 3 x 3) (D i) (P.soldTrumpet A c r n w i))

local notation "ℒ"=>Lead.Clan


def ripple (t:ℝ):Vantage:=fun j=>if j=3 then t else 0
lemma ripple_cont:Continuous ripple:= continuous_pi fun i=>by
 unfold ripple
 by_cases h:i=3
 · simp_rw [if_pos h]; exact continuous_id
 simp_rw [if_neg h];exact continuous_const
lemma ripple_zero: ripple 0=0:=by ext; simp [ripple]

def minkX(F:SampleDose)(z:ℒ):G:=Hierarchy.Seld.Zeca.awake S ν (D z) (att F)

/-- Minkowski X! Earlier is dagger; includes vacuum and team. Strict physical gap. -/
def minkPrice (F U:SampleDose):CrossRead:=
 Matrix.of (fun i j:ℒ=>inner ℂ (P.minkX x D F i) (P.minkX x D U j))

lemma mink_is(F U:SampleDose)(i j:ℒ):
 P.minkPrice x D F U i j=
 inner ℂ Ω ((D i).dagger.field S (att F)
       ((D j).field S (att U) ν)).val:=by
 have h:= awake_m S ν (D i) (att F) (D j) (att U)
 rw [att_b] at h
 exact h

lemma M_factor(p:Vantage): M S (homeV p)= (S).edge (p 3)*P.cartage 3 ξ p:=by
 rw [P.uses_cart]
 change _=(S).edge _*(S).U (poseSp 3 p)
 have e:SEP 3 (homeV p)=poseSp 3 p:= by
    rw [eyes_toFace 3 (SEP 3 (homeV p))]
    unfold poseSp
    apply congrArg; ext1 i
    change (homeV p - (homeV p) 3 • _root_.YM.basis 3) i.val=p i.val
    rw [PiLp.sub_apply,PiLp.smul_apply]
    have t:_root_.YM.basis 3 i.val=0:=by simp [i.property]
    rw [t,smul_zero,sub_zero];rfl
 change (S).edge _ * (S).U (SEP 3 (homeV p))=_
 rw [e]
 rfl

lemma M_ripple(t:ℝ): M S (homeV (ripple t))= (S).edge t:=by
 rw [P.M_factor,show ripple t 3=t from if_pos rfl]
 have e:P.cartage 3 ξ (ripple t)=P.cartage 3 ξ 0:= by
    rw [P.cart_m,P.cart_m]
    congr 1
    apply congrArg
    unfold poseSp
    apply congrArg
    ext1 i
    exact if_neg i.property
 rw [e,P.cart_zero]; rfl


lemma mintshift(q:Vantage)(i:ℕ)(t:ℝ)(j:ℒ):
 P.minkX x D (skate (q+ripple t) i) j=
 (S).edge t (P.minkX x D (skate q i) j):=by
 rw [←P.M_ripple x]
 exact skate_move S ν (P.nova 3 ξ) (D j) q (ripple t) i

lemma edge_inner {H:Hilbert}{a:Axis}(G':OS.Semigroup H a)(t:ℝ)(x y:H):
 inner ℂ (G'.edge t x) (G'.edge t y)= inner ℂ x y:=
 LinearIsometry.inner_map_map (show H →ₗᵢ[ℂ] H from
 { (G'.edge t).toLinearMap with norm_map':= fun _=> G'.life _ _ }) x y

lemma back_cart {p q:Vantage}(y z:G):
 inner ℂ (M S (homeV p) y)
         ((S).edge (-(q-p) 3) (M S (homeV q) z))=
 inner ℂ y (P.cartage 3 ξ (q-p) z):=by
 have e:(S).edge (-(q-p) 3) * (S).edge (q 3)=(S).edge (p 3):=by
   apply Eq.trans ((S).send _ _)
   congr 1
   rw [Pi.sub_apply]
   ring
 rw [P.M_factor,P.M_factor]

 change inner ℂ ((S).edge (p 3) (P.cartage 3 ξ p y))
        (((S).edge (-(q-p) 3) * (S).edge (q 3)) (P.cartage 3 ξ q z))=_
 rw [e,edge_inner,←ContinuousLinearMap.adjoint_inner_right,P.cart_reverses,←ContinuousLinearMap.comp_apply,
     ←P.cart_paves, neg_add_eq_sub]
