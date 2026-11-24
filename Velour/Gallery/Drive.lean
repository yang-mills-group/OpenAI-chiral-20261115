import Velour.Gallery.Assay
/-! # Calendar price 
    Birth on each sleeve. -/
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


variable (P:Spine)(a:P.Spectrum0 3)(j:Axis)
local notation "ξ"=> P.advocate 3 a j
local notation "S"=> P.seasons j ξ
local notation "Ω"=> P.heaven j ξ


variable (A:P.Apron) (x:OS.Cross j)(s:ℝ≥0)
local notation "w"=> A.realWidth P j
local notation "B"=> A.kiss P j

def rear : Vantage:= fun i=>if i=j then 2*w+s else x.val i

lemma ferried :
 P.cartage j ξ (P.rear j A x s)=(S).U x:= by
 rw [P.uses_cart]
 refine congrArg _ (Eq.trans ?_ (eyes_toFace j x).symm)
 congr 1
 ext i; exact if_neg i.property

local notation "M"=> P.mounted j ξ
local notation "l"=> (-w-1)
local notation "o"=> (w+1)
local notation "r"=> (3*w+(s:ℝ)+1)
local notation "p"=> (0:Vantage)
local notation "q"=> P.rear j A x s
local notation "E"=> (S).E

def calendar (v:P.ManyF j (P.advocate 3 a j)):ℝ:=
 (inner ℂ v ((S).U x (E s v))).re
def plate :=
 P.calendar a j x s (M A Ω)



lemma plate_price (h:2 ≤ s):
 P.scrollprice a j p q A l o r = P.plate a j A x s:= by
 have z:(q) j=2*w+s:=if_pos rfl
 have g:(o-(p) j-w).toNNReal+((q) j-o-w).toNNReal=s:= by
    have hs:(2:ℝ) ≤ s:= by exact_mod_cast h
    simp only [Pi.zero_apply,z]
    rw [← Real.toNNReal_add (by linarith only [hs] : 0 ≤ w+1-0-w)
              (by linarith only [hs] : 0 ≤ 2*w+(s:ℝ)-(w+1)-w)]
    ring_nf
    rw [Real.toNNReal_coe]
 unfold scrollprice plate calendar
 simp only [cloaked,pad_val, neg_zero,mul_apply_eq_comp,
    P.cart_empty,P.cart_zero, ContinuousLinearMap.id_apply,P.heaven_hot]
 rw [← ContinuousLinearMap.adjoint_inner_left, (S).sym _,P.heaven_hot,
     ← P.sleeve_star,ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right,P.ferried]
 rw [← ContinuousLinearMap.comp_apply (g:=E _), (S).independent,ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.comp_apply (g:=E _),← (S).time,g]


def slap (b:ℕ×ℕ) : ℝ:= P.beads a j p q A b.1 b.2
lemma slap_plate (J:P.Ellis 3 a) (h:2 ≤ s):
 Tendsto (P.slap a j A x s) kindling (𝓝 (P.plate a j A x s)):=by
 rw [← P.plate_price a j A x s h]
 apply P.assay _ _ _ _ _ _ _ _ J
 · simp only [Pi.zero_apply]; constructor <;> linarith only
 rw [show (q) j=2*w+s from if_pos rfl]
 have hs:(2:ℝ) ≤ s:= by exact_mod_cast h
 constructor <;> linarith only [hs]

#print axioms slap_plate

variable (b:ℝ≥0)
    (y:P.ManyF j (P.advocate 3 a j))

lemma flip_calendar :
 P.calendar a j x (s+b) y=
  (inner ℂ (E s y) ((S).U x (E b y))).re:=by
 unfold calendar
 rw [← ContinuousLinearMap.adjoint_inner_right, (S).sym,← ContinuousLinearMap.comp_apply (g:=E _), (S).independent, ContinuousLinearMap.comp_apply,
    ←ContinuousLinearMap.comp_apply (g:=E _), ← (S).time]




local notation "C" u:max v:max=> P.calendar a j u v y

lemma slide_spawn :
 (dist ((S).U x (E s y)) (E s y))^2 - (dist (E s y) (E b y))^2=
 C 0 (s+s)- 2*C x (s+s) - C 0 (b+b) + 2*C 0 (s+b):=by
 have e (s:ℝ≥0) : C 0 (s+s)=‖E s y‖^2:=by rw [P.flip_calendar,(S).uZero]; exact inner_self_eq_norm_sq (𝕜:=ℂ) _
 rw [e s,e b, P.flip_calendar, P.flip_calendar, (S).uZero,ContinuousLinearMap.id_apply]
 rw [dist_comm,dist_eq_norm,dist_eq_norm,norm_sub_sq (𝕜:=ℂ), (S).unitary,
     norm_sub_sq (𝕜:=ℂ),RCLike.re_eq_complex_re]
 ring
#print axioms slide_spawn
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

