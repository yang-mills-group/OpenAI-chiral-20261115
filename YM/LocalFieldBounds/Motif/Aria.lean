import YM.LocalFieldBounds.Motif.Tabard

/-!
# Until the hearing

The two singular prices are evaluated by symmetric field operators.
The direct purchase uses even non-static charges (joint time and space).
No using 4-rotation in the proof.
-/


set_option synthInstance.maxSize 28000
set_option maxHeartbeats 430000
set_option maxRecDepth 8000
set_option quotPrecheck false
noncomputable section
namespace YM.LocalFieldBounds.Motif

open Filter Function Set Metric MeasureTheory 
open scoped Topology ComplexOrder InnerProductSpace NNReal Classical
open CF.Buffered.Afterglow.Tower.VacuumSelection Spine
open CF.QuadClock.ShapeLab SoulField SatinWard.Installment
open Spine.Fame.Regulator Internal Dovetail Freeport Polaris
open Polaris.Rampart _root_.GarnetAct.Cut

variable (P:Spine) (M:P.par.R.L.val%16=1) (z:Soul) (mu:Axis)
variable {f0:ℕ}{Z:ℕ→ℕ}{H A d c dσ:ℝ}{η:Type}[Fintype η]
variable (pHw:Tendsto Z atTop atTop)(W:HeartClock P f0 H A d c dσ P.jump128 M Z η)(e:Melodic P η A f0 Z)(K:P.NightCop)[Nonempty η]
variable (x₁:P.Spectrum0 3) (T κ:ℝ) (F G:Curtain)
open Set MeasureTheory
open _root_.YM.SatinWFixed Andesite Carton _root_.YM.Boundary Probe
variable {X: InkWaves Dialect}{Y:WView Dialect}(τ:InkPort (galaxy P rayPost rayP M pHw W e K x₁) X Y) {B:ℝ}{ξ₀:skit}(wτ:ℝ) (pW:Wallpaper P M z pHw W e K mu κ wτ ξ₀ x₁ T F G B)
local notation "Other" x:max=> P.advocate 3 x 3
local notation "HH" x:max=> P.ManyF 3 (P.advocate 3 x 3)
local notation "PointA" x:max=> priceX P pHw e mu rayPost M K rayP 3 (Other x) z
local notation "PointB" x:max=> pricedPSE P M 3 (Other x) rayP W.tally
local notation "Buoy" x:max=> ((κ:ℂ) • PointA x)
local notation "S▪"=> P.advocate 3 x₁ 3
local notation "ΩJ☆"=> P.heaven 3 S▪ -- exists notation!
local notation "HCv" => galaxy P rayPost rayP M pHw W e K x₁
local notation "ΓJ"=> ( (κ:ℂ) • choral mu z)
local notation "ΓK"=> omegaCorner

open CF.Buffered.Afterglow.Hierarchy.Seld
open YM.LocalFieldBounds.Easel

local notation "port" => Port P M z mu pHw e K κ
local notation "bay" => Bay P M W
local notation "charZ" => (fun l => P.singleState 3 l x₁)
local notation "leftY" => Y.expect [(ΓJ,Easel.film F)]
local notation "rightY" => Y.expect [(ΓK,Easel.film G)]
local notation "jointY" => Y.expect [(ΓJ,Easel.film F),(ΓK,Easel.film G)]
local notation "J♥" => Jmoney P M z mu pHw e K F κ
local notation "K♥" => Kmoney P W.tally G
local notation "leftA" => tos P M z mu pHw e K x₁ κ
local notation "rightA" => tax P M W x₁
local notation "bothA" => jointSale P M z mu pHw W e K x₁ κ


open _root_.YM.SatinRegistration LimeWave Carton
local notation "HS" => P.seasons 3 S▪
local notation "NV" => bands HS
local notation "RD" => radial HS
local notation "Q" => pricedPSE P M 3 S▪ rayP W.tally
local notation "A0" => priceX P pHw e mu rayPost M K rayP 3 S▪ z
local notation "B0" => heyC P rayPost rayP 3 S▪ W.tally
local notation "Fresh" => realFreshF P pHw e mu rayPost M K rayP 3 S▪ z
local notation "lyre" => moonClock P

local notation "atom" => InkA P M z mu pHw e K x₁ κ
local notation "issu" => InkD P M W x₁
local notation "sJ" => StageJ P M z mu pHw e K x₁ κ F
local notation "sK" => StageK P M W x₁ G
local notation "dish" => soup P x₁
local notation "plate" => Rial P M z mu pHw e K x₁ κ F
local notation "cup" => Pound P M W x₁ G
local notation "brim" => Flavor P M z mu pHw W e K x₁ κ F G
local notation "ab" => inner ℂ ΩJ☆
local notation "vuc" => (HCv).vacuum

local notation "θ" => asJ (chirality 3)
open OS.Semigroup

lemma reflection (p : mu ≠ 3) :
    θ ΓJ = ΓJ ∧ θ ΓK = ΓK := by
  have k (i : Molars) (h : chirality 3 i = 1) :
      θ (Andesite.herald i 1) = Andesite.herald i 1 := by
    funext y
    change (chirality 3 y:ℂ) * star (Andesite.herald i 1 y) = Andesite.herald i 1 y
    unfold Andesite.herald; simp only [Pi.single_apply]
    split
    · subst y; simp [h]
    simp
  refine ⟨?_,k none rfl⟩
  unfold choral trueCorner
  rw [map_smulₛₗ, map_sum]
  rw [starRingEnd_apply,Complex.star_def,Complex.conj_ofReal]
  refine congrArg ((κ:ℂ) • ·) (Finset.sum_congr rfl fun i _ => ?_)
  rw [map_smulₛₗ,starRingEnd_apply,Complex.star_def,Complex.conj_ofReal,
    k (some (mu,i)) ((colorPay_eq 3 mu).trans (if_neg (Ne.symm p)))]

local notation "aOp" => (HCv).operator ΓJ (Easel.film F)
local notation "bOp" => (HCv).operator ΓK (Easel.film G)
variable (v : Duet P M z mu pHw W e K x₁ T κ Y X wτ ξ₀ F G B)
include v
lemma symmetry :
    LinearMap.IsSymmetric aOp ∧ LinearMap.IsSymmetric bOp := by
  have t (a : Dialect) (g : θ a = a) (Z : Curtain) :
      LinearMap.IsSymmetric ((HCv).operator a (Easel.film Z)) := by
    have e' : opTag θ (a,Easel.film Z) = (a,Easel.film Z) :=
      Prod.ext g (Easel.film_real Z)
    intro x y
    have p := (HCv).sharp θ v.tale (a,Easel.film Z) x y
    rwa [e'] at p
  have h := reflection z mu κ v.wrap.rank_spatial
  exact ⟨t _ h.1 _,t _ h.2 _⟩


local notation "aVec" => Easel.myKet HCv ΓJ F
local notation "bVec" => Easel.myKet HCv ΓK G
abbrev Center (x : HH x₁) : HH x₁ :=
  x - inner ℂ ΩJ☆ x • ΩJ☆
local notation "cut" => Center P x₁
omit v
lemma listens (x : HH x₁) :
    inner ℂ ΩJ☆ (cut x) = 0 := by
  unfold Center
  rw [inner_sub_right,inner_smul_right, inner_self_eq_norm_sq_to_K,
    P.stone_norm]
  simp

lemma cut_cost (x y : HH x₁) :
    inner ℂ (cut x) (cut y) =
      inner ℂ x y - inner ℂ x ΩJ☆ * inner ℂ ΩJ☆ y := by
  change inner ℂ (x - _ • ΩJ☆) _ = _
  rw [inner_sub_left,inner_smul_left,listens,mul_zero,sub_zero,Center,inner_sub_right,
    inner_smul_right,mul_comm]

include v
lemma harmony :
    inner ℂ (cut aVec) (cut bVec) = inkTest Y ΓJ ΓK F G := by
  rw [Easel.ink_P HCv θ v.tale v.ticket, Easel.sauce,cut_cost,
    (reflection z mu κ v.wrap.rank_spatial).1]
  rfl

lemma solo_costs :
    star leftY = leftY ∧ star rightY = rightY := by
  have sym := symmetry P M z mu pHw W e K x₁ T κ F G wτ v
  rw [v.ticket.real_value,v.ticket.real_value]
  simp only [←starRingEnd_apply, inner_conj_symm]
  exact ⟨sym.1 vuc vuc, sym.2 vuc vuc⟩

open Passage
local notation "U" => CF.Buffered.Afterglow.Hierarchy.Seld.M HS
local notation "bat" => inkTest Y ΓJ ΓK F G

lemma charge_real 
    (both : aOp (bOp vuc) = bOp (aOp vuc)) :
    star bat = bat := by
  have h := symmetry P M z mu pHw W e K x₁ T κ F G wτ v
  have u := solo_costs P M z mu pHw W e K x₁ T κ F G wτ v
  unfold inkTest
  rw [star_sub,star_mul, u.1,u.2,mul_comm rightY,v.ticket.real_value,
    ←starRingEnd_apply,inner_conj_symm]
  suffices inner ℂ (aOp (bOp vuc)) vuc = inner ℂ vuc (aOp (bOp vuc)) from by rw [show
    inner ℂ ((HCv).row [(ΓJ,Easel.film F),(ΓK,Easel.film G)]).val (HCv).omega =
     inner ℂ (HCv).omega ((HCv).row [(ΓJ,Easel.film F),(ΓK,Easel.film G)]).val from this]
  rw [both,h.2,h.1,both]

omit v
variable (g : P.lodestar 3 x₁)
include g
lemma berth : Passage.Moors HCv := by
  intro y h
  refine (P.heavenRank _ _ (g 3) y).2 ⟨(heat_iff_edge _ _ _).1 h.fixed,?_⟩
  intro t
  have a := h.space t.val
  rw [show SEP timeAxis t.val=t from ?_, laneslot] at a
  · exact a
  apply Subtype.ext
  change t.val-t.val timeAxis • basis timeAxis=t.val
  rw [show t.val timeAxis=0 from t.property,zero_smul,sub_zero]

lemma mooring (x : HH x₁) (u : ∀ p, U p x = x) :
    x ∈ Submodule.span ℂ {ΩJ☆} :=
  (P.heavenRank _ _ (g 3) x).2
    ⟨fun t => Eq.trans (congrArg (fun a => a x) (timeslot HS t).symm) (u _),
      fun p => Eq.trans (congrArg (fun a => a x) (laneslot HS p).symm) (u _)⟩

variable {g}
omit g v
/-- No common fixed subspace of the real spacetime translations contributes
to this bill, still on the original priced Hilbert space. Charges to the
two *actual* pressure vectors, not to a projection for Wick continuation. -/
structure Signal : Prop where
  pin : Passage.Moors HCv
  feet : (∀ (x : HH x₁), (∀ p, U p x = x) →
      inner ℂ x (cut aVec) = 0 ∧ inner ℂ x (cut bVec) = 0)
  marg : star leftY = leftY ∧ star rightY = rightY
  grip : LinearMap.IsSymmetric aOp ∧ LinearMap.IsSymmetric bOp
  rate : inner ℂ (cut aVec) (cut bVec) = bat ∧ bat ≠ 0
variable (g)
include g v
lemma signal : Signal (Y:=Y) P M z mu pHw W e K x₁ κ F G := by
  refine ⟨berth P M pHw W e K x₁ g,fun x h => ?_,
    solo_costs P M z mu pHw W e K x₁ T κ F G wτ v,
    symmetry P M z mu pHw W e K x₁ T κ F G wτ v,
    harmony P M z mu pHw W e K x₁ T κ F G wτ v,v.direct⟩
  obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.1 (mooring P x₁ g x h)
  simp only [inner_smul_left,listens,mul_zero,true_and]

#print axioms charge_real
#print axioms signal
end YM.LocalFieldBounds.Motif
