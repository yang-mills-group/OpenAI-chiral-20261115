import YM.LocalFieldBounds.Easel.Hedge

/-!
# One family, two bills

Transfer the positive Wick diagnostic to the W reading queried directly IN
Minkowski spacetime. Preserve even the CP-I/J certification via those same
normalized real smears (on their ACTUAL pose budgets). Do not dispense
a two-height or common-resolution substitute for the activated probe labels.
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

/-- Drop currency coordinate before the real crossing. -/
abbrev mist (p : Vantage) : Vantage :=
  p - elapsed (p 3)

lemma face_mist (p : Vantage) : Easel.face (mist p) = polarBase p := by
  change Easel.face (mist p) = position (spatial (Easel.face p)) 0
  apply Mink.ext_by
  · rw [spatial_position]; ext i
    change p _ - (p 3)*(basis timeAxis).ofLp (Fin.castSucc i) = p _
    rw [basis, PiLp.single_apply, if_neg (Fin.castSucc_ne_last i), mul_zero, sub_zero]
  rw [time_position]
  change p 3 - (p 3)*(basis timeAxis).ofLp timeAxis = 0
  rw [basis, PiLp.single_apply, if_pos rfl, mul_one, sub_self]

lemma mist_neg (p : Vantage) : mist (-p) = -mist p := by
  rw [mist, mist, Pi.neg_apply, elapsed, elapsed, neg_smul]
  abel

private lemma parade (p : Vantage) (a : (HH x₁).Op) :
    P.locate 3 S▪ p a = optx (P.seasons 3 S▪) a (Easel.face (mist p)) := by
  have h (p : Vantage) : P.cartage 3 S▪ p = M (P.seasons 3 S▪) (Easel.face (mist p)) := by
    rw [face_mist]; exact (P.cart_plank x₁ p).symm
  unfold locate optx
  rw [h,h,mist_neg]
  rfl

local notation "cutT" i:max => (mist (ξ₀ i))
local notation "timeT" i:max => (ξ₀ i 3)
local notation "crossT" => amber HCv (cutT false) (cutT true)
  T.toNNReal (timeT true - timeT false - 2*T) ΓJ ΓK
set_option maxHeartbeats 800000 in
lemma passageway (pt : 0 < T) :
    crossT = Harbor P 3 S▪ (Buoy x₁) (PointB x₁) ξ₀ T := by
  let u := T.toNNReal
  have ht := Real.toNNReal_pos.mpr pt
  have hu : (u:ℝ)=T := Real.coe_toNNReal _ pt.le
  have h : (HCv).bar u ΓJ = (Buoy x₁) T T := by
    rw [map_smul, shineJ P rayPost rayP M z mu pHw W e K x₁ u ht, hu]
    rfl
  have p : (HCv).bar u ΓK = (PointB x₁) T T := by
    rw [shineK P rayPost rayP M pHw W e K x₁ u ht, hu]
  unfold Harbor Easel.amber beacon scepter
  rw [parade P x₁, parade P x₁, h, p]
  rfl

variable (story : Remembers (galaxy P rayPost rayP M pHw W e K x₁) (asJ (chirality 3)))
include pW
lemma paid_amber :
    crossT ≠ 0 := by
  have h := pW.mansion.qprice (ξ₀ false) (mem_closedBall_self pW.hr.le)
    (ξ₀ true) (mem_closedBall_self pW.hr.le)
  rw [frontSk, ← passageway P M z mu pHw W e K x₁ T κ pW.tempo] at h
  intro e
  rw [e] at h
  exact (lt_asymm pW.meter h)

include τ story in
lemma fee_direct :
    ∃ L M : Curtain, Rampart.Supported L M ξ₀ (wτ/2) ∧ inkTest Y ΓJ ΓK L M ≠ 0 := by
  have he := paid_amber P M z mu pHw W e K x₁ T κ F G wτ pW
  obtain ⟨f,g,h,p,u⟩ := Easel.tone HCv (asJ (chirality 3)) story τ _ _ _ (Real.toNNReal_pos.mpr pW.tempo) _ _ _ he
    (timeT false) (timeT true) (wτ/2) (half_pos pW.hr)
  simp only [mist, sub_add_cancel] at h p
  exact ⟨f,g,⟨h,p⟩,u⟩

section
omit [Nonempty η]
lemma out_of_reach (x y : E4)
    (hx : x ∈ tsupport (Easel.film F)) (hy : y ∈ tsupport (Easel.film G)) :
    2*T < time y - time x ∧
    |time y - time x| + T < y.ofLp 0 - x.ofLp 0 ∧
    x-y ∈ Mink.spacelike := by
  rw [Easel.aperture] at hx hy
  obtain ⟨u,p,rfl⟩ := hx
  obtain ⟨v,t,rfl⟩ := hy
  have h := pW.distinct _
    (closedBall_subset_closedBall (half_le_self pW.hr.le) (pW.footprints.basis₀ p)) _
    (closedBall_subset_closedBall (half_le_self pW.hr.le) (pW.footprints.basis₁ t))
  exact ⟨h.1,h.2.1,(Poin.Canopy.phoney _ _).mp h.2.2⟩

theorem parts :
    Fields.causal (Easel.film F) (Easel.film G) :=
  fun _ x _ y => (out_of_reach P M z mu pHw W e K x₁ T κ F G wτ pW _ _ x y).2.2

end

/-- Full Wallpaper purchase also on any other actual films in that shell. -/
lemma change_film (u : P.Register) (L N : Curtain)
    (h : Rampart.Supported L N ξ₀ (wτ/2)) :
    Wallpaper P M z pHw W e K mu κ wτ ξ₀ x₁ T L N B := by
  have j := Freeport.marching P M z mu W.tally pHw W e K x₁ T L N κ wτ ξ₀ h
    pW.mansion.deck pW.hr u pW.tempo
  have d := margin_phys P 3 S▪ T ξ₀ L N wτ B pW.hr pW.mansion h
  refine ⟨pW.tempo,pW.meter,pW.hr,pW.key,pW.rank_spatial,pW.mansion,pW.distinct,h,j,d,?_⟩
  filter_upwards [camper P M z mu W.tally pHw e K L N κ ξ₀ wτ pW.hr h,
    (Complex.continuous_re.continuousAt.tendsto (x:=posedWindow _ _ _ _ _ _ _ _)
      |>.comp (j.pairZ.sub (j.soloμ.mul j.soloη))).eventually
        (lt_mem_nhds ((half_lt_self pW.meter).trans_le d))] with v p q
  exact ⟨p.1,p.2,q⟩

omit pW
/-- Paired positivity from Wick pricing and strict nonfactorization in
the Minkowski reading are for these *same* gauge and matter probes. Use the
normalized compact spacetime smears on their separate physical apertures.
Do not assert a direct value equal to the Wick difference. -/
structure Duet (Y : WView Dialect) (X : InkWaves Dialect)
    (r : ℝ) (pΩ : skit) (F G : Curtain) (b : ℝ) : Prop where
  ticket : InkPort HCv X Y
  tale : Remembers HCv (asJ (chirality 3))
  wrap : Wallpaper P M z pHw W e K mu κ r pΩ x₁ T F G b
  wick : b ≤ (vesper X ΓJ ΓK F G - sighting X ΓJ F * sighting X ΓK G).re
  direct : inkTest Y ΓJ ΓK F G ≠ 0
  spacelike : Fields.causal (Easel.film F) (Easel.film G)

include pW τ story
theorem double_billing (u : P.Register) :
    ∃ C D : Curtain, Duet P M z mu pHw W e K x₁ T κ Y X wτ ξ₀ C D B := by
  obtain ⟨g,f,h,t⟩ := fee_direct P M z mu pHw W e K x₁ T κ F G τ wτ pW story
  let a := change_film P M z mu pHw W e K x₁ T κ F G wτ pW u g f h
  exact ⟨g,f,τ,story,a,(ticket_lights P M z mu pHw W e K x₁ T κ g f τ wτ a).2,t,
    parts P M z mu pHw W e K x₁ T κ g f wτ a⟩
#print axioms double_billing

end YM.LocalFieldBounds.Motif
