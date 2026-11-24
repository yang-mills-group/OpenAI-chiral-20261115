import YM.LocalFieldBounds.Motif.Orient

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


open CF.Py.Rate.LocalLimit Preparation
open CF.Buffered.Afterglow.Tower
open Preparation.Tabletop CasaF.Signboard
open CF.Py.Rate.LocalLimit.Preparation.Yoke
open CF.Ione.Clock CF.Moto CF.LitCurrent AuroraX Verdance Lattice

open CF.QuadClock.SignSlot

variable (Lh:64 ≤ P.par.R.L.val){R:P.Register}{d₀ C' t' Wp β}
  (council: CouncilGrant P R d₀ C' t' Z Wp β)(bKern: PublicKernel P Z Wp)
variable (res: Resonant P η A H f0 P.jump128)
variable (V:Soul →ₗ[ℝ]ℝ)(hew: DerLedger P η M W pHw e K V)

variable (w : ℕ)
local notation "ϕ" => asJ (chirality 3)

/-- Direct purchase on same vacuum W now, under a named
activation w. Rosette every ε, every smaller positive aperture. No Wick
price taken as that direct act. -/
structure Glance : Prop where
  moors : P.lodestar 3 x₁
  song : Duet P M z mu pHw W e K x₁ T κ Y X wτ ξ₀ F G B
  credit : Signal (Y:=Y) P M z mu pHw W e K x₁ κ F G
  tag : Stamp P M z mu pHw W e K κ true 0 w
  charged : V z ≠ 0
  zeroK : rightY = 0
  world : ∀ ε a, 0<ε → Fare wτ a →
     ∃ (h : ℝ≥0) (n : ℕ) (I : Coat F n) (J : Coat G n) (D : Song h I J),
       ∀ᶠ L in atTop, Rosette P M z mu pHw W e K x₁ T κ F G (X:=X) (Y:=Y) (B:=B) (ξ₀:=ξ₀) wτ a ε L D

local notation "GIFT" => Glance P M z mu pHw W e K x₁ T κ F G (X:=X) (Y:=Y) (B:=B) (ξ₀:=ξ₀) wτ V w
variable (gift : Glance P M z mu pHw W e K x₁ T κ F G (X:=X) (Y:=Y) (B:=B) (ξ₀:=ξ₀) wτ V w)
include Lh council bKern hew res
lemma gift_of
    (p : Duet P M z mu pHw W e K x₁ T κ Y X wτ ξ₀ F G B)
    (h : P.lodestar 3 x₁) (a : Stamp P M z mu pHw W e K κ true 0 w)
    (n : V z ≠ 0) : GIFT :=
  ⟨h,p,signal P M z mu pHw W e K x₁ T κ F G wτ p h,a,n,
     no_tide P M z pHw W e K x₁ G p.ticket Lh council bKern res V hew n,
     fun _ _ u v=>earClosing P M z mu pHw W e K x₁ T κ F G wτ R p v u⟩

omit Lh council bKern hew res
local notation "aOp" => (HCv).operator ΓJ (Easel.film F)
local notation "bOp" => (HCv).operator ΓK (Easel.film G)
include gift
/-- Direct price. Two compact spacetime smears in W-set. In earlier Hilbert
system, not a Wick reading. Nonempty spacetime supports, worlds. -/
lemma price_not_product :
    inner ℂ vuc (aOp (bOp vuc)) ≠ (inner ℂ vuc (aOp vuc)) * inner ℂ vuc (bOp vuc) := by
  let t := gift.song.ticket
  have n := gift.song.direct
  rw [Easel.inkTest] at n
  simp only [t.real_value] at n
  exact sub_ne_zero.mp n

lemma wick_not_product :
    vesper X ΓJ ΓK F G ≠ sighting X ΓJ F * sighting X ΓK G := by
  intro h
  have p := gift.song.wrap.meter.trans_le gift.song.wick
  rw [h, sub_self, Complex.zero_re] at p
  exact lt_irrefl _ p

/-- Any demand on absolute tolerance (including regulator) and raw
enclosure, at ANY sufficiently large common height in this prescription -/
lemma halls (ε:ℝ) (t:0<ε) :
   ∃ (a:ℝ), Fare wτ a ∧ a<ε ∧
    ∃ (h:ℝ≥0) (n:ℕ) (I:Coat F n) (J:Coat G n) (D:Song h I J),
       ∀ᶠ L in atTop, Rosette P M z mu pHw W e K x₁ T κ F G (X:=X) (Y:=Y) (B:=B) (ξ₀:=ξ₀) wτ a ε L D := by
  let a := min (wτ/2) (ε/2)
  have p : Fare wτ a := ⟨lt_min (half_pos gift.song.wrap.hr) (half_pos t),min_le_left ..⟩
  exact ⟨a,p,(min_le_right ..).trans_lt (half_lt_self t),gift.world _ _ t p⟩

#print axioms gift_of
#print axioms price_not_product
#print axioms wick_not_product
#print axioms halls
end YM.LocalFieldBounds.Motif
