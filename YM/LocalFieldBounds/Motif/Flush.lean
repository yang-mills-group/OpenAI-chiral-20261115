import YM.LocalFieldBounds.Motif.Scale

/-!
# Ingredient
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


abbrev band (L : ℕ) := 2*lyre L

lemma post_empty (L : ℕ) : orderPost P L 0=0 := by
  funext i
  simp [orderPost, Curtain.shifter, MacroSix.Grid.tag]

variable (L : ℕ) (l : f0 ≤ L)
local notation "court" => choices P M z mu W.tally pHw e K l
local notation "Σₓ" => (↑(psScale P W.tally L):ℂ)
local notation "piₓ" => (κ:ℂ)
local notation "homeₓ" => Fame.Regulator.home P rayPost L
local notation "eng" c:max => annoFace P 3 S▪ L homeₓ (court c) (band P L) (band P L)

/-- Both charged operands at their respective origin: the *same* armor as
in all the centered and moved Eu approximations. -/
structure Origin (ε : ℝ) : Prop where
  minted : port L 0 = piₓ • (court false).F ∧ bay L 0 = Σₓ • (court true).F
  branch : (court false).s=L ∧ (court true).s=L
  arms : atom L = piₓ • eng false ∧ issu L = Σₓ • eng true
  edge : Unchained P court homeₓ (lyre L)
  rich : Rich P L (closedBall 0 ε) (port L 0) false ∧ Rich P L (closedBall 0 ε) (bay L 0) true

lemma originates (a : ℝ) (h : rounding P L ≤ a) :
    Origin P M z mu pHw W e K x₁ κ L l a := by
  refine ⟨⟨?_,?_⟩,⟨rfl,rfl⟩,⟨rfl,?_⟩,
    given P M z mu W.tally l pHw e K _ le_rfl,
    well_left P M z mu pHw W e K κ L l 0 _ (closedBall_subset_closedBall h),
    well_right P M W L l 0 _ (closedBall_subset_closedBall h)⟩
  · rw [Port,post_empty,cornea,RunH,chart_null]; rfl
  · rw [Bay,post_empty,brass,dif_pos l,RunK,chart_null]; rfl
  rw [InkD, montage, heyC,dif_pos l]; rfl

omit [Nonempty η] in
lemma cargoJ (r : Vantage) : port L r = P.chartAll (orderPost P L r) (port L 0) := by
  unfold Port cornea RunH
  rw [post_empty, chart_null,map_smul]

omit [Nonempty η] in
lemma cargoK (r : Vantage) : bay L r = P.chartAll (orderPost P L r) (bay L 0) := by
  unfold Bay brass
  rw [post_empty]
  by_cases h : f0 ≤ L
  · rw [dif_pos h,dif_pos h]
    unfold RunK
    rw [chart_null,map_smul]
  rw [dif_neg h,dif_neg h,map_zero]

local notation "Eagle" => CF.Buffered.Afterglow.Hierarchy.Seld.M
section
variable (u : (P.ManyF 3 (P.advocate 3 x₁ 3)).Op)
include W e K pHw
private lemma carry (p : Paper) :
    dish (optx HS u (Easel.face p)) = dish u := by
  have h : Eagle HS (-Easel.face p) ΩJ☆=ΩJ☆ :=
    (HCv).stay _
  change ab (Eagle HS (Easel.face p) (u (Eagle HS (-Easel.face p) ΩJ☆))) = _
  rw [tboth,h]

private lemma single_move (p : Paper) :
    dish (P.locate 3 S▪ p u) = dish u := by
  have v (p : Paper) : Eagle HS (Easel.face (mist p)) = P.cartage 3 S▪ p := by
    rw [face_mist]
    exact P.cart_plank x₁ p
  have g : Eagle HS (-Easel.face (mist p)) = P.cartage 3 S▪ (-p) := by
    rw [←v,mist_neg]; rfl
  convert carry P M pHw W e K x₁ u (mist p) using 2
  unfold optx locate
  rw [v,g]

lemma single_valise :
    dish (valise HS u (Easel.film F)) = dish u := by
  have h : Continuous (fun p : Paper => ‖optx HS u (Easel.face p) ΩJ☆‖) :=
    ((village HS ΩJ☆ u).comp cont_face).norm
  obtain ⟨i,t⟩ := (F.ownsK.image h).bddAbove
  have H : Integrable (fun p:Paper=>optx HS u (Easel.face p) ΩJ☆) F.ppm :=
    Integrable.of_bound ((village HS ΩJ☆ u).comp cont_face).aestronglyMeasurable i ?_
  · unfold soup
    rw [use_valise, ←integral_inner H]
    change (∫ p, dish (optx HS u (Easel.face p)) ∂F.ppm) = dish u
    simp_rw [carry P M pHw W e K x₁ u]
    simp
  filter_upwards [F.inhabits] with p v
  exact t (mem_image_of_mem _ v)
end


open OS.Semigroup.Marble
local notation "splitS" p:max q:max => frontage (landing P L p) (landing P L q)
local notation "altar" u:max => P.locate 3 S▪ (landing P L u)
local notation "leftMe" => κ -- 
local notation "cap" => band P L
abbrev trench (s : skit) : ℝ := s true 3 - s false 3 - 2*cap
abbrev node (p q : Vantage) :=
  hotPair HS ΩJ☆ (trench P L (splitS p q)) ((altar p) (atom L)) ((altar q) (issu L))

structure Act (p q : Vantage) : Prop where
  cited : bothA L p q = node P M z mu pHw W e K x₁ κ L p q
  own : leftA L p = dish (plate L) ∧ rightA L q = dish (cup L)

/- Exact origins: Even dual intersection Pose fees. -/
variable (U : P.Register) {p q : Vantage}
include U l

lemma charged (v : cap ≤ T) (h : Chili.Coast T (splitS p q)) :
    Act P M z mu pHw W e K x₁ κ F G L p q := by
  let y := kiosk P L p q
  have a := Freeport.earned P M z 3 mu W.tally l pHw e K x₁ (P.ellisP 3 x₁ U).some y cap
      (lt_of_le_of_lt (mul_le_mul_of_nonneg_left v zero_le_two) h.quest.1)
      (fun i => lt_of_le_of_lt (mul_le_mul_of_nonneg_left v zero_le_two) (h.quest.2 i)) (by
        unfold band; linarith only [clockP P L])
  constructor
  · unfold jointSale Port
    rw [smul_mul_assoc,map_smul]
    change piₓ • charZ L (cornea P M pHw e K L mu z (y false)*(brass P W.tally L (y true))) =
      Polaris.Cruise P 3 S▪ (piₓ • Fresh L) (B0 L) (landingY P L y) cap
    rw [a.pairs]
    simpa only [mul_one,one_smul,smul_eq_mul] using
      (Polaris.unitH P (landingY P L y) cap 3 S▪ (Fresh L) (B0 L) piₓ 1).symm
  constructor
  · rw [Rial, single_valise P M pHw W e K]
    unfold tos Port
    rw [map_smul]
    have ux := unitSolo P cap 3 S▪ (Fresh L) piₓ ((landingY P L y) false)
    rw [←a.sectorJ] at ux
    refine Eq.trans ux.symm (?_)
    exact single_move P M pHw W e K x₁ (atom L) _
  rw [Pound, single_valise P M pHw W e K]
  exact a.sectorP.trans (single_move P M pHw W e K x₁ (issu L) _)

#print axioms charged
end YM.LocalFieldBounds.Motif
