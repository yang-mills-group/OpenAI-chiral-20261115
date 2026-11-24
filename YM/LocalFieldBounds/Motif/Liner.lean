import YM.LocalFieldBounds.Easel.Chime
import YM.LocalFieldBounds.Motif.Waltz

/-!
# Ingredient bills in the same vacuum
An actual call x at height v: pose orderPost, money and readings.
Do not evolve a pure issue and query the comparator after promotion.
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


/- Pose printer at Vantage α. β on second input may be displaced during
the measurement; each term still on one height. -/
abbrev Port (L : ℕ) (α : Vantage) :=
  (κ:ℂ) • cornea P M pHw e K L mu z (orderPost P L α)
abbrev Bay (L : ℕ) (α : Vantage) :=
  brass P W.tally L (orderPost P L α)

local notation "port" => Port P M z mu pHw e K κ
local notation "bay" => Bay P M W
local notation "charZ" => (fun l => P.singleState 3 l x₁)

abbrev tos (L : ℕ) (α : Vantage) :=
  charZ L (port L α)
abbrev tax (L : ℕ) (β : Vantage) :=
  charZ L (bay L β)
abbrev jointSale (L : ℕ) (α β : Vantage) :=
  charZ L ((port L α)*(bay L β))
local notation "leftY" => Y.expect [(ΓJ,Easel.film F)]
local notation "rightY" => Y.expect [(ΓK,Easel.film G)]

variable (w : ℝ≥0) (hw : 0<w)
include hw in
private lemma spark (p : Vantage) :
    (beacon HCv ΓJ (horizon p) w = scepter P 3 S▪ p w w (Buoy x₁)) ∧
    (beacon HCv ΓK (horizon p) w = scepter P 3 S▪ p w w (PointB x₁)) := by
  have h := shineJ P rayPost rayP M z mu pHw W e K x₁ w hw
  have d := shineK P rayPost rayP M pHw W e K x₁ w hw
  have f (p : Vantage) : CF.Buffered.Afterglow.Hierarchy.Seld.M (P.seasons 3 S▪) (Easel.face (mist p)) = P.cartage 3 S▪ p := by
    rw [face_mist]; exact (P.cart_plank x₁ p)
  have g : CF.Buffered.Afterglow.Hierarchy.Seld.M (P.seasons 3 S▪) (-Easel.face (mist p)) = P.cartage 3 S▪ (-p) := by
    rw [← f, mist_neg]; rfl
  change beacon HCv _ (mist p) _ = _ ∧ beacon HCv _ (mist p) _ = _
  unfold beacon optx scepter locate
  erw [f p, g, map_smul, h, d]
  exact ⟨rfl, rfl⟩


local notation "leftA" => tos P M z mu pHw e K x₁ κ
local notation "rightA" => tax P M W x₁
local notation "bothA" => jointSale P M z mu pHw W e K x₁ κ
local notation "spearA" => Easel.spear HCv w ΓJ ΓK
variable (p : skit) (h : Polaris.straight 3 w p) (t : broadV w p)

include hw
private lemma age :
    spearA (p false) (p true)
     = (κ:ℂ) * face_pair P M z 3 mu W.tally pHw e K x₁ p w := by
  unfold Easel.spear
  rw [(spark P M z mu pHw W e K x₁ κ w hw _).1, (spark P M z mu pHw W e K x₁ κ w hw _).2]
  change Cruise P 3 S▪ (Buoy x₁) _ _ _ = _
  have g := Polaris.unitH P p (w:ℝ) 3 S▪ (PointA x₁) (PointB x₁) (κ:ℂ) 1
  rw [one_smul, mul_one] at g
  exact g

include τ h t
lemma heard (R : P.Register) :
    Tendsto (fun n => bothA n (p false) (p true)) atTop
      (𝓝 (spearA (p false) (p true))) ∧
    Tendsto (fun n => leftA n (p false)) atTop (𝓝 leftY) ∧
    Tendsto (fun n => rightA n (p true)) atTop (𝓝 rightY) := by
  obtain ⟨u,d,v⟩ := session_pair P M z 3 mu W.tally pHw W e K x₁ w hw p h t R
    (fun v=>kiosk P v (p false) (p true))
    (show Tendsto (fun v=> landingY P v (kiosk P v (p false) (p true))) atTop (𝓝 p) from (frontSk p) ▸ revolving P (p false) (p true))
  rw [age P M z mu pHw W e K x₁ κ w hw,
    Easel.sight _ w τ _ hw _ (Easel.horizon (p false)),
    Easel.sight _ w τ ΓK hw _ (Easel.horizon (p true)),
    (spark P M z mu pHw W e K x₁ κ w hw _).1, (spark P M z mu pHw W e K x₁ κ w hw _).2]
  change _ ∧ Tendsto _ _ (𝓝 (SingleF P 3 S▪ (Buoy x₁) (p false) w)) ∧ _
  rw [unitSolo]
  refine ⟨(u.const_mul (κ:ℂ)).congr (fun i=>?_), (d.const_mul (κ:ℂ)).congr (fun i=>?_),v⟩
  · unfold jointSale Port
    rw [smul_mul_assoc,map_smul]
    rfl
  · unfold tos Port
    rw [map_smul]
    rfl

omit τ h t hw
section
omit [Nonempty η]

lemma meniscus_left (p x : Vantage) (n : ℕ) :
    leftA n p = leftA n x := by
  unfold tos Port cornea RunH
  rw [map_smul, map_smul, P.chart_price, P.chart_price]
lemma meniscus_right (p x : Vantage) (n : ℕ) :
    rightA n p = rightA n x := by
  unfold tax Bay brass
  by_cases h : f0 ≤ n
  · rw [dif_pos h, dif_pos h]
    unfold RunK
    rw [map_smul,map_smul,P.chart_price,P.chart_price]
  rw [dif_neg h, dif_neg h]

abbrev rounding (L : ℕ) : ℝ :=
  moonClock P L + 2*P.macroStep L
include W
lemma vanishes :
    Tendsto (rounding P) atTop (𝓝 0) := by
  simpa using (small_clock P W.tally).add (P.macroStep_zero.const_mul 2)

omit W

open RibbonDoc
private lemma aimed (L : ℕ) (x : Vantage)
    (S : Set Vantage) (h : closedBall x (rounding P L) ⊆ S)
    (N : P.Apron)
    (u : ∀ (i : Axis), N.realWidth P i + |Fame.Regulator.home P rayPost L i| ≤ moonClock P L) :
    P.Aperture N (P.meshPose L (orderPost P L x)) ⊆ S :=
  (paysAt P N 0 u _).trans (fun y hx =>
    h ((dist_triangle y _ x).trans (add_le_add hx (seeks P L x))))

include W
lemma well_left (L : ℕ) (ht : f0 ≤ L) (x : Vantage) (S : Set Vantage)
    (h : closedBall x (rounding P L) ⊆ S) :
    Rich P L S (port L x) false := by
  let y := trueKey P pHw e K L z
  let N := JpriceApp P rayPost M rayP y mu L
  have v := RibbonDoc.inside P (orderPost P L x) N S (by rfl : N.s=L)
    (aimed P L x S h N (fun i => ?_))

  exact rich_scale P _ _ (b:=false)
    ⟨v.1,v.2,spinBill P (v:=L) (orderPost P L x) M y mu⟩ _
  unfold N
  rw [Hmu_width]
  exact (add_le_add_right (home_room P rayP L _) _).trans (MezzoBill.windMoney P W.tally ht)

lemma well_right (L : ℕ) (ht : f0 ≤ L) (x : Vantage) (S : Set Vantage)
    (h : closedBall x (rounding P L) ⊆ S) :
    Rich P L S (bay L x) true := by
  let N := soloV P L (W.tally.date.stock L ht).2 rayPost rayP pseV
  have v := RibbonDoc.inside P (orderPost P L x) N S (by rfl : N.s=L)
    (aimed P L x S h N (fun i=>?_))
  rw [Bay,brass,dif_pos ht]
  exact rich_scale P _ _ (b:=true)
    ⟨v.1,v.2,RibbonDoc.lensColor P _ _⟩ _
  unfold N
  rw [solo_width]
  exact (add_le_add_right (home_room P rayP L _) _).trans (windowLaw P W.tally ht)


omit W

local notation "J♥" => Jmoney P M z mu pHw e K F κ
local notation "K♥" => Kmoney P W.tally G

lemma fog_left (L : ℕ) (p : Vantage) :
    P.singleState 3 L x₁ (J♥ L) = leftA L p := by
  rw [(sum_income P x₁ F _).2]
  change (∫ y, leftA L y ∂ F.ppm) = _
  simp_rw [show (fun u => leftA L u) = (fun _ : Paper=> leftA L p) from
    funext (fun u => meniscus_left P M z mu pHw e K x₁ κ u p L)]
  simp

include W
lemma fog_right (L : ℕ) (p : Vantage) :
    P.singleState 3 L x₁ (K♥ L) = rightA L p := by
  rw [(sum_income P x₁ G _).2]
  change (∫ y, rightA L y ∂ G.ppm) = _
  simp_rw [show (fun u => rightA L u) = (fun _ : Paper=> rightA L p) from
    funext (fun u => meniscus_right P M W x₁ u p L)]
  simp

end
include τ pW

lemma no_clock :
    leftY = sighting X ΓJ F ∧ rightY = sighting X ΓK G := by
  have h : 0 < T.toNNReal := Real.toNNReal_pos.2 pW.tempo
  have g : (T.toNNReal:ℝ)=T := Real.coe_toNNReal _ pW.tempo.le
  obtain ⟨t,u,v,d⟩ := lightingW P M z mu pHw W e K x₁ T κ F G τ wτ pW
  rw [Easel.sight _ _ τ _ h _ (Easel.horizon 0),
    Easel.sight _ _ τ ΓK h _ (Easel.horizon 0),
    (spark P M z mu pHw W e K x₁ κ _ h 0).1,
    (spark P M z mu pHw W e K x₁ κ _ h 0).2, g,
    ←u, ←v, posed_One, posed_One]
  exact ⟨rfl,rfl⟩

lemma initial : Tendsto (fun L => P.singleState 3 L x₁ (Jmoney P M z mu pHw e K F κ L))
    atTop (𝓝 leftY) ∧ Tendsto (fun L => P.singleState 3 L x₁ (Kmoney P W.tally G L))
    atTop (𝓝 rightY) := by
  obtain ⟨s,t⟩ := no_clock P M z mu pHw W e K x₁ T κ F G τ wτ pW
  obtain ⟨_,v,u,_⟩ := lightingW P M z mu pHw W e K x₁ T κ F G τ wτ pW
  rw [s,t,←v,←u]
  exact ⟨pW.budget.soloμ,pW.budget.soloη⟩

end YM.LocalFieldBounds.Motif
