import YM.LocalFieldBounds.Motif.Liner

/-!
# Horn

Spend both estimator and coupled fog wages in the same program and through their precise poses.
The room includes all those fees even with both component enlargements. No mean gaps.
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

/-- Seats within nominal support enlarged by a radius. -/
def Shade (a : ℝ) : Set Vantage := {p | ∃ u ∈ F.boxS, p ∈ closedBall u a}

abbrev landing (L : ℕ) (x : Vantage) := Rampart.station P L (orderPost P L x)

/-- Purchases in Shade (even point fees with small displacements). -/
structure Pack (L : ℕ) (a : ℝ) : Prop where
  wharf (p : Vantage) (h : p ∈ F.boxS) (u : Vantage) (d : u∈closedBall p (a/2)) :
    landing P L u ∈ closedBall p a ∧ ∀ S : Set Vantage, closedBall p a ⊆ S → Rich P L S (port L u) false
  till (p : Vantage) (h : p ∈ G.boxS) (u : Vantage) (d : u∈closedBall p (a/2)) :
    landing P L u ∈ closedBall p a ∧ ∀ S : Set Vantage, closedBall p a ⊆ S → Rich P L S (bay L u) true
  club (S : Set Vantage) : Shade F a ⊆ S → Rich P L S (J♥ L) false
  band (S : Set Vantage) : Shade G a ⊆ S → Rich P L S (K♥ L) true

omit [Nonempty η] in
lemma packing (a : ℝ) (h : 0<a) :
    ∀ᶠ L : ℕ in atTop, Pack P M z mu pHw W e K κ F G L a := by
  filter_upwards [(vanishes P M W).eventually (ge_mem_nhds (half_pos h)),
    eventually_ge_atTop f0, (P.macroStep_zero.const_mul 2).eventually (ge_mem_nhds (by simp [h] : 2*(0:ℝ)<a/2))]
      with L v ht j
  have hair (p u : Vantage) (hy : u ∈ closedBall p (a/2)) :
        landing P L u ∈ closedBall p a :=
    (dist_triangle _ _ _).trans ((add_le_add ((seeks P L u).trans j) hy).trans_eq (add_halves _))
  have aim (p u : Vantage) (hy : u ∈ closedBall p (a/2)) :
        closedBall u (rounding P L) ⊆ closedBall p a :=
    fun y d => (dist_triangle _ _ _).trans ((add_le_add (le_trans d v) hy).trans_eq (add_halves _))
  refine ⟨fun p _ u d =>
    ⟨hair p u d, fun S t => well_left P M z mu pHw W e K κ L ht u S ((aim p u d).trans t)⟩,
    fun p _ u d =>
    ⟨hair p u d, fun S t => well_right P M W L ht u S ((aim p u d).trans t)⟩,
    fun S t => rich_sell P S L _ _ false ?_,
    fun S t => rich_sell P S L _ _ true ?_⟩
  · intro x hx
    obtain ⟨p,aP,rfl⟩ := Curtain.picked .. |>.mp hx
    refine rich_scale P S L (well_left P M z mu pHw W e K κ L ht p S ?_) _
    refine closedBall_subset_closedBall (v.trans (half_le_self h.le)) |>.trans ?_
    exact fun _ q => t ⟨p,aP,q⟩
  intro x hx
  obtain ⟨p,aP,rfl⟩ := Curtain.picked .. |>.mp hx
  refine rich_scale P S L (well_right P M W L ht p S ?_) _
  refine closedBall_subset_closedBall (v.trans (half_le_self h.le)) |>.trans ?_
  exact fun _ q => t ⟨p,aP,q⟩

/-- Radius of localization allowed both for field anchors and for estimators. -/
abbrev Fare (b a : ℝ) := 0 < a ∧ a ≤ b/2

structure Placement (T : ℝ) (ξ : skit) (F G : Curtain) (b a : ℝ) : Prop where
  terrain : ∀ i∈Shade F a, ∀ j∈Shade G a, Chili.Coast T (frontage i j)
  radius : Fare b a
  left : Shade F a ⊆ closedBall (ξ false) b
  right : Shade G a ⊆ closedBall (ξ true) b

include pW
omit [Nonempty η] in
lemma placed {a : ℝ} (f : Fare wτ a) :
    Placement T ξ₀ F G wτ a := by
  have h (K : Curtain) (p : Vantage) (s : K.boxS ⊆ closedBall p (wτ/2)) :
      Shade K a ⊆ closedBall p wτ := by
    rintro x ⟨u,g,t⟩
    exact (dist_triangle x u p).trans ((add_le_add (le_trans t f.2) (s g)).trans_eq (add_halves _))
  let b := h F _ pW.footprints.basis₀
  let c := h G _ pW.footprints.basis₁
  exact ⟨fun i hi j hj => pW.mansion.deck i (b hi) j (c hj),f,b,c⟩
omit pW


variable {w : ℝ≥0} {n : ℕ} (A' : Coat F n) (C : Coat G n) (D : Song w A' C)
variable (a : ℝ)
abbrev Radius (a T : ℝ) (w : ℝ≥0) := 0 < w ∧ (w:ℝ) ≤ T ∧ (w:ℝ) ≤ a/2

omit [Nonempty η] in
lemma hired (g : Placement T ξ₀ F G wτ a) (r : Radius a T w) :
    Nonempty (Song w A' C) := by
  refine Song.afforded w _ _ r.1 (fun i hi j hj => ?_)
  exact le_trans (mul_le_mul_of_nonneg_left r.2.1 zero_le_two)
    (g.terrain i ⟨i,hi,mem_closedBall_self g.radius.1.le⟩ j ⟨j,hj,mem_closedBall_self g.radius.1.le⟩).quest.1.le

omit [Nonempty η] in
lemma displacements (r : Radius a T w) (i j) (k : (D.coin i j).Job) :
    dist ((D.coin i j).eighth k) (C.note j) ≤ a/2 :=
  le_trans ((D.coin i j).moves k) r.2.2

omit [Nonempty η] in
lemma given_fee (r : Radius a T w) (L : ℕ) (v : Pack P M z mu pHw W e K κ F G L a)
    (i j) (k : (D.coin i j).Job) :
    Rich P L (closedBall (A'.note i) a) (port L (A'.note i)) false ∧
    Rich P L (closedBall (C.note j) a) (bay L ((D.coin i j).eighth k)) true := by
  exact ⟨(v.wharf _ (A'.stays i) _ (mem_closedBall_self (le_trans w.2 r.2.2))).2 _ Set.Subset.rfl,
    (v.till _ (C.stays j) _ ((D.coin i j).moves k |>.trans r.2.2)).2 _ Set.Subset.rfl⟩

include τ
lemma clarion (g : Placement T ξ₀ F G wτ a) (r : Radius a T w) (U : P.Register) :
    Tendsto (fun L : ℕ => D.play (bothA L)) atTop (𝓝 (D.play (spear HCv w ΓJ ΓK))) := by
  refine Song.uplift D (fun i j k => ?_)
  have z0 := g.radius.1.le
  obtain ⟨h,d⟩ := (g.terrain _ ⟨A'.note i,A'.stays i,mem_closedBall_self z0⟩ _
    ⟨C.note j,C.stays j,le_trans ((D.coin i j).moves k) (le_trans r.2.2 (half_le_self z0))⟩).quest
  have v := mul_le_mul_of_nonneg_left r.2.1 zero_le_two
  exact (heard P M z mu pHw W e K x₁ κ F G τ w r.1
    (frontage (A'.note i) ((D.coin i j).eighth k))
    (lt_of_le_of_lt v h) (fun s => lt_of_le_of_lt v (d s)) U).1
omit τ

#print axioms packing
#print axioms clarion
end YM.LocalFieldBounds.Motif
