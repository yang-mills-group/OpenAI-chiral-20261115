import YM.LocalFieldBounds.Motif.Horn

/-!
# Primer

Settling a paid wage, at simultaneous mark price through
both joint polls, both own marginals, and the two independence debits.
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

variable (story : Remembers (galaxy P rayPost rayP M pHw W e K x₁) (asJ (chirality 3)))
local notation "gross" L:max => charZ L (J♥ L)
local notation "tarif" L:max => charZ L (K♥ L)
local notation "levy" L:max => charZ L ((J♥ L)*(K♥ L))
local notation "bat" => inkTest Y ΓJ ΓK F G
local notation "wik" => vesper X ΓJ ΓK F G


variable {a ε : ℝ} (L : ℕ)
variable {w : ℝ≥0} {n : ℕ} {A' : Coat F n} {C : Coat G n} (D : Song w A' C)
section primitive
omit [Nonempty η]
/-- Any independence candidate at these same costs, need only test on the
actual poses of this query. -/
lemma price_check (r : Paper → Paper → ℂ)
    (h : ∀ i j k, r (A'.note i) ((D.coin i j).eighth k) =
      leftA L (A'.note i) * rightA L ((D.coin i j).eighth k)) :
    D.play r = (gross L)*(tarif L) := by
  refine (D.agrees (b:= fun _ _ => (gross L)*(tarif L)) ?_).trans (D.constant _)
  intro i j k
  rw [h, ← fog_left (F:=F), ← fog_right (G:=G)]

lemma pay_solo :
    D.play (fun p _ => leftA L p) = gross L ∧ D.play (fun _ u => rightA L u) = tarif L := by
  exact ⟨(D.agrees (fun i j k =>
    (fog_left P M z mu pHw e K x₁ κ F L (A'.note i)).symm :
         ∀ i j k, leftA L (A'.note i) = gross L)).trans (D.constant _),
         (D.agrees (fun i j k => (fog_right P M W x₁ G L _).symm)).trans (D.constant _)⟩

lemma pay_cross :
    D.play (fun p q => bothA L p q - leftA L p * rightA L q) =
     D.play (bothA L) - gross L*tarif L := by
  rw [←Song.under, price_check P M z mu pHw W e K x₁ κ F G L D (fun p q=>leftA L p * rightA L q) (fun i j k=>rfl)]

end primitive


/-- Grade of a performance through its wage and its receipt -/
structure Score (wτ B a ε : ℝ) (ξ₀ : skit) (L : ℕ)
    (D : Song w A' C) : Prop where
  placed : Placement T ξ₀ F G wτ a
  padded : Radius a T w
  pack : Pack P M z mu pHw W e K κ F G L a
  first : dist (gross L) leftY < ε
  last : dist (tarif L) rightY < ε
  comparator : dist ((gross L)*(tarif L)) (leftY * rightY) < ε
  eu : dist (levy L) wik < ε
  eu_cross : dist ((levy L) - (gross L)*(tarif L)) (wik-leftY*rightY) < ε
  amber : B/2 < ((levy L) - (gross L)*(tarif L)).re
  real_joint : dist (D.play (bothA L)) jointY < ε
  real_cross : dist (D.play (bothA L) - (gross L)*(tarif L)) bat < ε
  salute : ‖bat‖/2 < ‖D.play (bothA L) - (gross L)*(tarif L)‖


local notation "hire" => Score P M z mu pHw W e K x₁ T κ F G (X:=X) (Y:=Y) wτ B

variable (U : P.Register)
private lemma dist_half {x y : ℂ}
    (h : dist y x < ‖x‖/2) :
    ‖x‖/2 < ‖y‖ :=
  (by rw [dist_comm,dist_eq_norm] at h; linarith only [h,norm_sub_norm_le x y])

local notation "eHalf" => (min ε (‖bat‖/2))
include U τ pW
private lemma pass (_h : Radius a T w) (b : Placement T ξ₀ F G wτ a)
    (t : dist (D.play (spear HCv w ΓJ ΓK)) jointY < eHalf) :
    ∀ᶠ j in atTop, hire a ε ξ₀ j D := by
  have he : 0 < ε := (dist_nonneg.trans_lt t).trans_le (min_le_left ..)
  have h0 := clarion P M z mu pHw W e K x₁ T κ F G τ wτ _ _ D a b _h U
  obtain ⟨h1,h2⟩ := initial P M z mu pHw W e K x₁ T κ F G τ wτ pW
  have h3 : Tendsto (fun j => levy j) atTop (𝓝 wik) := by
    rw [← (lightingW P M z mu pHw W e K x₁ T κ F G τ wτ pW).1]
    exact pW.budget.pairZ
  have hx := h1.mul h2
  have u := (h0.sub hx).eventually (isOpen_ball.mem_nhds
    (show D.play (spear HCv w ΓJ ΓK) - leftY * rightY ∈ ball bat eHalf from by
      rw [inkTest,mem_ball,dist_sub_right]
      exact t))
  filter_upwards [packing P M z mu pHw W e K κ F G a b.radius.1,
    pW.region, u,
    (Metric.tendsto_nhds.mp h1) ε he, (Metric.tendsto_nhds.mp h2) ε he,
    (Metric.tendsto_nhds.mp hx) ε he, (Metric.tendsto_nhds.mp h3) ε he,
    (Metric.tendsto_nhds.mp (h3.sub hx)) ε he,
    h0.eventually (isOpen_ball.mem_nhds (mem_ball.mpr t))] with l h g d r s v f p t
  exact ⟨b, _h,h,r,s,v,f,p,g.2.2,
    lt_of_lt_of_le t (min_le_left ..),lt_of_lt_of_le d (min_le_left ..),
    dist_half (lt_of_lt_of_le d (min_le_right ..))⟩

omit τ pW
variable (Hτ : Duet P M z mu pHw W e K x₁ T κ Y X wτ ξ₀ F G B)
    (dancer : ∀ n, Coat F n) (baker : ∀ n, Coat G n)
include Hτ
theorem salary (v : Fare wτ a) (t : 0 < ε) :
    ∀ᶠ w in 𝓝[>] (0 : ℝ≥0), Radius a T w ∧
      (∀ {n : ℕ} (A : Coat F n) (C : Coat G n), Nonempty (Song w A C)) ∧
      ∀ᶠ n in atTop, ∀ D : Song w (dancer n) (baker n), ∀ᶠ j in atTop, hire a ε ξ₀ j D := by
  have zc : 0 < eHalf := lt_min t (half_pos (norm_pos_iff.mpr Hτ.direct))
  have v₀ : Placement T ξ₀ F G wτ a := placed P M z mu pHw W e K x₁ T κ F G wτ Hτ.wrap v
  filter_upwards [cue_goal HCv (asJ (chirality 3)) Hτ.tale ΓJ ΓK Hτ.ticket dancer baker zc,
    self_mem_nhdsWithin (s:=Set.Ioi 0),
    ((NNReal.continuous_coe.continuousAt.tendsto
      |>.mono_left nhdsWithin_le_nhds).eventually (ge_mem_nhds (lt_min Hτ.wrap.tempo (half_pos v.1))))] with w p s d
  let r : Radius a T w := ⟨s, le_min_iff.mp d⟩
  refine ⟨r,fun A C=>hired T F G wτ A C a v₀ r,p.mono (fun n h D => ?_)⟩
  exact pass P M z mu pHw W e K x₁ T κ F G Hτ.ticket wτ Hτ.wrap D U r v₀ (h D)

/-- Withhold all tolerance decisions on the cabinet placement until after Duet.
Illustrates use of the precision order on *any* requested arbitrarily high
common length (at or above threshold after widths and stencils). -/
theorem hired_now (v : Fare wτ a) (t : 0 < ε) :
    ∃ (w : ℝ≥0) (n : ℕ) (A : Coat F n) (C : Coat G n) (D : Song w A C),
        ∀ᶠ j in atTop, hire a ε ξ₀ j D := by
  let f (p : Curtain) n := (Coat.weave p n).some
  obtain ⟨w, _, h, u⟩ :=
    (salary P M z mu pHw W e K x₁ T κ F G wτ U Hτ (f F) (f G) v t).exists
  let ⟨n,g⟩ := u.exists
  let D := (h (f F n) (f G n)).some
  exact ⟨w,n,_,_,D,g D⟩
#print axioms hired_now
#print axioms pay_cross
end YM.LocalFieldBounds.Motif
