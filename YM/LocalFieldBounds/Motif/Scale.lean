import YM.LocalFieldBounds.Motif.Primer
/-!
# Real pressure
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

abbrev InkA (L : ℕ) := (κ:ℂ) • montage lyre Fresh L
abbrev InkD (L : ℕ) := montage lyre B0 L
local notation "atom" => InkA P M z mu pHw e K x₁ κ
local notation "issu" => InkD P M W x₁

/-- Actual real-time smear over all coordinates. -/
abbrev StageJ (L : ℕ) := warm HS (atom L) (Easel.film F)
abbrev StageK (L : ℕ) := warm HS (issu L) (Easel.film G)
local notation "sJ" => StageJ P M z mu pHw e K x₁ κ F
local notation "sK" => StageK P M W x₁ G
variable {U : ℕ → ↑(radial (P.seasons 3 (P.advocate 3 x₁ 3)))} {x : ↑(radial (P.seasons 3 (P.advocate 3 x₁ 3)))}

lemma stageK (h : (NV).Approaches atTop U x) :
    (NV).Approaches atTop (fun i => sK i (U i)) (((HCv).operator ΓK (Easel.film G)) x) := by
  rw [signatureK]
  exact Post.warmth (face_K P rayPost rayP M 3 S▪ W.tally pHw K) _ h

lemma stageJ (h : (NV).Approaches atTop U x) :
    (NV).Approaches atTop (fun i => sJ i (U i)) (((HCv).operator ΓJ (Easel.film F)) x) := by
  have a := face_J P rayPost rayP M z 3 S▪ mu pHw W e K
  have c := Post.warmth a ((κ:ℂ) • Easel.film F) h
  have g (i : ℕ) : sJ i = warm HS (montage lyre Fresh i) ((κ:ℂ) • Easel.film F) := by
    rw [map_smul]
    apply LinearMap.ext; intro x
    change warm HS ((κ:ℂ) • montage lyre Fresh i) (Easel.film F) x =
      (κ:ℂ) • warm HS _ _ x
    refine Subtype.ext ?_
    simp only [warm_actual, vscale, smul_apply, Submodule.coe_smul_of_tower]
  simp_rw [map_smul, signatureJ, g, map_smul] at c ⊢
  exact c



-- Heated real-time fees
omit [Nonempty η] in
lemma use_valise (x : HH x₁) (a : (HH x₁).Op) (F : Curtain) :
    valise HS a (Easel.film F) x =
      ∫ p : Paper, optx HS a (Easel.face p) x ∂ F.ppm :=
  transpire F (fun p : E4 => optx HS a p x)

abbrev Rial (L : ℕ) := valise HS (atom L) (Easel.film F)
abbrev Pound (L : ℕ) := valise HS (issu L) (Easel.film G)
abbrev Flavor (L : ℕ) := Rial P M z mu pHw e K x₁ κ F L
    * Pound P M W x₁ G L

abbrev soup (a : (HH x₁).Op) := inner ℂ ΩJ☆ (a ΩJ☆)
local notation "dish" => soup P x₁
local notation "plate" => Rial P M z mu pHw e K x₁ κ F
local notation "cup" => Pound P M W x₁ G
local notation "brim" => Flavor P M z mu pHw W e K x₁ κ F G
local notation "ab" => inner ℂ ΩJ☆
local notation "vuc" => (HCv).vacuum

include τ
theorem paid_stage :
    Tendsto (fun L => dish (brim L)) atTop (𝓝 jointY) ∧
    Tendsto (fun L => dish (plate L)) atTop (𝓝 leftY) ∧
    Tendsto (fun L => dish (cup L)) atTop (𝓝 rightY) := by
  rw [τ.real_value,τ.real_value,τ.real_value]
  have h : (NV).Approaches atTop (fun _ : ℕ=>vuc) vuc := fun k=> by
    simp only [Grading.budget, Grading.due, sub_self, map_zero, norm_zero,
      mul_zero, tsum_zero]
    exact tendsto_const_nhds
  have g := stageK P M pHw W e K x₁ G h
  have i := stageJ P M z mu pHw W e K x₁ κ F h
  have ci := stageJ P M z mu pHw W e K x₁ κ F g
  have h0 : Tendsto (fun _ : ℕ=>ΩJ☆) atTop (𝓝 ΩJ☆) := tendsto_const_nhds
  have hi := h0.inner (𝕜:=ℂ) (Grading.Approaches.hilbert NV i)
  have hg := h0.inner (𝕜:=ℂ) (Grading.Approaches.hilbert NV g)
  have ht := h0.inner (𝕜:=ℂ) (Grading.Approaches.hilbert NV ci)
  simp only [StageJ,StageK, warm_actual] at hi hg ht
  exact ⟨ht,hi,hg⟩

#print axioms paid_stage
omit τ

end YM.LocalFieldBounds.Motif
