import YM.SU5.Reconstruction.PilotLight.Clock
import YM.SU5.Reconstruction.PilotLight.Position
/-! Cost for step in stack. Also padding, keeping estimate truly in POWER-operator norm. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5000
set_option maxHeartbeats 280000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation SlabMark MeshClock
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G false
local notation "Gt" => marks (timeMesh Λ)
local notation "K₀"=> tent Y H
variable (j : Axis) (C : Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)
open Chambers LightBudget Germ
local notation "J₀"=> indoor Y H V G.history G.clipped j false C χ
local notation "hₙ"=> hOne Λ
local notation "Ω₀"=> mainsea Y H V G.history G.clipped j false C χ
local notation "w'₀"=> doorstep Y H V G.history G.clipped j false C χ
local notation "L"=> ride Y H V G.history G.clipped j false C χ
local notation "F"=> osValue Y H V G j C χ
local notation "A₀"=> flank j 0
local notation "T₀"=> OSvector Y H V G j C χ
local notation "Pr"=> atEstate Y H V G.history G.clipped j false C χ
local notation "Lq₁" => Follows Y H V G j C χ
variable {A B : (indoor Y H V G.history G.clipped j false C χ).Op}
variable (s w:ℕ)
variable {q d: Bool} {x y:Dome (tent Y H)}
local notation "g₁"=> hOne Λ s w
local notation "g₂" n:max=> hAll Λ s w n
local notation "b₁"=> bOne Λ s w
local notation "bP" n:max=> bAll Λ s w n
local notation "K₁"=> ticket Y H G s
local notation "u"=> stamps Λ s (granite w)
noncomputable def splice (p:placement Λ)(d₀ U W:marks (timeMesh Λ))(A B:(indoor Y H V G.history G.clipped j false C χ).Op): (indoor Y H V G.history G.clipped j false C χ).Op:= A * (Pr (p-eject j U)) * B * (Pr (eject j d₀ - (p+eject j W)))
local notation "Sp"=> splice Y H V G j C χ
lemma splicing (p:placement Λ) (d₀ U W:marks (timeMesh Λ)): ‖Sp p d₀ U W A B‖ ≤ ‖A‖*‖B‖:=by
 unfold splice; refine (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (fare_less ..)).trans ((norm_mul_le ..).trans ?_)); exact mul_le_mul_of_nonneg_right ((norm_mul_le ..).trans (mul_le_of_le_one_right (norm_nonneg _) (fare_less ..))) (norm_nonneg _)
lemma along_stack {n:ℕ}(hw:0<w)(a:x∈insideAt Λ l K q (alcove g₁) s) (t:y∈insideAt Λ l K d (alcove (g₂ n)) s) (h:Lq₁ (K₁ x) b₁ A)(g:Lq₁ (K₁ y) (bP n) B): Lq₁ (K₁ (x*lined K w y)) (bP (n+1)) (Sp u (bP (n+1)) b₁ (bP n) A B):=by
 rw [level_exact Y H V G s hw a t]
 refine boxAfter Y H V G j C χ u _ ?_ ?_ ?_ ?_ h g
 · exact (bTime s w).ge.trans' (by positivity) -- Coe confusing; bTime b=θ; want use ▸
 · rw [aTime]; positivity
 · rw [bTime,strikes]; linarith [gPositive (Λ:=Λ) s hw]
 change (u j:ℝ)+ (↑(bP n):ℝ) ≤ ↑(bP (n+1))
 rw [aTime,strikes,aTime,hstep]
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame.along_stack
