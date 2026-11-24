import YM.SU5.Reconstruction.PilotLight.LanternRoom
import YM.SU5.Reconstruction.Vermont.Periods
/-! Real-clock earnings. No Momentum Stage hypothesis. Quantifier statements restricted as in CP9. -/
set_option autoImplicit false
set_option synthInstance.maxSize 29000
set_option maxRecDepth 5700
set_option maxHeartbeats 470000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation SlabMark MeshClock
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open CF.Pannier.Chancel
open Fock Lat Lifted
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G
local notation "Gt" => marks (timeMesh Λ)
variable (j : Axis)(c:∀ j:Axis,Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false (c j) →⋆ₐ[ℂ] ℂ)
open Chambers LightBudget
local notation "J₀"=> indoor Y H V G.history G.clipped j false (c j) χ
local notation "w'₀"=> doorstep Y H V G.history G.clipped j false (c j) χ
local notation "L"=> ride Y H V G.history G.clipped j false (c j) χ
local notation "F"=> osValue Y H V G j (c j) χ
local notation "T₀"=> OSvector Y H V G j (c j) χ
local notation "Pr"=> atEstate Y H V G.history G.clipped j false (c j) χ
local notation "Lp'"=> Follows Y H V G j (c j) χ
variable {A B : (indoor Y H V G.history G.clipped j false (c j) χ).Op}
variable (s w:ℕ)
variable {x y:Dome (tent Y H)}
local notation "g₁"=> hOne Λ s w
local notation "g₂" n:max=> hAll Λ s w n
local notation "b₁"=> bOne Λ s w
local notation "Ω"=>w'₀
local notation "Ξ"=>charted Y H V G j (c j) χ
open _root_.YM.Lens ConePrice Sail OS.Semigroup
-- A stage (operator) with Eu widths included. Don't confuse with a proved covariance of ANY local unpadded field!
def grease (v:placement Λ)(t:ℝ)(A : (indoor Y H V G.history G.clipped j false (c j) χ).Op): (indoor Y H V G.history G.clipped j false (c j) χ).Op := (L).edge t * Ξ v * A * Ξ (-v) * (L).edge (-t)
local notation "Sq"=> grease Y H V G j c χ
lemma realPort (v:placement Λ) (d:ℝ): pilotBeam Y H V G j (c j) χ v A B (sideways d)= inner ℂ Ω ((A* (Sq v d B)) Ω) := by
 rw [on_clock]; change _= inner ℂ Ω (A ((L).edge d (Ξ v (B (Ξ (-v) ((L).edge (-d) Ω))))))
 rw [(resides_real Y H V G.history G.clipped j false (c j) χ).1,concert_omega]
lemma grease_heat (v:placement Λ)(t:ℝ)(h:ℝ≥0): Sq v t ((L).E h)=(L).E h:= by
 unfold grease; rw [mul_assoc _ (Ξ v), (concert_heat Y H V G j (c j) χ h v).eq,←mul_assoc, mul_assoc _ (Ξ v), concert_one,mul_one]
 rw [← show (L).E h * (L).edge t=(L).edge t*(L).E h from (L).eitherE .., mul_assoc,unedge',mul_one]
lemma grease_price (v:placement Λ)(t:ℝ): ‖Sq v t A‖≤‖A‖:=by
 have h:‖(L).edge t*Ξ v‖ ≤1:=(norm_mul_le ..).trans ((mul_le_one₀ (Lens.edge_price ..) (norm_nonneg _) (concert_bill ..)))
 have ht:‖(L).edge t*Ξ v*A‖ ≤‖A‖:=(norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) h)
 apply (norm_mul_le ..).trans; apply le_trans (mul_le_of_le_one_right (norm_nonneg _) (Lens.edge_price ..)) ((norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (concert_bill ..)).trans ht))
lemma grease_shape (v:placement Λ)(t:ℝ): Sq v t (A+B)= Sq v t A+Sq v t B:=by unfold grease; rw [mul_add,add_mul,add_mul]
lemma grease_close (v:placement Λ)(t:ℝ)(h:ℝ≥0) (X:ℝ)(p:‖A+(L).E h‖ ≤ X):‖Sq v t A+(L).E h‖≤ X:=by
 rw [← grease_heat Y H V G j c χ v t h,← grease_shape]; exact (grease_price ..).trans p
lemma grease_const (v:placement Λ)(t:ℝ): Sq v t (-1:(J₀).Op)= (-1:(J₀).Op) := by
 have hx := grease_heat Y H V G j c χ v t 0; rw [(L).eZero] at hx; change Sq v t 1=1 at hx
 unfold grease at *; simpa only [mul_neg,neg_mul,hx] -- tune
lemma attendsStrong {X:ℕ→ (indoor Y H V G.history G.clipped j false (c j) χ).Op}{h:ℕ→ℝ≥0}{e:ℕ→ℝ}(p:Tendsto e atTop (𝓝 0))
    (a:∀ n,‖X n+(L).E (h n)‖≤e n) (g:Tendsto h atTop (𝓝 0)) (v:J₀) : Tendsto (fun n=> X n v) atTop (𝓝 (-v)):=by
    have he:Tendsto (fun n=> (X n+(L).E (h n)) v) atTop (𝓝 0):=by
       apply tendsto_zero_iff_norm_tendsto_zero.mpr; apply squeeze_zero (fun n=> norm_nonneg _) (fun n=> le_trans _ (mul_le_mul_of_nonneg_right (a n) (norm_nonneg v))) ((zero_mul _ : 0*‖v‖ = 0) ▸ p.mul_const ‖v‖); exact fun n=> (X n + (L).E _).le_opNorm v
    have ht:= ((L).continuousE v).continuousAt.tendsto.comp g; rw [(L).eZero] at ht
    have hx:= he.sub ht; simpa only [Function.comp_apply,Function.comp_def,ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply, zero_sub, add_sub_cancel_right] using hx
lemma beam_everywhere {Z:ℕ→(indoor Y H V G.history G.clipped j false (c j) χ).Op} {h:ℕ→ℝ≥0}{e:ℕ→ℝ}(p:Tendsto e atTop (𝓝 0))(q:Tendsto h atTop (𝓝 0))(u:∀ n,‖Z n+(L).E (h n)‖≤e n)(k:ℕ→placement Λ)(b:ℕ→ℝ)(v:J₀):
    Tendsto (fun n=> grease Y H V G j c χ (k n) (b n) (Z n) v) atTop (𝓝 (-v)):=attendsStrong Y H V G j c χ p (fun n=> grease_close Y H V G j c χ (k n) (b n) (h n) (e n) (u n)) q v
-- Both interpreting Full and even on Compass (without asserts price).
local notation "G₀"=>fort Y H V G.history G.clipped j false (c j) χ
local notation "Ψ"=>opCarries Y H V G j (c j) χ
lemma costs_there {X:ℕ→(indoor Y H V G.history G.clipped j false (c j) χ).Op}(g:∀ x:J₀,Tendsto (fun n=> X n x) atTop (𝓝 (-x)))(v:G₀): Tendsto (fun n=> (Ψ (X n)) v) atTop (𝓝 (-v)):=by
 let Q':=saunters Y H V G.history G.clipped j false (c j) χ; let π:= Q'.orthogonalProjectionOnto
 have h:= ((π).continuous.tendsto (-(v.val:J₀))).comp (g (v.val:J₀)); rw [map_neg,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self] at h; exact h
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame.beam_everywhere
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame.realPort
