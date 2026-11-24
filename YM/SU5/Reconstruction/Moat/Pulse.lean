import YM.SU5.Reconstruction.Moat.Bank
import YM.SU5.Reconstruction.Moat.Zone
import YM.SU5.Reconstruction.Cashier.Foyer
import YM.SU5.Reconstruction.Moat.Diode
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock ConePrice SelectionAnalysis Germ Chambers
open Anvil
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G false
local notation "Ds" => Domain Y H G true
local notation "Gt" => marks (timeMesh Λ)
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (a:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped a false (C a) →⋆ₐ[ℂ] ℂ)
local notation "w" i:max=> displacement Y H V G.history G.clipped a false (C a) χ i (C i)
local notation "J₀" i:max=> indoor Y H V G.history G.clipped i false (C i) (w i)
local notation "C₀" i:max=> saunters Y H V G.history G.clipped i false (C i) (w i)
local notation "G₀" i:max=> fort Y H V G.history G.clipped i false (C i) (w i)
local notation "Ω₀" i:max=> vocation Y H V G.history G.clipped i false (C i) (w i)
local notation "S₀" i:max=> peninsula Y H V G.history G.clipped i false (C i) (w i)
local notation "ℜ" p:max=> Real.toNNReal (p:ℝ)
local notation "Pr" i:max=> bridgeEstate Y H V G i (C i) (w i)
local notation "Vo" i:max=> coreOs Y H V G i (C i) (w i)
local notation "Os" i:max=> compassKet Y H V G i (C i) (w i)
local notation "D'" i:max=> Domain Y H G false (flank i 0)
local notation "Tx" => timeMesh Λ
local notation "Q" i:max=>Follows Y H V G i (C i) (w i)
local notation "X" i:max=> OSvector Y H V G i (C i) (w i)
local notation "θ" i:max=> flipMark i (tent Y H)
local notation "m₁" => FirstWindows.move (tent Y H)
local notation "ℓ_"=>osValue Y H V G a (C a) χ
namespace Reflector
variable (j:Axis)
local notation "Ω" i:max=>doorstep Y H V G.history G.clipped i false (C i) (w i)
local notation "Π₁"=> opCarries Y H V G j (C j) (w j)
lemma lightship : ‖doorstep Y H V G.history G.clipped j false (C j) (w j)‖ = 1:= Selected.ready .. -- is it namespaced
variable (f:Sky (tent Y H))(t:marks (timeMesh Λ)) {A:(indoor Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))).Op} (p:Follows Y H V G j (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j)) f t A)
include p
lemma emp : A (Ω j)= (OSvector Y H V G j (C j) (w j)) (outgoing Y H G j f t p.pose):= by
 obtain ⟨x,h,w'⟩:=p.graph (⟨1, domain_one ..⟩: D' j); exact Eq.trans (congrArg A (vacuum_ticket Y H V G j (C j) (w j)).symm) (w'.symm.trans (congrArg _ (Subtype.ext (by change (x.val:Sky K)=f; simpa only [move_unit,mul_one] using h)))) -- simpa! maybe reduc
lemma empStar (v:0<(t:ℝ)) : (star A) (Ω j)= (OSvector Y H V G j (C j) (w j)) (returning Y H V G j f t p.pose):= emp Y H V G C a χ j _ t (fromBack Y H V G C a χ j f t p v)
lemma billed (hp:0<(t:ℝ)){M:ℝ}(v:‖A‖≤ M): Billable Y H V G C a χ j f t M:= by
 have he (A:(J₀ j).Op): ‖A (Ω j)‖ ≤ ‖A‖:= by simpa only [lightship,mul_one] using A.le_opNorm (Ω j)
 refine ⟨p.pose,?_,?_⟩; rw [← emp Y H V G C a χ j f t p]; exact (he _).trans v
 rw [← empStar Y H V G C a χ j f t p hp]; exact (he _).trans (norm_star A ▸ v)
variable (u₁: saunters Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))=⊤)
include u₁
lemma carries (v:0< (t:ℝ)): opCarries Y H V G j (C j) (w j) A (Ω₀ j)=(Vo j) (outgoing Y H G j f t p.pose) ∧ opCarries Y H V G j (C j) (w j) (star A) (Ω₀ j)=(Vo j) (returning Y H V G j f t p.pose):= by
 refine ⟨Subtype.ext ?_,Subtype.ext ?_⟩; rw [voice_full Y H V G j _ _ u₁,carries_full Y H V G j _ _ u₁,vocate,emp Y H V G C a χ j f t p]
 rw [voice_full Y H V G j _ _ u₁,carries_full Y H V G j _ _ u₁,vocate,empStar Y H V G C a χ j f t p v]
-- variable p duplication used twice? include p earlier delete. rw after ; nesting tunes.
end Reflector
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
