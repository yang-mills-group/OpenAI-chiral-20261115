import YM.SU5.Reconstruction.Moat.Cheque
import YM.SU5.Reconstruction.Moat.Wallet
import YM.SU5.Reconstruction.Moat.Multiple
import YM.SU5.Reconstruction.Moat.Sonic
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
variable (F: ∀ j:Axis, saunters Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))=⊤)
  (S : ∀ j:Axis, Forward (peninsula Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))))
local notation "Bill"=> Billable Y H V G C a χ
variable (j:Axis)(u v C':ℝ)
def Licensed (x : Sky (tent Y H))(t : marks (timeMesh Λ)) (u:ℝ):Prop:=∀ j:Axis, Billable Y H V G C a χ j x t u
local notation "eV"=> Licensed Y H V G C a χ
variable {x: Sky (tent Y H)} {t:marks (timeMesh Λ)} (q:Licensed Y H V G C a χ x t C')
include F S
local notation "J₁"=>Moat.tariff (S₀ j)
local notation "Q₁"=> J₁ ((Vo j) (outgoing Y H G j x t (q j).registers))
local notation "Q₂"=> J₁ ((Vo j) (returning Y H V G j x t (q j).registers))
include q
-- sign budgets pair. h≤sf,motion.Condition pair.Length. SI3. Grants actual inequality.
lemma ignition (y z:placement Λ)(h: y j=0)(s:z j=0)(u':marks (timeMesh Λ))(h₁:0≤(t:ℝ))(h₂:(t:ℝ)≤ (u':ℝ))(b':ℝ≥0)(v':0<b')(Dp:∃ k:Axis,k≠j ∧ (((b'+b':ℝ≥0):ℝ)+(t:ℝ)≤ ((y-z) k:ℝ)∨ ((b'+b':ℝ≥0):ℝ)+(t:ℝ)≤ ((z-y) k:ℝ))) :
    Q₁ (ℜ u') (sidePay j y -sidePay j z)+ Q₂ (ℜ u') (sidePay j y -sidePay j z) ≤ 3*C'^2*(u':ℝ)^2/(b':ℝ)^2:=by
 obtain ⟨b,hb,t'|t'⟩:=Dp
 · rw [← sidePay_sub]; exact launch Y H V G C a χ j b x t (y-z) (q j) (q b) hb F S u' h₁ h₂ (by simp [h,s]) b' v' t'
 rw [show sidePay j y-sidePay j z= -(sidePay j (z-y)) from by rw [sidePay_sub]; abel, Moat.probate, Moat.probate]
 exact launch Y H V G C a χ j b x t (z-y) (q j) (q b) hb F S u' h₁ h₂ (by simp [h,s]) b' v' t'
open Moat
local notation "Pvv"=> (S₀ j).ℚmeasure.region (Moat.band j u v)
include q F
lemma spectral_receipt {ι:Type}[Fintype ι] (z:ι→placement Λ)(h:∀ i,z i j=0) (s:∀ i k:ι, v*‖sidePay j (z i)-sidePay j (z k)‖≤ 1)
   (r:marks (timeMesh Λ))(e:0≤(t:ℝ))(l:(t:ℝ)≤(r:ℝ))(b':ℝ≥0)(v₁:0<b')(p:∀i y:ι, i≠y→ ∃ k:Axis,k≠ j∧ (((b'+b':ℝ≥0):ℝ)+(t:ℝ)≤ ((z i-z y) k:ℝ)∨ ((b'+b':ℝ≥0):ℝ)+(t:ℝ)≤ ((z y-z i) k:ℝ)))
   (B:ℝ)(hp:0≤B)(he:B*(r:ℝ)≤1-Real.exp (-u*(r:ℝ))) :
     let Xp:=(Vo j) (outgoing Y H G j x t (q j).registers); let Y₁:=(Vo j) (returning Y H V G j x t (q j).registers); let N:ℝ:=Fintype.card ι
     (N^2/2)*(B*(r:ℝ))*(‖Pvv Xp‖^2+‖Pvv Y₁‖^2) ≤ (N*(3*C'^2*(r:ℝ)^2/(b':ℝ)^2)+4*C'^2)*N :=by
 intro Xp Y' N
 -- term Mood wants he & g h etc soft
 let b:= (r:ℝ).toNNReal; have ctx:(b:ℝ)=r:= Real.coe_toNNReal _ (e.trans l)
 have g := Moat.wallet (S₀ j) (fun i=>sidePay j (z i)) b Xp Y' u v C' (S j) s hp (by rw [ctx]; exact he) ((voicebill Y H V G C a χ j F _).trans_le (q j).positive) ((voicebill Y H V G C a χ j F _).trans_le (q j).negative) _ (by positivity : 0≤3*C'^2*(r:ℝ)^2/(b':ℝ)^2) (fun i y q'=> ignition Y H V G C a χ F S j C' q _ _ (h i) (h y) r e l b' v₁ (p i y q'))
 rw [ctx] at g; exact g
end Reflector
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
