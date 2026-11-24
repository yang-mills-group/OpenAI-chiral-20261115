import YM.SU5.Reconstruction.Moat.Cash
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
local notation "r̂"=> reversion (tent Y H) Λ
local notation "€"=> Fund Y H V G C a χ
variable (j b:Axis)(p:b≠j)
include p
lemma reverser (v:Gt): reverseOne j (eject b v)=eject b v:=by ext1 i; by_cases h:i=j<;>simp [h,p.symm,reverseOne]
lemma mirrorsAway {u v: D' b}{d: marks (timeMesh Λ)}(t:v.val= r̂ b d u.val):
  (θ b) ((θ j) v.val) = FirstWindows.move (tent Y H) (eject b (-d)) ((θ j) u.val):= by
 rw [mirror_commuting Y H b, t, upright, ← eject_neg, flipped_moves, reverser _ _ p]
@[simp] lemma singletonAway (t:Gt): sidePay b (eject j t)=(t:ℝ) • transversal b j p.symm:= by
 apply Subtype.ext; ext k; by_cases h:k=b
 · subst k; change (sidePay b (eject j t)).val b = _; rw [show (sidePay b _).val b=0 from (sidePay b (eject j t)).property]; simp [transversal,p]
 rw [sidePay,coordinates_eject]; -- coe
 change (rimPay b _).val k=_; rw [rimPay_at b _ k h]; by_cases v:k=j<;>simp [v,transversal]

variable (P':saunters Y H V G.history G.clipped b false (C b) (displacement Y H V G.history G.clipped a false (C a) χ b (C b))=⊤) (z:placement Λ) (u:marks (timeMesh Λ))
include P'
lemma Fund.lateral (f g k₀:D' b)(h:g.val= r̂ b u f.val)(s:k₀.val=(θ j) g.val)(t:Gt)(v:(u:ℝ)≤ (z b:ℝ)): Fund Y H V G C a χ ((θ j) f.val*m₁ (z+eject j t) f.val) (inner ℂ ((Vo b) k₀) ((S₀ b).U (sidePay b z + (t:ℝ) • transversal b j p.symm) ((S₀ b).E (Real.toNNReal ((z b:ℝ) - (u:ℝ))) ((Vo b) f)))):=by
 let x:=z+eject j t; let y:= eject b (-u); have e: coordinates Λ (y+x) b=(z b:ℝ)-(u:ℝ):= by unfold x y; simp [coordinates_eject,p,sub_eq_add_neg,add_comm]
 have r:= Fund.warm Y H V G C a χ b P' k₀ f (y+x) (by rw [e]; exact sub_nonneg.mpr v); apply Fund.before Y H V G C a χ y
 have p': sidePay b (y+x)= sidePay b z+(t:ℝ) • transversal b j p.symm:=by rw [sidePay_add,discount,zero_add,show x=z+eject j t from rfl,sidePay_add,singletonAway _ _ p]
 rw [e,p'] at r
 refine Eq.subst (motive:=fun x=> € x _) (?_: (θ b) k₀.val *m₁ (y+x) f.val=m₁ y ((θ j) f.val*m₁ (z+eject j t) f.val)) r
 rw [s,mirrorsAway Y H G j b p h,move_prod,move_sum]

-- clocks align these four positions. For x and g both positive and negative OF OWN tests, k funds.Heights exact.
end Reflector
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
