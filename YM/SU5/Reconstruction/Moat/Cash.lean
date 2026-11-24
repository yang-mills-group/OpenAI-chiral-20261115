import YM.SU5.Reconstruction.Moat.Verso
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
variable (j:Axis) (y z:placement Λ) (t t':marks (timeMesh Λ))
local notation "ψ"=> m₁
local notation "r̂"=> reversion (tent Y H) Λ
-- all from same root law. Support at stage explicitly ext paid at sector temperatures
variable {C₁:ℝ}
def Fund (x:Sky (tent Y H))(z:ℂ):Prop := ∃ h:x∈Domain Y H G false univ, osValue Y H V G a (C a) χ ⟨x,h⟩=z
local notation "€"=>Fund Y H V G C a χ
lemma Fund.unique {x:Sky (tent Y H)}{u v:ℂ}(p:Fund Y H V G C a χ x u)(e: € x v):u=v:= p.choose_spec.symm.trans e.choose_spec
lemma Fund.travel {x:Sky (tent Y H)} {u:ℂ} (p:Fund Y H V G C a χ x u)(y:placement Λ) : € (m₁ y x) u:=⟨enrolledu Y H V G p.choose y,(moving_value Y H V G a (C a) χ y _ _).trans p.choose_spec⟩
lemma Fund.before {x:Sky (tent Y H)} {u:ℂ} (y:placement Λ) : Fund Y H V G C a χ (m₁ y x) u→ € x u:= by
 intro p; have g:= Fund.travel Y H V G C a χ p (-y); rwa [move_sum,neg_add_cancel,move_by_zero] at g
variable (F: saunters Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))=⊤)
include F
lemma pairedFund (x y:D' j): Fund Y H V G C a χ ((θ j) x.val * y.val) (inner ℂ ((Vo j) x) ((Vo j) y)):=by
 let p:=paired_forever Y H G j x.val y.val x.property y.property; refine ⟨p,?_⟩; change _= inner ℂ (((Vo j) x).val:J₀ j) (((Vo j) y).val:J₀ j) -- tune H
 rw [voice_full Y H V G j _ _ F,voice_full Y H V G j _ _ F, registered_pair, ← os_across Y H V G a (C a) χ j (C j)]
local notation "T" p:max => coordinates Λ p
omit F
abbrev sidePay (j:Axis)(y:placement Λ) := rimPay j (coordinates Λ y)
@[simp] lemma sidePay_add : sidePay j (y+z)=sidePay j y+sidePay j z:=by unfold sidePay; simp
@[simp] lemma sidePay_sub : sidePay j (y-z)=sidePay j y-sidePay j z:=by unfold sidePay; simp
@[simp] lemma sidePay_neg : sidePay j (-y)= -sidePay j y:=by unfold sidePay; simp
@[simp] lemma discount (t:marks (timeMesh Λ)): sidePay j (eject j t)=0:=by rw [sidePay, coordinates_eject]; exact Anvil.only_pay j _
-- include omitted for helper lemmas
include F
lemma Fund.warm (x y:D' j)(t:placement Λ)(p:0≤ coordinates Λ t j) : Fund Y H V G C a χ ((θ j) x.val * m₁ t y.val) (inner ℂ ((Vo j) x) ((S₀ j).U (sidePay j t) ((S₀ j).E (Real.toNNReal (coordinates Λ t j)) ((Vo j) y)))):=by
 let hz:= later_frame Y H V G j y.val t y.property p
 have h:= pairedFund Y H V G C a χ j F x (⟨_,hz⟩ : D' j); rw [voice_move Y H V G j _ _ F t y p,bridgeEstate, Chambers.Schedule.route,(S₀ j).independent] at h; exact h
lemma Fund.focus (x:D' j)(p:y j=0)(q:0 ≤ (t:ℝ)): € ((θ j) x.val*m₁ (y+eject j t) x.val) (Moat.note (S₀ j) ((Vo j) x) (ℜ t) (sidePay j y)):=by
 have h:coordinates Λ (y+eject j t) j=(t:ℝ):=by simp [p]
 have v:= Fund.warm Y H V G C a χ j F x x (y+eject j t) (by rw [h]; exact q); simpa only [Moat.note,h,sidePay_add,discount,add_zero] using v
lemma Fund.reverse {u:D' j}{d:D' j}(h:d.val= r̂ j t u.val)(p:y j=0)(q:0≤(t':ℝ)):
     Fund Y H V G C a χ ((θ j) u.val*m₁ (y+eject j (- t - t - t')) u.val) (Moat.note (S₀ j) ((Vo j) d) (ℜ t') (- sidePay j y)):= by
 have t₀:=Fund.focus Y H V G C a χ j (-y) t' F d (by simp [p]) q
 rw [sidePay_neg] at t₀; let m:=eject j t; let L:= y+eject j (- t - t -t')
 apply Fund.before Y H V G C a χ (-m-L) 
 refine Eq.subst (motive:=fun x=> € x _) (?_: (θ j) d.val * m₁ (-y+ eject j t') d.val=m₁ (-m-L) ((θ j) u.val*m₁ (y+eject j (-t-t-t')) u.val)) t₀
 rw [h,upright, reversion, move_prod,move_sum, move_sum, show -y+eject j t'+eject j t= -m-L from ?_, show -m-L+ (y+eject j (-t-t-t'))= -m from (by unfold L; abel),mul_comm]
 unfold L m; simp_rw [show (-t - t -t')=(-t) + (-t)+ (-t') from by abel, ←selectRay, eject_neg]; abel

end Reflector
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
