import YM.SU5.Reconstruction.Moat.Pulse
import YM.SU5.Reconstruction.Trap.Castle
import YM.SU5.Reconstruction.Crease.BackLight
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
open BridgeClub Reflector
namespace Crease
variable (F: BoostBacking Y H V G C a χ)
variable (j z:Axis) (b:j≠z)
private lemma busy : DenseRange (Vo j) := (compass_domain_dense Y H V G j (C j) (w j)).mono (fun y e=> by obtain ⟨d,h⟩:=e; exact ⟨Submodule.inclusion (domain_loose Y H G _) d,h⟩ )
theorem chamberEd (A B:(G₀ j).Op)(p:∀ v:D' j,A ((Vo j) v)= B ((Vo j) v)):A=B:= DFunLike.coe_injective ((busy Y H V G C a χ j).equalizer A.continuous B.continuous (funext p))
include F b in
lemma supplyFlare : ∃ J:Flash (G₀ j), ∀ f f':D' j,f'.val= (θ z) f.val→ J.f ((Vo j) f)=(Vo j) f':=by
 let g₀(f:D' j): D' j:= ⟨_,sidestamp Y H G j z b f⟩; -- arg tune sidestamp
 let g : D' j →ₗ⋆[ℂ] D' j:=
  {toFun:=g₀
   map_add':=fun x y=> Subtype.ext (map_add (θ z) x.val y.val)
   map_smul':=fun r x=> Subtype.ext ( (θ z).map_smulₛₗ r x.val)}
 obtain ⟨A,p⟩:= Flash.cycle g (fun x=> Subtype.ext (mirror_twice ..)) (f:=Vo j) (fun f f'=> by
    change inner ℂ ((Vo j) _).val ((Vo j) _).val= inner ℂ ((Vo j) _).val ((Vo j) _).val; -- TC? fort.coherence tune
    rw [voice_full Y H V G j _ _ (F.present j),voice_full Y H V G j _ _ (F.present j),voice_full Y H V G j _ _ (F.present j),voice_full Y H V G j _ _ (F.present j),sidemirror Y H V G C a χ j z b f f' (g f) (g f') rfl rfl]; exact inner_conj_symm _ _) (busy Y H V G C a χ j)
 exact ⟨A,fun x y v=> (p x).trans (congrArg _ (Subtype.ext v.symm))⟩ -- typo
-- check unused included
include b F
noncomputable def Flare : Flash (fort Y H V G.history G.clipped j false (C j) (w j)):= Classical.choose (supplyFlare Y H V G C a χ F j z b) -- arg tune because def unused binder? variable F not included
local notation "Bx"=> Flare Y H V G C a χ F j z b
include b F
lemma flare_cash (x y:D' j)(v:y.val=(θ z) x.val): (Bx).f ((Vo j) x)= (Vo j) y:= Classical.choose_spec (supplyFlare Y H V G C a χ F j z b) x y v
lemma stillHere : (Bx).f (Ω₀ j)= Ω₀ j:= by
 let y:D' j:= ⟨1,domain_one ..⟩; have p:(Vo j) y=Ω₀ j:= comesHome Y H V G C a χ j; rw [← p]; exact flare_cash Y H V G C a χ F j z b y y (flipMark_unit z).symm -- tune
variable (m:Axis)
omit b F in
lemma reverseAway (z m:Axis)(d:m≠z)(u:Gt): reverseOne z (eject m u)=eject m u:=by ext1 i; by_cases b:i=z<;> simp [reverseOne,b,d.symm] -- rw [reverseOne,if_neg b]
lemma shifter (p:placement Λ)(t:0≤coordinates Λ p j) : (Bx).shade ((Pr j) p)=(Pr j) (reverseOne z p):=by
 let q:= reverseOne z p; have e: 0≤coordinates Λ q j:= (show coordinates Λ q j= coordinates Λ p j from (by simp [q,reverseOne,b])).symm ▸ t -- tune
 apply chamberEd
 intro x; let y: D' j:=⟨_,sidestamp Y H G j z b x⟩; have hb:= flare_cash Y H V G C a χ F j z b x y rfl
 let he:m₁ p y.val∈ D (flank j 0):= later_frame Y H V G j y.val p y.property t -- tune
 let hy:=(⟨_,he⟩:D' j); let t': m₁ q x.val∈ D (flank j 0):= later_frame Y H V G j x.val q x.property e
 let s:=(⟨_,t'⟩ : D' j)
 have h:s.val=(θ z) hy.val:= by change _= (θ z) (m₁ p ((θ z) x.val)); rw [flipped_moves, mirror_twice]
 rw [Flash.shade_at,hb,← show (Vo j) hy =(Pr j) p ((Vo j) y) from voice_move Y H V G j _ _ (F.present j) p y t he, flare_cash Y H V G C a χ F j z b hy s h]; exact voice_move Y H V G j _ _ (F.present j) _ x e t'
end Crease
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
