import YM.SU5.Reconstruction.GiftWrap.OneTurn
import YM.SU5.Reconstruction.GiftWrap.Aqueduct
/-! # Wall right edges : extending two-operand cross through actual Schwinger sector -/
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
open CrossedFrame
local notation "U"=>flank j 0∩flank z 0
local notation "Λ₁" i:max=>onceLens Y H V G C a χ i
local notation "Π" i:max=> opCarries Y H V G i (C i) (w i)
variable {D₀:Hilbert} (Z : Clasp D₀ (fort Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))) (fort Y H V G.history G.clipped z false (C z) (displacement Y H V G.history G.clipped a false (C a) χ z (C z))))
variable (p:Quarter Y H V G C a χ j z b.symm Z)
local notation "Tm" i:max=> Picket.trans (S₀ i)
local notation "Ω" i:max=> Ω₀ i
local notation "Sq" => (S₀ j)
namespace Boots
local notation "lu" x:max=> (Tm j) ((x:ℝ) • basis z)
local notation "BC" => parcelUp Sq
open Lens Sail
local notation "lz" T₁:max => (Tm z) ((T₁:ℝ) • basis j)
local notation "N" => reserves Y H V G C a χ j z Z
local notation "Φ₀" x:max=> far Y H V G j (C j) (w j) z x false
variable {x: Sky (tent Y H)} (d v0 s t: marks (timeMesh Λ))
variable (A:(indoor Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))).Op)
  (A':(indoor Y H V G.history G.clipped z false (C z) (displacement Y H V G.history G.clipped a false (C a) χ z (C z))).Op)
variable (f0: Follows Y H V G j (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j)) x s A)
  (f1: Follows Y H V G z (C z) (displacement Y H V G.history G.clipped a false (C a) χ z (C z)) (FirstWindows.move (tent Y H) (eject z (-d)) x) v0 A')
variable (u v:Axis→marks (timeMesh Λ)) (L : (fort Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))).Op)
local notation "η" => u z+v z+(u z-(d+v0))
local notation "E₀"=> F.forward z
include p F f0 f1
lemma wallCorner (tL:Sight Y H V G C a χ j u v L)(k:d+v0<u z)(r:s<t)(e:0≤ (s:ℝ)) (x':G₀ j)(hx:x'∈ Φ₀ d)(q:G₀ j)(h:q∈ N η): ∃ c>0, ∃ f,Lens.Plan (S₀ j) ((Π j) A) L (ℜ t) (ℜ s) c x' q f:= by
 obtain ⟨S',es⟩:= (doorway Y H V G C a χ j z Z η q).1 h; subst q; obtain ⟨p',rfl⟩:= LinearMap.mem_range.mp hx
 let y':D' j := ⟨p'.val,domain_loose Y H G _ (domain_mono Y H G inter_subset_left p'.property)⟩
 obtain ⟨l0,ϕL⟩:= leftGate Y H V G j z b y' d t (domain_loose Y H G _ (domain_mono Y H G inter_subset_right p'.property))
 obtain ⟨θ',h₀,y,T₁,hT,k0,a0⟩:=tL; obtain ⟨W,D₁⟩:= a0 z b.symm
 let R:= (lz t) (Z.r S'); let δ':=u z-(d+v0); let ρ:= ℜ δ'; have hρ: 0<(δ':ℝ):= sub_pos.mpr k; have Hρ:0<ρ:= Real.toNNReal_pos.mpr hρ
 let ω:=transversal z j b; let ℓ:=le_of_eq (transversal_norm z b); let Sz:=(S₀ z)
 let F'(n:ℕ):=screen Sz E₀ ω ℓ ρ Hρ ((Π z) A') ((Π z) (W n)) ((Vo z) l0) R
 obtain ⟨ζ,bζ⟩:= D₁.bounded
 have h0:0 < (t:ℝ):= lt_of_le_of_lt e r
 have ℓt(i:ℕ)(q0:Gt): (s ≤ q0 → q0+h₀ i≤t → (_:ℂ)=_) ∧ (q0+h₀ i≤0 → -t≤ q0 → s≤ t → (_:ℂ)=_) := wallChart Y H V G C a χ F j z b Z p d v0 s t A A' f0 f1 (u z) (v z) (h₀ i) (T₁ i) (W i) (hT.stays i) (D₁.beyond i) k S' _ _ ϕL q0 h0.le
 refine ⟨(ρ:ℝ), (show 0<(ρ:ℝ) from Hρ), promotion (f:=F') Sq _ _ _ _ (ρ:ℝ) _ _ (fun i=>slit_opens Sz E₀ _ _ ρ Hρ _ _ _ _) Hρ ⟨_,fun n ζ' h=> anchored_cost Sz E₀ _ ℓ ρ Hρ _ _ _ _ (le_refl _) (bζ n) h⟩ Gt (daylight (timeMesh Λ)) hT.short hT.propitious ?_ ?_⟩
 · intro i i' hp; rw [Real.coe_toNNReal (t:ℝ) h0.le,Real.coe_toNNReal (s:ℝ) e] at hp
   have hv: ∀ᶠ n in atTop,i+(h₀ n:ℝ)< (t:ℝ):=(tendsto_const_nhds (x:=i)|>.add hT.short).eventually (gt_mem_nhds (by simpa using hp.2)); filter_upwards [hv] with n e'; rw[Real.coe_toNNReal (s:ℝ) e]; exact ((ℓt n ⟨i,i'⟩).1 hp.1.le e'.le).symm
 intro i i' hp; rw [Real.coe_toNNReal (t:ℝ) h0.le] at hp
 have hv:∀ᶠ n in atTop,i+(h₀ n:ℝ)<0:=(tendsto_const_nhds (x:=i)|>.add hT.short).eventually (gt_mem_nhds (by simpa using hp.2)); filter_upwards [hv] with n e'; rw[Real.coe_toNNReal (s:ℝ) e]; exact ((ℓt n ⟨i,i'⟩).2 e'.le hp.1.le r.le).symm
end Boots
end Crease
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
