import YM.SU5.Reconstruction.Seams.Court
import YM.SU5.Reconstruction.Anvil.Era
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
variable (j:Axis)(x:Sky (tent Y H))(h:marks (timeMesh Λ)) {A:(indoor Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))).Op} (p:Follows Y H V G j (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j)) x h A)
-- compute adjoint ON FULL. Back unneeded. scope later star nets.
def reversion (J: Calibration) (Λ:Preparation)(j:Axis)(h:marks (timeMesh Λ))(x:Sky J): Sky J:= FirstWindows.move J (eject j h) (flipMark j J x)
local notation "r̂"=> reversion (tent Y H) Λ
lemma upright (j:Axis)(h:Gt)(x:Sky (tent Y H)): flipMark j (tent Y H) (reversion (tent Y H) Λ j h x)=FirstWindows.move (tent Y H) (- eject j h) x:=by unfold reversion; rw [flipped_moves, mirror_twice, reverse_eject, eject_neg]
include V
lemma pose (j:Axis)(h:Gt)(x:Sky (tent Y H))(p:x∈ D (strip j 0 (h:ℝ))):reversion (tent Y H) Λ j h x∈ D (strip j 0 (h:ℝ)):= by
 apply domain_mono Y H G _ (FirstWindows.moving Y H V G _ _ (mirror_support Y H G j x p)); rintro _ ⟨_,⟨y,v,rfl⟩,rfl⟩
 have e:=v.1; have b:=v.2; simp only [Chambers.strip,Set.mem_setOf_eq,mirrorE,if_true, sub_eq_add_neg,Pi.add_apply,coordinates_eject,eject_at]; constructor<;>linarith -- tune mirrorE namespace
lemma enrolledu {p:Sky (tent Y H)} (v:p∈D univ) (m:placement Λ) : FirstWindows.move (tent Y H) m p∈ D univ:= domain_mono Y H G (subset_univ _) (FirstWindows.moving Y H V G _ _ v)
local notation "Dd"=> osValue Y H V G j (C j) (w j)
include p
set_option maxHeartbeats 80000 in
lemma fromBack (hp:0<(h:ℝ)): Follows Y H V G j (C j) (w j) (reversion (tent Y H) Λ j h x) h (star A):= by
 obtain ⟨B,b⟩:= fits Y H V G j (C j) (w j) h hp (r̂ j h x) (pose Y H V G j h x p.pose)
 let T:=eject j h; 
 suffices B=star A by rwa [←this]
 ext1 z; apply congrFun (a:=z) ((physical_dense Y H V G j (C j) (w j)).equalizer B.continuous (star A).continuous _)
 funext k; let y: D' j:= Submodule.inclusion (domain_loose Y H G _) k; apply Dense.eq_of_inner_right ℂ (physical_dense Y H V G j (C j) (w j)); rintro _ ⟨k',rfl⟩; let o:D' j := Submodule.inclusion (domain_loose Y H G _) k'
 change inner ℂ ((X j) o) (B ((X j) y))=inner ℂ ((X j) o) (ContinuousLinearMap.adjoint A ((X j) y))
 obtain ⟨f,p0,h0⟩:= p.graph o; obtain ⟨g,f0,t⟩:= b.graph y
 have hz: (θ j) o.val*g.val=m₁ T ((θ j) f.val*y.val) := by
    rw [p0,f0,move_prod]
    rw [flipMark_mul,flipped_moves,reverse_eject,eject_neg, move_prod, move_sum,show T+ -(eject j h)=0 from add_neg_cancel _,move_by_zero]; unfold reversion; unfold T; ac_rfl
 let H':=paired_forever Y H G j f.val y.val f.property y.property
 rw [ContinuousLinearMap.adjoint_inner_right,←h0,←t,registered_pair,registered_pair]; rw [show (⟨_,paired_forever Y H G j o.val g.val o.property g.property⟩: D univ)= ⟨_,enrolledu Y H V G H' T⟩ from Subtype.ext hz,moving_value]

omit p V
-- Anti on KETS.Full measures. for a different spatial orientation.
variable (j':Axis)(p':j≠j') -- j observer
include p'
lemma sidestamp (f:D' j): (θ j') f.val ∈ Domain Y H G false (flank j 0):=by
 apply domain_mono Y H G _ (mirror_support Y H G j' f.val f.property)
 rintro _ ⟨x,t,rfl⟩; change 0≤ mirrorE j' 0 x j; simpa [mirrorE,p'] using (show 0≤ x j from t) -- notation
include V
lemma sidemirror (f g f' g':D' j) (h:f'.val= (θ j') f.val)(v:g'.val=(θ j') g.val): inner ℂ ((X j) f') ((X j) g')=star (inner ℂ ((X j) f) ((X j) g)):=by
 rw [registered_pair,registered_pair]; have e: (θ j) f'.val*g'.val= (θ j') ((θ j) f.val*g.val):= by rw [h,v,mirror_commuting Y H j, flipMark_mul]; -- order
 let P:=paired_forever Y H G j f.val g.val f.property g.property
 let K':= paired_forever Y H G j f'.val g'.val f'.property g'.property
 rw [show (⟨_,K'⟩:D univ)= ⟨_, (e ▸ K':(θ j') ((θ j) f.val*g.val) ∈ D univ)⟩ from Subtype.ext e]; exact FirstWindows.reflected_read Y H V G j' j (C j) (w j) P _
lemma mirrorsize (f f':D' j) (h:f'.val= (θ j') f.val): ‖(X j) f'‖=‖(X j) f‖:= by
 apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp; rw [← inner_self_eq_norm_sq (𝕜:=ℂ), ← inner_self_eq_norm_sq (𝕜:=ℂ), sidemirror Y H V G C a χ j j' p' f f f' f' h h]; rfl
end Reflector
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
