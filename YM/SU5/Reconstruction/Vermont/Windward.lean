import YM.SU5.Reconstruction.Vermont.Motor
import YM.SU5.Reconstruction.Vermont.Benefit
import YM.SU5.Reconstruction.Vermont.Reeler
set_option autoImplicit false
set_option maxHeartbeats 800000
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
local notation "θ" i:max=> flipMark i (tent Y H)
local notation "m₁" => FirstWindows.move (tent Y H)
local notation "ℓ_"=>osValue Y H V G a (C a) χ
open BridgeClub Reflector
namespace Crease
variable (F: BoostBacking Y H V G C a χ)
variable (j z:Axis) (b:j≠z)
open Lens Sail
local notation "Π₀" i:max=> opCarries Y H V G i (C i) (w i)
local notation "L0" => Sight Y H V G C a χ j
local notation "Fz" => (Vo z)
local notation "ζ"=> floor Y H V G C a χ j
local notation "S"=> (S₀ j)
local notation "Ω"=> (Ω₀ j)
structure Charter (U:Set E4)(t:marks (timeMesh Λ))(A:(G₀ j).Op)(M:ℕ→ℂ→(G₀ j).Op) : Prop where
 clock : ∃ c,∀ n,WickScript (S₀ j) (ζ U) (M n) (Real.toNNReal (t:ℝ)) c
 scout (p:G₀ j) : Tendsto (fun i=> inner ℂ p (M i 1 Ω)) atTop (𝓝 (inner ℂ p (A Ω)))
local notation "Δ"=> Charter Y H V G C a χ j
lemma gain (U:Set E4)(t:Gt)(A:(G₀ j).Op)(M:ℕ→ (G₀ j).Op) (p:Optical Y H V G C a χ j U t A M): ∃ Y':ℕ→ℂ→(G₀ j).Op, Charter Y H V G C a χ j U t A Y' ∧ ∀ n,Y' n 1=M n:=by
 obtain ⟨c,r⟩:= p.armour; choose P hp e using fun n=> (r n).wake; refine ⟨P,⟨⟨c,hp⟩,fun q=>?_⟩,e⟩; simp_rw [e]; exact p.fare q
include F b
lemma reads (k:Creased Y H V G C a χ F j z b) (W:Set RSpace) (h:IsCompact W)(A:(J₀ j).Op)(M:ℕ→ℂ→(G₀ j).Op)(x:Sky K)(d:Gt)(d0:0≤ (d:ℝ))(u:(Q j) x d A)
    (q':Charter Y H V G C a χ j (panelFace j W) d ((Π₀ j) A) M) : Limited atTop (fun i=>M i 1) ((Π₀ j) A):=by
 obtain ⟨R,v⟩:=panel_bound j h; obtain ⟨c,e⟩:= q'.clock; exact charged Y H V G C a χ F j z b k _ R (fun i v'=>v i v' z b.symm) d d0 A x u _ ⟨⟨c,fun i=>(e i).understands⟩,q'.scout⟩
omit F b
-- for actual gauge invariant memberships, a physically localized thermal WK bill to buy on THIS law: only ask panel projector at time0 corresponding to
-- Eu lookup regions.Cost price; not already granting Θ enough OP.Thick. Enough across pair footprints.
def Registered : Prop:= ∀ (U:Set RSpace)(d:Gt), U⊆ Chambers.strip j 0 d → IsCompact U→ 0< (d:ℝ)→ ∀ (x:Sky (tent Y H))(A:(J₀ j).Op),x∈ Ds U → (Q j) x d A → ∃ M, Optical Y H V G C a χ j (panelFace j U) d ((Π₀ j) A) M
variable (c : Registered Y H V G C a χ j)
include c
lemma answers (U:Set RSpace)(d:Gt)(p:U⊆ Chambers.strip j 0 d)(q:IsCompact U)(h:0< (d:ℝ))(x:Sky (tent Y H))(A:(J₀ j).Op)
 (t:x∈ D U) (e:(Q j) x d A): ∃ M:ℕ→ℂ→(G₀ j).Op, Charter Y H V G C a χ j (panelFace j U) d ((Π₀ j) A) M:=by
 obtain ⟨F,g,e⟩:= northC Y H V G C a χ j U d h x t p A e
 obtain ⟨M,Hℓ⟩:= c U d p q h F A g e
 obtain ⟨Y',X,p⟩:= gain Y H V G C a χ j _ d _ M Hℓ; exact ⟨Y',X⟩

-- one window query.Hinge includes moving ENSEMBLE reference with width. Shifting PURE time to start, same Γ comparison. Thus keep EXACT panelFace!
omit c
variable (U:Set RSpace)
local notation "Ξ" p:max=> FirstWindows.move (tent Y H) (eject j p)
include V
lemma slide_pin (r:Gt)(x:Sky K)(u : x∈ D U)(d:Gt)(p:U⊆ Chambers.strip j r ((r:ℝ)+d)) :
    (Ξ (-r)) x∈ D (slides (coordinates Λ (eject j (-r))) U) ∧ panelFace j U=panelFace j (slides (coordinates Λ (eject j (-r))) U) ∧ slides (coordinates Λ (eject j (-r))) U⊆ Chambers.strip j 0 d := by
 let e:= coordinates Λ (eject j (-r)); let f(y:RSpace):= WithLp.toLp 2 y - y j • basis j
 have he(y:RSpace): f y=f (y+e):=by
   ext i; by_cases k:i=j
   · subst i; unfold f; simp
   unfold f e; simp [k,coordinates_eject]
 refine ⟨moving Y H V G _ _ u, Subset.antisymm ?_ ?_,?_⟩
 · rintro _ ⟨y,p,rfl⟩; exact ⟨y+e, mem_image_of_mem _ p,(he y).symm⟩ -- tune
 · rintro z ⟨_,⟨y,h,rfl⟩,rfl⟩; exact ⟨y,h,he y⟩
 rw [eject_neg, map_neg, coordinates_eject]; apply subset_trans (image_mono p); change slides (-eject j (r:ℝ)) (Chambers.strip j (r:ℝ) ((r:ℝ)+d)) ⊆ Chambers.strip j 0 d; rw [show slides _ _= _ from strip_zero j (r:ℝ) ((r:ℝ)+d), add_sub_cancel_left]; -- maybe target
include V
end Crease
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
