import YM.SU5.Reconstruction.Seams.Orthogonal
import YM.SU5.Reconstruction.Anvil.Merge
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5000
set_option maxHeartbeats 360000
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
namespace LightBudget
open SlabMark MeshClock ConePrice SelectionAnalysis Germ Chambers
variable {J : Calibration}
local notation "D" => Domain Y H G false
local notation "Gt" => marks (timeMesh Λ)
local notation "K₀"=> tent Y H
variable (j : Axis) (C : Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)
local notation "J₀"=> indoor Y H V G.history G.clipped j false C χ
local notation "C₀"=> saunters Y H V G.history G.clipped j false C χ
local notation "G₀"=> fort Y H V G.history G.clipped j false C χ
local notation "Ω₀"=> mainsea Y H V G.history G.clipped j false C χ
local notation "L"=> ride Y H V G.history G.clipped j false C χ
local notation "S"=> peninsula Y H V G.history G.clipped j false C χ
local notation "Π" x:max=> physicalKet Y H V G j C χ x
local notation "F"=> osValue Y H V G j C χ
local notation "A₀"=> flank j 0
set_option quotPrecheck false
local notation "P"=> (C₀).orthogonalProjectionOnto
local notation "θ"=> flipMark j K
local notation "ℜ" p:max=> Real.toNNReal (p:ℝ)
local notation "κ" p:max=> move K p
local notation "Jj"=> Domain Y H G false (flank j 0)open YM.Anvil
local notation "Θ" p:max=> eject j p
local notation "Q" p:max=> opCarries Y H V G j C χ p
local notation "Vo"=> coreOs Y H V G j C χ
local notation "Ft"=> Follows Y H V G j C χ
-- Bool grants with Price $r_n,t_n$ always stamps as needed, goals values in real geometry. External p and w already as prepared from common tests.
variable (tC : saunters Y H V G.history G.clipped j false C χ=⊤)
  (wC : ConePrice.Forward (peninsula Y H V G.history G.clipped j false C χ))
-- physical spec consistency, identity across root.Clarity.
include wC
lemma earns (u:placement Λ) (p: facet (coordinates Λ u)∈ Tunnel j):
    PaysOn (S) (facet (coordinates Λ u)) = bridgeEstate Y H V G j C χ u ∧ 0 ≤ (u j:ℝ):= by
 rw [tunnel_initial] at p; exact ⟨Anvil.realRent _ wC _ p.le,p.le⟩
variable {x y: Sky (tent Y H)} (e t f s:marks (timeMesh Λ)) {A B:(indoor Y H V G.history G.clipped j false C χ).Op}
    (u : Follows Y H V G j C χ (move (tent Y H) (eject j (-e)) x) t A)(v : Follows Y H V G j C χ (move (tent Y H) (eject j (-f)) y) s B)
    (a b : Domain Y H G false (flank j 0))
include tC u v
local notation "Ψ" x:max=> Anvil.facet (coordinates Λ x)
-- no SOT here; seam interactions can ask $R$ price
abbrev horizonPrice (T e t f s : marks (timeMesh Λ)) : Anvil.Price:=⟨T,e,t,f,s⟩
def Quartet (d k:Sky J) (x y:Sky J) (z:placement Λ):= d*(x*(move J z y*k))
lemma embossed (T:marks (timeMesh Λ))(z:placement Λ) (w:Bool) (W:(horizonPrice T e t f s).permeates j w (Anvil.facet (coordinates Λ z))) :
    let X₀:= Quartet (move K (Θ (-T)) (θ a.val)) (move K (Θ T) b.val) x y z;
    ∃ h: X₀ ∈ D univ, osValue Y H V G j C χ ⟨X₀,h⟩= (horizonPrice T e t f s).sale w (S) (Q A) (Q B) (Vo a) (Vo b) (Ψ z):= by
  let Tt:=Θ T; let Tu:=Θ (-T); let Z:=Θ e; let Y₁:=z+eject j f
  let x':= move K (eject j (-e)) x; let y':= move K (eject j (-f)) y
  have hp : move K Z x'=x:= by unfold x' Z; rw [move_sum,selectRay,add_neg_cancel,eject_zero,move_by_zero]
  have hq : move K Y₁ y'=move K z y:=by unfold y' Y₁; rw [move_sum,add_assoc,selectRay,add_neg_cancel,eject_zero,add_zero]
  intro O; let Vt:= horizonPrice T e t f s
  let X:= Ψ z
  have ha (r: Gt): Ψ (eject j r)= Anvil.onlyTime j ((r:ℝ):ℂ):= by rw [coordinates_eject,eject,Anvil.facet_t]; -- test
  have p0:= W.1; have p1:= W.2.1; have p2:= W.2.2
  cases w; swap
  · have he1 : Vt.entry j true X= Ψ (Z-Tu):= by
       unfold Vt Z Tu horizonPrice Anvil.Price.entry; simp only [map_sub,Anvil.facet_sub,ha,if_true,AddSubgroup.coe_neg,Complex.ofReal_neg,← Anvil.single_steal,sub_neg_eq_add]; push_cast; rfl
    have he2: Vt.compare j true X= Ψ (Y₁-(Z+ eject j t)):= by
       unfold Vt Z Y₁ X horizonPrice Anvil.Price.compare; simp only [map_sub,map_add,Anvil.facet_sub,Anvil.facet_add,ha,if_true,← Anvil.single_compensate]; rw [add_sub_assoc, ←Anvil.single_steal]; push_cast; rfl
    have he3: Vt.leaves j true X= Ψ (Tt-(Y₁+eject j s)):=by
       unfold Vt Tt Y₁ X horizonPrice Anvil.Price.leaves; simp only [map_sub,map_add,Anvil.facet_sub,Anvil.facet_add,ha,if_true,Complex.ofReal_sub, Complex.ofReal_add,single_steal,single_compensate]; abel
    rw [he1] at p0; rw [he2] at p1; rw [he3] at p2
    obtain ⟨A1,B1⟩:= earns Y H V G j C χ wC _ p0; obtain ⟨A2,B2⟩:= earns Y H V G j C χ wC _ p1; obtain ⟨A3,B3⟩:= earns Y H V G j C χ wC _ p2
    obtain ⟨k,g⟩:= purchases Y H V G j C χ tC x' y' t s A B Tu Tt Z Y₁ a b u v B1 B2 B3
    have hv: tab K Tu Z Y₁ Tt (θ a.val) x' y' b.val=O:= by unfold tab; rw [hp,hq]; rfl
    refine ⟨hv ▸ k,?_⟩; unfold Anvil.Price.sale; rw [show (⟨O,_⟩: D univ)= ⟨_,k⟩ from Subtype.ext hv.symm,g,he1,he2,he3,A1,A2,A3]; rfl
  have he1 : Vt.entry j false X= Ψ (Y₁-Tu):= by
       unfold Vt Y₁ Tu X horizonPrice Anvil.Price.entry; simp only [map_sub,map_add,reduceCtorEq,Anvil.facet_add,Anvil.facet_sub,ha,if_false,AddSubgroup.coe_neg,Complex.ofReal_neg]; rw [add_sub_assoc,←single_steal,sub_neg_eq_add]; push_cast; rfl
  have he2: Vt.compare j false X= Ψ (Z-(Y₁+ eject j s)):= by
       unfold Vt Z Y₁ X horizonPrice Anvil.Price.compare; simp only [if_false,reduceCtorEq,map_sub,map_add,Anvil.facet_add,Anvil.facet_sub,ha,Complex.ofReal_sub,Complex.ofReal_add,single_steal,single_compensate]; abel
  have he3: Vt.leaves j false X= Ψ (Tt-(Z+eject j t)):=by
       unfold Vt Tt Z X horizonPrice Anvil.Price.leaves; simp only [map_sub,map_add,Anvil.facet_sub,Anvil.facet_add,ha,if_false, reduceCtorEq,← single_compensate,← single_steal]; push_cast; rfl -- unused X
  rw [he1] at p0; rw [he2] at p1; rw [he3] at p2
  obtain ⟨A1,B1⟩:= earns Y H V G j C χ wC _ p0; obtain ⟨A2,B2⟩:= earns Y H V G j C χ wC _ p1; obtain ⟨A3,B3⟩:= earns Y H V G j C χ wC _ p2
  obtain ⟨k,g⟩:= purchases Y H V G j C χ tC y' x' s t B A Tu Tt Y₁ Z a b v u B1 B2 B3
  have hv: tab K Tu Y₁ Z Tt (θ a.val) y' x' b.val=O:= by unfold tab; rw [hp,hq,mul_left_comm (move K z y)]; rfl
  refine ⟨hv ▸ k,?_⟩; unfold Anvil.Price.sale; rw [show (⟨O,_⟩: D univ)= ⟨_,k⟩ from Subtype.ext hv.symm,g,he1,he2,he3,A1,A2,A3]; rfl
end LightBudget
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
