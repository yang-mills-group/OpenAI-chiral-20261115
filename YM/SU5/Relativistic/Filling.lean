import YM.SU5.Relativistic.Docket
/-!
# Timestamped operators (unprojected).
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 280000
set_option synthInstance.maxSize 25000
set_option maxRecDepth 5500
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Set Filter Finset MeasureTheory
open SU Lattice Wilson Lat Mir Phase RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy MeshClock Selected
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  (V:Universal Y H i k I E) (s : ℕ)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}
  (Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)(Qt:Clipped Y H (i∘a) (k∘b))
variable (j:Axis) (J: Arena Y H Q.circuit j 0 false) (χ : displayAlgebra Y H V Q Qt j false J →⋆ₐ[ℂ] ℂ)
local notation "M"=> timeMesh Λ
local notation "N" i:max z:max=> notch M i z
local notation "Ν" => Slab (timeMesh Λ)
local notation "Ρ" => indoor Y H V Q Qt j false J χ
local notation "𝔅" => driveAlgebra Y H V Q Qt j false J
local notation "ρ" => procession Y H V Q Qt j false J χ
local notation "Ω" => doorstep Y H V Q Qt j false J χ
local notation "A" => (ride Y H V Q Qt j false J χ).E
local notation "S" => turnstile Y H V Q Qt j false J χ
local notation "P₀" t:max x:max p:max => entrance Y H V t Q Qt j false J x p
local notation "B₀" t:max x:max p:max => procession Y H V Q Qt j false J χ (P₀ t x p)
local notation "Qm" u:max => Marks (tent Y H) u
local notation "En" s:max w:max=> Entry Y H s j false w

local notation "U" => spacePos Y H V Q Qt j J χ
local notation "dock" => Docked Y H V s Q Qt j J
/-- envelope as function of OFFSET on full lattice (not continuous in all
axes). Allows fixed-sized register tile W moved to fit in fixed renumbered W₀. -/
def encase (W W₀: Slab (timeMesh Λ)) (B:𝔅) (u:Axis → Stamp (timeMesh Λ)) : (Ρ).Op :=
    (A (heatGap W₀.lower (W.lower + u j))) * (U u* ρ B * U (-u)) * (A (heatGap (W.upper+u j) W₀.upper))
abbrev fitsMesh {Λ:Preparation} (j:Axis) (W W₀: Slab (timeMesh Λ)) (u:Axis → Stamp (timeMesh Λ)) : Prop := W₀.lower ≤ W.lower + u j ∧ W.upper+u j ≤ W₀.upper

namespace Docked
section offset
variable (W W₀ : Slab (timeMesh Λ))(X:Marks (tent Y H) false)(B₁:driveAlgebra Y H V Q Qt j false J)
local notation "dock₀"=> Docked Y H V s Q Qt j J W₀
variable (h:Docked Y H V s Q Qt j J W X B₁)
local notation "se" t:max => notch M s (t:ℤ)
include h
lemma pokes (u:Cover) (p:W₀.lines s) (q:fitsMesh j W W₀ (fun i=> notch (timeMesh Λ) s (u i))) :
    ∃ C : 𝔅, Docked Y H V s Q Qt j J W₀ (relocateWorld Y H false u X) C ∧
      ρ C=encase Y H V Q Qt j J χ W W₀ B₁ (fun i=> notch (timeMesh Λ) s (u i)) := by
  let z:= u j; let U₀ (i:Axis):= N s (u i)
  obtain ⟨r,w,he,ht,v,x,F,Yx⟩:=h.certified
  obtain ⟨⟨g,hg⟩,l,hl⟩:=p
  have a:g≤ r+z:= (stamp_le M s _ _).mp (by rw [hg,notch_add,he]; exact q.1)
  have t:r+(w:ℤ)+z ≤ l := (stamp_le M s _ _).mp (by rw [notch_add,hl,ht]; exact q.2)
  obtain ⟨c,(hc:g+(c:ℕ)=r+z)⟩:∃ c:ℕ,g+(c:ℕ)=r+z:= ⟨(r+z-g).toNat,by omega⟩
  obtain ⟨d,(hd:r+(w:ℤ)+z+(d:ℕ)=l)⟩:∃ d:ℕ,r+(w:ℤ)+z+(d:ℕ)=l:= ⟨(l-(r+w+z)).toNat,by omega⟩
  let y:= traverseEntry Y H s j (look j) x u
  let P:= edit Y H s j false c w (SlabMark.identity Y H s j false c) y
  let L:= edit Y H s j false (c+w) d P (SlabMark.identity Y H s j false d)
  have hL: L.val.val=P.val.val :=by unfold L; rw [editor]; change _* relocate _ j _ 1=_; rw [relocate_unit,mul_one]
  have hP: P.val.val= relocate K j (c:ℤ) y.val.val :=by unfold P; rw [editor]; exact one_mul _
  let vP:0<c+w:= by omega
  let vL:0<c+w+d:= by omega
  refine ⟨P₀ s L vL, ⟨g,c+w+d,hg,?_ ,vL,L,?_,rfl⟩,?_⟩
  · rw [show g+((c+w+d:ℕ):ℤ)=l by omega, hl]
  ·
    rw [world_val,hL,hP]
    let Xp:TestFamily K true X.val:=(marksSpec false X).1
    unfold y; rw [traverseEntry_val,F,cad_movement K j (spare j (look j)) Xp]
    let Xt:=cad_paid K (spare j (look j)) Xp u
    rw [chart_piece K j u Xp,relocate_sums K j _ _ Xt,relocate_sums K j _ _ Xt]
    rw [show (c:ℤ)+ -r= -g + u j by unfold z at *; omega]
  have hX: P₀ s P vP = heatStamp Y H V s Q Qt j false J c * P₀ s y v :=
    Subtype.ext (shape_left Y H V s Q Qt j false J w w y v c P hP)
  have hZ: P₀ s L vL = P₀ s P vP * heatStamp Y H V s Q Qt j false J d :=
    Subtype.ext (shape_right Y H V s Q Qt j false J (c+w) (c+w) P vP d L hL)
  have hv: B₀ s y v= (U U₀)*B₀ s x v*(U (-U₀)) := by
     have hz:U U₀ * B₀ s x v = B₀ s y v * U U₀:= traverseEntry_cost Y H V s Q Qt j J χ (look j) v x u
     rw [hz,mul_assoc,spacePos_mul,add_neg_cancel,spacePos_origin,mul_one]
  have h₁: heatGap W₀.lower (W.lower+U₀ j)= whenly M s c:=by
    rw [←hg,←he]
    unfold U₀; rw [←notch_add]; exact heatGap_stamp hc s
  have h₂: heatGap (W.upper+U₀ j) W₀.upper= whenly M s d:=by rw [←ht,←hl]; unfold U₀; rw [←notch_add]; exact heatGap_stamp hd s
  change ρ (P₀ s L vL)= _
  rw [hZ,map_mul,hX,map_mul,hv,Yx]; unfold encase; rw [h₁,h₂]; rfl
end offset
end Docked
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Docked.pokes
