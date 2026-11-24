import YM.SU5.Relativistic.Intervals
import YM.SU5.Selected.Appointments
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

/-- At one level, exact booking into this tile. No internal shifts reversed through
imaginary time. Positive thickness. -/
structure Docked (W:Slab (timeMesh Λ)) (X : Marks (tent Y H) false) (B : driveAlgebra Y H V Q Qt j false J) : Prop where
  certified : ∃ (r:ℤ)(w:ℕ), notch M s r=W.lower ∧ notch M s (r+w)=W.upper ∧ ∃ (p:0<w)(x:Entry Y H s j false w), x.val.val= relocate K j (-r) X.val ∧ entrance Y H V s Q Qt j false J x p=B
local notation "dock" => Docked Y H V s Q Qt j J
namespace Docked
variable {W : Slab (timeMesh Λ)}{B:driveAlgebra Y H V Q Qt j false J} {X:Marks (tent Y H) false}
lemma gridded (p:dock W X B) : W.lines s:= by obtain ⟨r,w,h,t,_⟩:=p.certified; exact ⟨⟨_,h⟩,⟨_,t⟩⟩
lemma uniqueB (p:dock W X B) {d:𝔅}(a:dock W X d) : B=d:=by
  obtain ⟨r,w,h,t,l,x,hb,rfl⟩:=p.certified; obtain ⟨r',w',h',t',l',x',hb',rfl⟩:=a.certified
  obtain rfl:r=r':= notch_tight M s (h.trans h'.symm)
  have he:w=w':=by have h:= notch_tight M s (t.trans t'.symm); omega
  subst w'; exact congrArg (fun y: Entry Y H s j false w => entrance Y H V s Q Qt j false J y l) (Subtype.ext (Subtype.ext (hb.trans hb'.symm)))

lemma elevated (p:dock W X B) (t:ℕ)(h:s≤t) : Docked Y H V t Q Qt j J W (upGrade Y H s Q false X t) B:=by
  obtain ⟨u,w,hv,hw,e,x,hx,rfl⟩:= p.certified
  let c:=Λ.R.L.val^(t-s); have he : 0 < c*w:= Nat.mul_pos (pow_pos Λ.R.L.property _) e
  refine ⟨_,c*w,(notch_up M s t h u).trans hv,?_, he,furnished Y H s Q j false w x t h,?_,Subtype.ext (refined_box Y H V s Q Qt j false J w x e t h).symm⟩ -- nesting exists? need constructor
  · rw [←hw,←notch_up M s t h]; unfold c castor; rw [mul_add,Nat.cast_mul,Nat.cast_pow]; rfl
  change stream Y H D s _ x.val.val = relocate K j _ (stream Y H D s _ X.val); rw [hx]
  unfold relocate gaugeT; rw [show (K).B=Λ.block from rfl,chime_X Y H V s j _ Q.circuit (marksSpec false X).1]
  congr 1
  unfold castor; rw [← mul_neg]; unfold Heat.gaugeShift; ring! -- tune
end Docked
local notation "Uv" l:max v:max=> (turnstile Y H V Q Qt j false J χ).raw l (fun i=> (v i.val : ↥(marks (timeMesh Λ))))
noncomputable def spacePos (v: Axis → Stamp (timeMesh Λ)): (Ρ).Op := Uv (look j) v
local notation "U"=> spacePos Y H V Q Qt j J χ
lemma spacePos_origin : U 0=1:=Germ.Alliance.raw_zero S _
lemma spacePos_mul (u v : Axis → Stamp (timeMesh Λ)): U u*U v= U (u+v):=((S).travelR (look j) (fun i=>u i.val) (fun i=> v i.val)).symm
lemma spacePos_independent (v : Axis → Stamp (timeMesh Λ)) (x:ℝ≥0) : U v * A x = A x * U v:= by
  change (U _).comp _= _
  exact (S).hard _ _ (fun i _ v=> (rides_trans Y H V Q Qt j false J χ (α:=i) v x).symm) _
lemma heat_origin (v : ℝ≥0) : A v Ω=Ω := ride_affordable Y H V Q Qt j false J χ (fun s n=> hinges Y H V s Q Qt j false J χ n) v

-- panel label actions
variable (l₁:List (Trans j)) {w:ℕ} (p : 0 < w)(x:Entry Y H s j false w)
variable (z:Cover)
local notation "Ξ"=> fun i':Axis => notch (timeMesh Λ) s (z i')
noncomputable def traverseEntry :Entry Y H s j false w:= l₁.foldr (fun i q=> alongS Y H s j false w q i (z i.val)) x
local notation "Qₚ" t:max=> traverseEntry Y H s j t x z
lemma traverseEntry_val : (Qₚ l₁).val.val=cad K (spare j l₁) z x.val.val:=by
 induction l₁ with
 | nil=> rfl
 | cons i l ih=> rw [show Qₚ (i::l)=alongS Y H s j false w (Qₚ l) i (z i.val) from rfl,alongS_val,ih]; rfl
lemma traverseEntry_cost : (Uv l₁ Ξ) * B₀ s x p = (B₀ s (Qₚ l₁) p) * (Uv l₁ Ξ):=by
  induction l₁ with
  | nil=>rfl
  | cons i l ih=>
    let Z:=shiftStamp Y H V Q Qt j false J i (N s (z i.val))
    change (ρ Z * (Uv l Ξ)) * _ = ρ (P₀ s (alongS Y H s j false w (Qₚ l) i (z i.val)) p) * (ρ Z * (Uv l Ξ))
    -- holes? change explicit
    rw [mul_assoc,ih, ← mul_assoc, ← map_mul, show Z * (P₀ s (Qₚ l) p) = _ from entrance_moves Y H V s Q Qt j false J (Qₚ l) p i (z i.val), map_mul, mul_assoc]
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Docked.elevated
