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

local notation "dock" => Docked Y H V s Q Qt j J
local notation "κ" t:max => actor Y H t Q.circuit j 0 false J
local notation "Fb" t:max => Tower.Field Y H t j 0 false
lemma entrance_addition {w:ℕ}(p:0<w)(x y z:Entry Y H s j false w)(a:z.val=x.val+y.val): P₀ s z p= P₀ s x p + P₀ s y p:= by
 apply Subtype.ext; apply test_high Y H V s Q j false J
 intro n h f
 let Z(i:Entry Y H s j false w):=furnished Y H s Q j false w i n h
 change (boxOp Y H V s Q Qt j false J w z p) _= (boxOp Y H V s Q Qt j false J w x p) _+ (boxOp Y H V s Q Qt j false J w y p) _
 rw [snatch Y H V s Q Qt j false J _ z p h, snatch Y H V s Q Qt j false J _ x p h, snatch Y H V s Q Qt j false J _ y p h]
 let C (i : Entry Y H s j false w) : Fb n:= slabT Y H n j false _ (Z i) f
 change arrows Y H V Q.circuit j 0 false J n (C z)= arrows Y H V Q.circuit j 0 false J n (C x) + arrows Y H V Q.circuit j 0 false J n (C y)
 have hx: (Z z).val=(Z x).val+(Z y).val :=by
    change Raise Y H Q.circuit j 0 false s n h z.val= _
    rw [a]; exact Subtype.ext (woven_add Y H Q.circuit s (n-s) (test_entry Y H s j false x) (test_entry Y H s j false y))
 have ht: C z=C x+C y:= by
    apply Subtype.ext; unfold C
    change _= (slabT Y H n j false _ (Z x) f).val + (slabT Y H n j false _ (Z y) f).val; simp only [slab_eq,hx]; exact add_mul ..
 rw [ht,map_add]
lemma entrance_scale {w:ℕ}(p:0<w)(x y:Entry Y H s j false w)(c:ℂ)(a:y.val=c • x.val): P₀ s y p= c • P₀ s x p:=by
 apply Subtype.ext; apply test_high Y H V s Q j false J
 intro n h f
 let Z(i:Entry Y H s j false w):=furnished Y H s Q j false w i n h
 change (boxOp Y H V s Q Qt j false J w y p) _= c • (boxOp Y H V s Q Qt j false J w x p) _
 rw [snatch Y H V s Q Qt j false J _ x p h, snatch Y H V s Q Qt j false J _ y p h]
 let C (i:Entry Y H s j false w): Fb n:= slabT Y H n j false _ (Z i) f
 change arrows Y H V Q.circuit j 0 false J n (C y) = c • arrows Y H V Q.circuit j 0 false J n (C x)
 have hx: (Z y).val=c • (Z x).val :=by change Raise Y H Q.circuit j 0 false s n h y.val=_; rw [a]; exact Subtype.ext (woven_smul Y H Q.circuit s (n-s) (test_entry Y H s j false x) c)
 have ht:C y=c • C x:=by
   apply Subtype.ext; unfold C
   change _= c • (slabT Y H n j false _ (Z x) f).val; simp only [slab_eq,hx]; exact Algebra.smul_mul_assoc ..
 rw [ht,map_smul]

namespace Docked
section tally
variable {W : Slab (timeMesh Λ)}{p q:Marks (tent Y H) false}{B B': driveAlgebra Y H V Q Qt j false J}
lemma plusX (a:dock W p B)(z:dock W q B'):dock W (p+q) (B+B'):=by
 obtain ⟨r,w,g,h,e,x,hv,β⟩:= a.certified
 obtain ⟨d,v,k,t,l,y,h₁,γ⟩:= z.certified
 obtain rfl:r=d:= notch_tight M s (g.trans k.symm)
 have hi:w=v:=by have h:=notch_tight M s (h.trans t.symm); omega
 subst v; obtain ⟨R,c,a'⟩:=x.property; obtain ⟨X,c₁,hp⟩:=y.property

 let i: Fb s:=x.val + y.val
 have hu: Between K j 0 (ruler Λ.block*w) (R∪X):= fun _ h=> (mem_union.mp h).elim (a' _) (hp _)
 let w₁: Entry Y H s j false w:= ⟨i,R∪X,(c.mono Finset.subset_union_left).add (c₁.mono Finset.subset_union_right),hu⟩
 refine ⟨r,w,g,h,e,w₁,?_ ,?_⟩
 · change x.val.val+y.val.val= relocate K j _ (p.val+q.val); rw [hv,h₁]; exact (chime_plus ..).symm
 rw [←β,←γ,entrance_addition Y H V s Q Qt j J e x y w₁ rfl]
lemma scaledX (a:dock W p B)(c:ℂ):dock W (c•p) (c•B):=by
 obtain ⟨r,w,g,h,e,x,hv,β⟩:= a.certified
 obtain ⟨R,k,h'⟩:= x.property
 let i : Fb s:= c • x.val; let w':Entry Y H s j false w:= ⟨i,R,k.smul c,h'⟩
 refine ⟨r,w,g,h,e,w',?_,?_⟩
 · change c • x.val.val= relocate _ _ _ (c • p.val); rw [hv]; exact (chime_scale ..).symm
 rw [←β]; exact entrance_scale Y H V s Q Qt j J e x w' c rfl
lemma voidX (h: W.lines s): dock W 0 0:=by
 obtain ⟨⟨c,a⟩,w,h⟩:=h
 have hc: c<w:= (stamp_lt M s _ _).mp (by rw [a,h]; exact W.thick)
 obtain ⟨n,(e:0<n),(t:c+(n:ℤ)=w)⟩:∃ n:ℕ,0<n∧ c+n=w:= ⟨(w-c).toNat,by omega,by omega⟩; subst w
 let f:=SlabMark.identity Y H s j false n
 let F:𝔅:= P₀ s f e
 have h':dock W 1 F:= ⟨c,n,a,h,e,f,(relocate_unit K j _).symm,rfl⟩
 have ht:=scaledX Y H V s Q Qt j J h' 0; rwa [zero_smul,zero_smul] at ht
lemma combineX {I:Type*}{F:I→ Marks (tent Y H) false}{Z:I→ driveAlgebra Y H V Q Qt j false J} (f:Finset I) (p: W.lines s)(t:∀i∈f,dock W (F i) (Z i)) : dock W (∑ i∈ f,F i) (∑ i∈ f,Z i):=by
 induction f using Finset.induction with
 | empty=> simp; exact voidX Y H V s Q Qt j J p
 | insert a f h ih=> simp_rw [Finset.sum_insert h]; exact plusX Y H V s Q Qt j J (t a (Finset.mem_insert_self ..)) (ih (fun i e=> t i (Finset.mem_insert_of_mem e)))
end tally
end Docked
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Docked.combineX
