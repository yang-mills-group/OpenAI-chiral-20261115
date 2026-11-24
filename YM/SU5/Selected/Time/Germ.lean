import YM.SU5.Selected.Twirl.Lull
import YM.SU5.Selected.Cor.Coterie
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Selection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
open RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
open scoped InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock
open Vacancy

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b)
  (Qc : Clipped Y H (i ∘ a) (k ∘ b))
  (j : Axis) (C : Arena Y H Q.circuit j 0 false)
local notation "R" => Aurora Y H V Q j false C
local notation "A" => Ark.Ht Y H Q.circuit j 0 false C
local notation "W" => floorV Y H Q.circuit j 0 false C
local notation "F₊" n:max => Tower.Field Y H n j 0 false
local notation "φ" n:max => actor Y H n Q.circuit j 0 false C
local notation "Ω" => seat0 Y H V Q j false C
attribute [local instance] opCStarAlgebra
open CF.Pannier.Chancel Tapestry Papal
open CF.Pannier.Chancel.Lantern CF.Pannier.Chancel.Lantern.Bulb CF.Pannier.Chancel.Lantern.Bulb.Mezz
-- use C : Arena false only (assembly neutral). 
local notation "Ch"=> CapCharacter Y H V Q Qc j false C
local notation "Test"=> Vacancy.observable (tent Y H) false
local notation "readχ"=> phaseRead Y H V Q Qc j C
local notation "F₀" i:max=> cap Y H V i Q Qc j false C
local notation "N" i:max=> liftCap Y H V Q Qc j false C i
namespace Fern
-- recovery linear maps. Bool r. decide. c+ lab.
variable (s n:ℕ)
local notation "N'"=> n
variable {S T:Finset Cover}{k0 d:ℝ} {f g:Family (tent Y H)}
namespace Curtain
open Grant
local notation "μ"=> reserve Λ l
local notation "U" i:max=> volumeAround Λ l i
local notation "P" v:max=> plow K 3 v
local notation "ϕ" i:max=> relocate K 3 i
local notation "Θ" i:max=> E (s+i)
local notation "p₀"=> readχ
-- carry Curtain.Corr labels to resolution.s+t with space, effective all n+, precise
structure Gala (S T: Finset Cover)(f g: Family (tent Y H))(c:ℝ): Prop where
 fired: InTest K false S false f ∧ Neutral K f
 renteds : InTest K false T false g∧Neutral K g
 layout : GalleryG Λ l s c (grate Λ l s) S T
 lifeT (χ: CapCharacter Y H V Q Qc j false C)(n:ℕ):
    let x:=stream Y H D s n f; let y:=stream Y H D s n g
    x∈ observ K (volumeAround Λ l n S) true ∧ y∈ observ K (volumeAround Λ l n T) true ∧ stream Y H D s n (f*g)= x*y ∧ E (s+n) (x*y)= E s (f*g) ∧ phaseRead Y H V Q Qc j C χ (s+n) (x*y) = phaseRead Y H V Q Qc j C χ s (f*g)
include V Q Qc C
lemma celebrate (t:InTest K false S false f)(e: Neutral K f) (l₀:InTest K false T false g)(h:Neutral K g)(c:ℝ)(q:GalleryG Λ l s c (grate Λ l s) S T): Gala Y H V Q Qc j C s S T f g c:=by
 let i:= gentle Y H t.widen; let p:= gentle Y H l₀.widen; let u:= composed false i p; let a:=C; refine ⟨⟨t,e⟩,⟨l₀,h⟩,q,?_⟩; intro χ n; let d:= upward Y H Q false u s n; let x:=stream Y H D s n f; let y:=stream Y H D s n g; have hp : d.val=x*y:=woven_product _ _ Q.circuit _ n t.widen l₀.widen q.detached; have he:(N (s+n)) d=(N s) u:= read_refines Y H V Q Qc j false C s n u
 refine ⟨Tower.chroma Y H Q.circuit s n ((obs_in ..).2 ⟨t.widen,e⟩), Tower.chroma Y H Q.circuit s n ((obs_in ..).2 ⟨l₀.widen,h⟩), hp, ?_,?_⟩
 · change E (s+n) (x*y)= E s u.val; rw [←hp, ←inspected Y H V s Q Qc j false C (F:=u), ←inspected Y H V (s+n) Q Qc j false C (F:=d)] -- specify args
   rw [show (F₀ (s+n)) d=(F₀ s) u from congrArg Subtype.val he]
 change phaseRead Y H V Q Qc j C χ (s+n) (x*y)= phaseRead Y H V Q Qc j C χ s u.val; rw [←hp,phase_read,phase_read,he]
omit V Q Qc C
variable (Z:Mezz)(d₀: Z.BlockDay)
variable {x:ℝ}(t:addgap (tent Y H) ≤ Z.ℓ.val) (h:printedHere Λ l s Z.Broad (cabin x))(v:Bool)
local notation "L" b:max=> quarry Z K d₀ b
local notation "R1" b:max=> quay Z K d₀ b
local notation "ρ" b:max=> boundaryT Z K d₀ b
local notation "HH" b:max=> (ruler (K).B)* boundaryT Z K d₀ b
include t
lemma clockLeft (i:Cover)(p:i∈L v): i 3 + (K).ℓ ≤ HH v:=by have ht:= (show i 3 + 10* (Z.ℓ.val:ℤ) ≤ HH v from (mem_filter.mp p).2); unfold addgap stepgap at t; omega
lemma clockRight (i:Cover)(p:i∈R1 v): HH v+ruler (K).B+(K).ℓ≤ i 3 := by
 have h':=(show HH v+10*(Z.ℓ.val:ℤ)≤ i 3 from (mem_filter.mp p).2); unfold addgap stepgap at t; have he:ruler (K).B+(K).ℓ ≤ 10*(Z.ℓ.val:ℤ):= by unfold ruler; omega
 omega
lemma longetic (x y:Cover) (hx:x∈ L v)(hy:y∈ R1 v): (3:ℤ)*μ≤ y 3-x 3:= by
 have hh:=(show x 3+10*(Z.ℓ.val:ℤ)≤ HH v from (mem_filter.mp hx).2); have he:=(show HH v+10*(Z.ℓ.val:ℤ)≤ y 3 from (mem_filter.mp hy).2); have hp: μ≤Z.ℓ.val:= by refine le_trans ?_ t; unfold addgap stepgap; change (reserve Λ l) ≤ 2*((reserve Λ l)+_); omega
 omega
include h
lemma fancy_b : GalleryG Λ l s x (grate Λ l s) (L v) (R1 v):= shapeK Λ l s h (filter_subset ..) (filter_subset ..) (fun x g y v' =>by have ht:= longetic Y H Z d₀ t v _ _ g v'; omega)
omit h
lemma fancy_n : ∃ c:ℕ, GalleryG Λ l s c (grate Λ l s) (L v) ((P (n:ℤ)) (R1 v)):=by
 let Q':=(P (n:ℤ)) (R1 v); obtain ⟨p,c⟩:= (fundCabin Λ l s ((L v)∪Q')).exists; refine ⟨p,shapeK Λ l s c subset_union_left subset_union_right ?_⟩; intro i h' v₀ he; obtain ⟨y,g',rfl⟩:= plow_stays K 3 _ _ he; have h':=(longetic Y H Z d₀ t v i y h' g'); rw [moves,if_pos rfl]; have hn:0 ≤ (ruler (K).B)*(n:ℤ):=mul_nonneg (ruler_gene _).le (by positivity); omega

end Curtain
end Fern
end YM.CF.Buffered.Afterglow.Tower.Selection
open YM.CF.Buffered.Afterglow.Tower.Selection.Fern.Curtain
#print axioms fancy_b
#print axioms fancy_n
#print axioms Gala
#print axioms celebrate
#print axioms clockLeft
#print axioms clockRight
