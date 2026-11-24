import YM.SU5.Selected.Prag.Tekt
import YM.SU5.Selected.Cairn.Radio
import YM.SU5.Selected.Time.Pace
import YM.SU5.Selected.Prag.Pr
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 320000
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
  (C : ∀ j:Axis, Arena Y H Q.circuit j 0 false)
namespace Summer
open Germ
variable (j v:Axis)
local notation "θ" j:max=>mirror K j 0
local notation "T" v:max x:max=> relocate K v x
local notation "Y₀"=> timeMesh Λ
local notation "R" s:max r:max k:max=> Raise Y H Q.circuit k 0 false s r
local notation "Ξ" s:max r:max=> stream Y H D s (r-s)
local notation "W" j:max u:max=> Tower.Field Y H u j 0 false
local notation "M₀" s:max r:max=> castor Y₀ s r
local notation "B₀"=> (Λ.R.L.val:ℤ)
variable (s:ℕ)
variable (χ:CapCharacter Y H V Q Qc 3 false (C 3)) -- primary. Can generalize to arbitrary meeting Leg.
variable (qv:v≠j)
local notation "Λ₀" v:max=> escort Y H V Q Qc 3 false (C 3) v (C v) χ
variable (F: Birthplace Y H V Q Qc j false (C j) (escort Y H V Q Qc 3 false (C 3) j (C j) χ))
variable (P: Birthplace Y H V Q Qc v false (C v) (escort Y H V Q Qc 3 false (C 3) v (C v) χ))
local notation "V₀"=> Summer.Polaris Y H V Q Qc j false (C j) F
local notation "U₀" a:max=> (((V₀).crew a).play)
local notation "Π" a:max F:max=> Diary.jetTime Y H V Q Qc a false (C a) F
local notation "ρ" v:max F:max=> markedActor Y H V Q Qc v false (C v) F
local notation "L" s:max=> (ρ j F) s
variable (z:ℤ) (c:Axis→ℤ){S D':Finset Cover}(x y:Tower.Field Y H s j 0 false)
open Tapestry
local notation "ℓ'" => ruler (tent Y H).B
abbrev Shelter (S:Finset Cover) (j:Axis) (z:ℤ) : Prop:= ∀ x∈ S,x j+(tent Y H).ℓ≤ ruler (tent Y H).B*z
abbrev ReachS (S: Finset Cover)(j:Axis)(z:ℤ): Prop:= ∀ x∈ S,ruler (tent Y H).B*z+ruler (tent Y H).B+(tent Y H).ℓ ≤ x j
namespace Sable
local notation "Θ"=> Shelter Y H
local notation "Θ'"=>ReachS Y H
local notation "Φ" t:max=> plow (tent Y H) j t
include qv
lemma across(p: Θ S v z)(b:ℤ): Θ (reflectedBox j b S) v z:=by
 intro x u; obtain ⟨x,u1,rfl⟩:= mem_image.mp u; rw [fling_move,if_neg (Ne.symm qv)]; exact p x u1
lemma sides(p: Θ S v z)(b:ℤ): Θ ((Φ b) S) v z:=by
 intro x u; obtain ⟨x,u1,rfl⟩:= plow_stays (K) j b S u; rw [moves,if_neg qv]; exact p x u1
lemma sails(p: Θ' S v z)(b:ℤ): Θ' ((Φ b) S) v z:=by
 intro x u; obtain ⟨x,u1,rfl⟩:=plow_stays K j b S u; rw [moves,if_neg qv]; exact p x u1
variable (p: InTest (tent Y H) false S false x.val)(t: InTest (tent Y H) false D' false y.val)
   (q:Neutral (tent Y H) x.val) (h:Neutral (tent Y H) y.val)
   (p':Shelter Y H S v z)(e:ReachS Y H D' v z)
include V Q Qc C
local notation "π"=> plow K v (-z)
local notation "E₁"=> (π) (reflectedBox j 0 S)
local notation "ζ"=>ruler (tent Y H).B*z
include p q t h p' e
lemma dues:∃ X Y':W v s, Refracts Y H s v j z 1 x y X Y':=by
 let f:= axial K j 0 p; let H':=(show Neutral K ((θ j) x.val) from covariant_flips K j 0 p.widen q); let Lx:= Fern.Curtain.wakes_x Y H V Q Qc v (C v) z s (across Y H j v qv z p' 0) e f t H' h; obtain ⟨X,Y',p,i,r,s'⟩:= Lx
 refine ⟨X,Y',?_, i⟩; rw [p]; let d:= flow_port K v (gaugeT (K) (-z)) f; exact Tower.reversal K v 0 (show InTest K false E₁ false ((T v (-z)) ((θ j) x.val)) from d)
omit qv p q t h p' e
open Fern Fern.Planet Fern.Curtain CF.Pannier.Chancel.Attic.Cairn CF.Pannier.Chancel.Attic.Cairn.Giant
local notation "κ"=> Refracts
-- print Wake propagation criterion. state width unchanged. Use axis j upper and v-plane after. 
local notation "Ψ"=> Poem Y H V Q Qc C j χ F
abbrev door (Λ:Preparation)(s:ℕ):ℝ:= bell (timeMesh Λ) s (1:ℤ)
omit V Q Qc C in
lemma pulsed (Λ:Preparation)(s:ℕ):0 < door Λ s:= Refracts.bell_p (timeMesh Λ) s 1 zero_lt_one -- include V Q? remove
local notation "δ"=> door Λ s
variable (f g:Family (tent Y H))(i0: Curtain.Steams Y H V Q Qc j (C j) (c j) s F x y f g S D')
    (pT: ∀ j:Axis,Shelter Y H S j (c j) ∧ ReachS Y H D' j (c j))
include χ F i0 pT
lemma nexx (v:Trans j): Ψ v.val (door Λ s) ((L s) x) ((L s) y):=by
 let v':= v.property; obtain ⟨u,V',hi⟩:= dues Y H V Q Qc C j v.val s v.property (c v.val) x y i0.born.2.1 i0.bore.2.1 i0.born.2.2 i0.bore.2.2 (across Y H j v.val v' _ (sides Y H j v.val v' _ (pT _).1 _) _) (sails Y H j v.val v' _ (pT _).2 _); exact ⟨_,_,_,_,_,_,_,hi,rfl,rfl,le_rfl⟩
end Sable
end Summer
end YM.CF.Buffered.Afterglow.Tower.Selection
open YM.CF.Buffered.Afterglow.Tower.Selection.Summer.Sable
#print axioms dues
#print axioms nexx -- keyword?
#print axioms pulsed
#check @nexx
