import YM.SU5.Selected.Prag.Living
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
local notation "Γ"=> marks (timeMesh Λ)
-- distance d carries arbitrary support margin.
local notation "Λs"=> (notch (timeMesh Λ) s)
local notation "Λv" i:max=> (U₀ (⟨v,qv⟩:Trans j)) i
local notation "L" s:max=> ((ρ j F) s)
def Poem (v:Axis)(d:ℝ)(x y:F.H.space): Prop := ∃ (s:ℕ)(z m:ℤ)(X Y': Tower.Field Y H s j 0 false)(U W':Tower.Field Y H s v 0 false),Refracts Y H s v j z m X Y' U W'∧ x=(L s) X∧y=(L s) Y'∧d≤ bell (timeMesh Λ) s m -- need parentheses.
namespace Poem
variable {d:ℝ}{x y : F.H.space} (p:Poem Y H V Q Qc C j χ F v d x y)
private lemma lateTime (M:Mesh)(d:ℕ)(t:ℝ≥0)(q:t∈ MeshClock.times M): ∃ s≥d,∃ i:ℕ, whenly M s i=t:=by obtain ⟨u,i,rfl⟩:= MeshClock.split _ q; exact ⟨_, le_max_left d u, _, matchR M u (max d u) i (le_max_right ..)⟩
include V Q Qc C F
local notation "F₀"=> Poem Y H V Q Qc C j χ F v
local notation "Λ₁" t:max=>((Π j F).E t)
local notation "ζ" t:max=> castor (timeMesh Λ) s t
private lemma arises (a t:ℕ)(p:a≤t)(X:W j a)(t₀:F.H)(e:t₀=(L a) X) : t₀= (L t) ((R a t j) p X):= e.trans (path Y H V Q Qc j false (C j) F a t p X).symm -- T conflicts
-- auxiliary generic avoids destruct time $e
omit V Q Qc C F in
private lemma smooth' {X: Type}(M:Mesh)(s:ℕ)(i:marks M)(f:marks M→X)(Q': X → Prop)(h:∀ t≥s,∀ z:ℤ,Q' (f (notch M t z))) : Q' (f i):=by obtain ⟨t,a,i,rfl⟩:= Refracts.notch_bigger M s i; exact h _ a _
omit V Q Qc C F in
private lemma smoothT' {X: Type}(M:Mesh)(s:ℕ)(i:ℝ≥0)(q:i∈ MeshClock.times M)(f:ℝ≥0→X)(Q': X → Prop)(h:∀ t≥s,∀ z:ℕ,Q' (f (whenly M t z))) : Q' (f i):=by obtain ⟨t,a,i,rfl⟩:= lateTime M s i q; exact h _ a _
omit V Q Qc C F in
private lemma stage_by {X:Type*}{P:X→ Prop}{x:X}(h:∃ x,P x)(g:∀ t,P t→ P x): P x:=by obtain ⟨y,h⟩:=h; exact g y h -- not used
-- exact Origin predicate all. avoid Lean kernel timeout destruct Born
include p
lemma heated (t:ℝ≥0)(q:t∈ MeshClock.times (timeMesh Λ))(b:v≠j) : F₀ d x ((Λ₁ t) y):=by
 obtain ⟨s,z,m,X,Y',u,v',h,h0,h1,h2⟩:=p
 refine smoothT' Y₀ s t q (fun t=> (Λ₁ t) y) (F₀ d x) ?_; intro t p i
 let S:= R s t j; let Y₁:= (R s t j) p Y' -- remove
 let z:= (h.escalates Y H V Q s t p).sailFuture Y H t (Ne.symm b) i
 let ε:= whenly (timeMesh Λ) t i; exact ⟨_,_,_,_,_,_,_,z,arises Y H V Q Qc C j χ F _ _ p X x h0,(congrArg (Λ₁ ε) (arises Y H V Q Qc C j χ F s t p _ y h1)).trans (Fern.Curtain.when_clock Y H V Q Qc j (C j) t F Y₁ i),h2.trans_eq (refineZ (timeMesh Λ) s t p m).symm⟩ -- signature y order?
lemma travel (w:Trans j)(q:(w:Axis)≠v)(a:Γ): F₀ d x ((U₀ w) a y):=by
 obtain ⟨s,z,m,X,Y',u,v',h,h0,h1,h2⟩:=p
 refine smooth' Y₀ s a (fun i=> (U₀ w) i y) (F₀ d x) ?_; intro t p i
 let z:=(h.escalates Y H V Q s t p).sailBoth Y H t w.val w.property q i; let Y₁:= (R s t j) p Y'; let U':= (U₀ w) (notch (timeMesh Λ) t i); have hz':U' ((L t) Y₁)=(L t) (sail Y H t j 0 false w.val w.property (2*i) Y₁):= (congrArg (fun i:F.H.Op=>i ((L t) Y₁)) (source_z Y H V Q Qc j false (C j) F w t i)).trans (travel_step Y H V Q Qc j false (C j) F t w _ _)
 exact ⟨_,_,_,_,_,_,_,z,arises Y H V Q Qc C j χ F _ _ p X x h0,(congrArg U' (arises Y H V Q Qc C j χ F s t p _ y h1)).trans hz',h2.trans_eq (refineZ (timeMesh Λ) s t p m).symm⟩
-- window independent, no curried bands; may generalize semi p_{3} direction as t≥0. Need separate cross_vectorP.
include qv
lemma paysFront (c:Γ)(q : -d < (c:ℝ)) : ContinuousAt (fun a:Γ=> inner ℂ x ((Λv a) y)) c:=by
 let P':= Classical.choice (realizeRoom Y H V Q Qc v false (C v) (Λ₀ v))
 obtain ⟨s,z,m,X,Y',u,v',h,p',v'',t⟩:=p
 have hr:= show 0 < (c:ℝ)+bell (timeMesh Λ) s m from (by linarith only [t,q]); -- prefer congr avoiding p rewrite.
 exact p'.symm ▸ v''.symm ▸ Refracts.aliveC Y H V Q Qc C j v s χ qv F P' h c hr
end Poem
end Summer
end YM.CF.Buffered.Afterglow.Tower.Selection
open YM.CF.Buffered.Afterglow.Tower.Selection.Summer.Poem
#print axioms heated
#print axioms travel
#print axioms paysFront
#check @paysFront
