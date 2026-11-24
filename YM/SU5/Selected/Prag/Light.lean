import YM.SU5.Selected.Prag.Refract
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
namespace Refracts
variable {z m:ℤ}{x y: Tower.Field Y H s j 0 false}{X Y': Tower.Field Y H s v 0 false}
   (u:Refracts Y H s v j z m x y X Y')
local notation "Ψ"=> (notch (timeMesh Λ) s)
local notation "Δ" x:max=> ((U₀ (⟨v,qv⟩:Trans j)) x)
local notation "δ" t:max w:max=> whenly (timeMesh Λ) t w
local notation "ω" j:max x:max a:max=> (bornTest Y H j false s x a)
local notation "Λ'" x:max => ((Π v P).E x)
local notation "L" F:max s:max=> (ρ j F) s
local notation "Ξv" F:max s:max=> (ρ v F) s
include qv u
private lemma slideMark (i:ℤ)(a:ℕ)(h:i+m=(a:ℤ)): ω v X (tick Y H s v 0 false (2*a) Y')=moved Y H v false (-z) (ω j x (sail Y H s j 0 false v qv (2*i) y)):=by
 apply Subtype.ext; change (θ v) X.val*(tick _ _ _ _ _ _ (2*a) Y').val=(T v (-z)) ((θ j) x.val*(T v i) y.val);
 have hp: i+m=(a:ℤ):=h; rw [timed_apply Y H v false,u.future,u.early, relocate_mul,relocate_sums K v _ _ (field_test Y H s j 0 false y), relocate_sums K v _ _ (field_test Y H s j 0 false y), show (a:ℤ) +(-z -m) = -z+i from (by omega)] -- syntax
include V Q Qc C F P
lemma ICross (i:ℤ)(a:ℕ)(h:i+m=(a:ℤ)): inner ℂ ((L F s) x) ((Δ (Ψ i)) ((L F s) y)) = inner ℂ ((Ξv P s) X) ((Λ' (δ s a)) ((Ξv P s) Y')):=by
 let Y₁:= sail Y H s j 0 false v qv (2*i) y; let Y₂:= tick Y H s v 0 false (2*a) Y'; have h₁:(Δ (Ψ i)) ((L F s) y) = (L F s) Y₁:= (congrArg (fun i:F.H.Op=> i ((L F s) y)) (Summer.source_z Y H V Q Qc j false (C j) F (⟨v,qv⟩:Trans j) s i)).trans (travel_step Y H V Q Qc j false (C j) F s ⟨v,qv⟩ (2*i) y); have h₂:(Λ' (δ s a)) ((Ξv P s) Y')=(Ξv P s) Y₂:= Fern.Curtain.when_clock Y H V Q Qc v (C v) s P Y' a
 have hv(v:Axis)(i: Vacancy.observable K false): (marked Y H V Q Qc v false (C v) (Λ₀ v)) s i= marked Y H V Q Qc 3 false (C 3) χ s i := unchanged Y H V Q Qc 3 false (C 3) v (C v) χ s i
 let U:= liftCap Y H V Q Qc v false (C v) s; have hz: U (ω v X Y₂)= U (ω j x Y₁):=(congrArg U (slideMark Y H j v s qv u i a h)).trans (Fern.Guild.move_cap Y H V Q Qc v (C v) (-z) s _); let τ:=ω j x Y₁; refine (congrArg (inner ℂ ((L F s) x)) h₁).trans ?_; symm; exact (congrArg (inner ℂ ((Ξv P s) X)) h₂).trans ((affirmation Y H V Q Qc v false (C v) P s X Y₂).trans ((congrArg (Λ₀ v) hz).trans ((hv v τ).trans ((hv j τ).symm.trans (affirmation Y H V Q Qc j false (C j) F s x Y₁).symm))))
end Refracts
end Summer
end YM.CF.Buffered.Afterglow.Tower.Selection
open YM.CF.Buffered.Afterglow.Tower.Selection.Summer.Refracts
#print axioms slideMark
#print axioms ICross
#check @ICross
