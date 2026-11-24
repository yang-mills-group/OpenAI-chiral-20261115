import YM.SU5.Selected.Prag.Elie
import YM.SU5.Selected.Prag.Trove
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
---- Horizon & state of continuation restricted. Preserved labels (Altar). 
local notation "ζ"=> skyline Y H V Q Qc C j χ F
local notation "ξ"=> (Π j F)
open Spectral Spectral.Alps Germ.Alliance
local notation "Β"=> Actress.Label Y H j false
local notation "ν"=> Actress.Label.money Y H V Q Qc j false (C j) F
local notation "Φ"=> (V₀).Realm (look j)
local notation "w"=> vacuum Y H V Q Qc j false (C j) F
local notation "d"=> terse Y H V Q Qc C j χ F
local notation "S"=> worldShelf Y H V Q Qc C j χ F
local notation "Ω"=> terse Y H V Q Qc C j χ F w
local notation "V₁"=> (daylight (timeMesh Λ))
local notation "μ"=> source_heat Y H V Q Qc j false (C j) F
local notation "λ₀"=> Alliance.Arden ζ
local notation "Γ"=> MeshClock.marks (timeMesh Λ)
namespace Mills
include V Q Qc C F
abbrev slabC (s t:ℕ)(p:0<t):Β:=⟨s,t,p,SlabMark.identity Y H s j false t,(covariant_one K)⟩
local notation "κ" u:max v:max p:max => slabC Y H j u v p
local notation "Β₀" s:max t:max => whenly (timeMesh Λ) s t
omit V Q Qc C F in
private lemma press {X:Hilbert}{a:Axis}{Γ':AddSubgroup ℝ}(P:Alliance (Trans a) Γ' X)(dp:Dense (Γ':Set ℝ))(F:OS.Semigroup X a)(q: ∀ i v t, Commute ((P.crew i).play v) (F.E t))(c:X.Op)(t:ℝ≥0)(e:c=F.E t): Alliance.bead P c=(Frog P dp F q).E t:=by
 ext1 x; rw [e]; change descendH P (F.E t (arise P x)) = _; rw [←Alliance.pulseR P dp F q, Alliance.descends_d]
lemma sunset (t:ℕ)(p:0<t): S (κ s t p,0)=(ζ).E (Β₀ s t):=by
 let c:= Β₀ s t; let v:= V₀; let i:= κ s t p; exact (powder Y H V Q Qc C j χ F i).trans (press v V₁ ξ μ (ν i) c (Actress.roof_id Y H V Q Qc j false (C j) F s t p))
omit V Q Qc C F in
private lemma secShift (H:Hilbert){a:Axis}(F:OS.Semigroup H a)(k:OS.Cross a)(q t:ℝ≥0)(b:ℝ) : Alps.conduct F b (Alliance.Vista F k (F.E t))=F.E t:=by
 have he: F.U k * F.E t= F.E t * F.U k:=(F.independent t k).symm; have h':F.edge b *F.E t= F.E t*F.edge b:=(F.eitherE t b).symm; rw [Alliance.swapper F k _ _ he,Alps.system,h',mul_assoc]; rw [show F.edge b*F.edge (-b)=1 from (F.send ..).trans ((congrArg F.edge (add_neg_cancel b)).trans F.birth),mul_one] -- name e.
lemma timeless (t:ℕ)(p:0<t)(b:ℝ)(a:OS.Cross j) : Alps.conduct ζ b (S (κ s t p, a))= (ζ).E (Β₀ s t):=by
 let F':= κ s t p; let i:=Β₀ s t
 have h': S (F',a)= Alliance.Vista ζ a ((ζ).E i):= (constellation Y H V Q Qc C j χ F F' a).symm.trans (congrArg (Alliance.Vista ζ a) (sunset Y H V Q Qc C j s χ F t p)) -- constellation args order
 exact (congrArg (Alps.conduct ζ b) h').trans (secShift (Φ) ζ a 0 i b)
end Mills
end Summer
end YM.CF.Buffered.Afterglow.Tower.Selection
open YM.CF.Buffered.Afterglow.Tower.Selection.Summer.Mills
#print axioms timeless
#print axioms sunset
#print axioms slabC
