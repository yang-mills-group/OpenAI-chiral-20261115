import YM.SU5.Selected.Actress.Basket
import YM.SU5.Selected.Actress.Basket
import YM.SU5.Selected.Actress.Moves
import YM.SU5.Selected.Euro.Palate
import YM.SU5.Selected.Time.Prom
/-! Observables CP6. Select & reconstruct continuous **physical time**, no spectator semantics. Includes concurrence test of spatial mesh motions. Test spacings as Vanguard. ( `monoAxis U` has dummy spatial even though real mesh is present; `stay` keeps only relevant time facts expressed with spectralP pushed to ℝ of THAT operator system). -/
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
  (j : Axis) (r : Bool) (C : Arena Y H Q.circuit j 0 r)
local notation "R" => Aurora Y H V Q j r C
local notation "A" => Ark.Ht Y H Q.circuit j 0 r C
local notation "W" => floorV Y H Q.circuit j 0 r C
local notation "F₊" n:max => Tower.Field Y H n j 0 r
local notation "φ" n:max => actor Y H n Q.circuit j 0 r C
local notation "Ω" => seat0 Y H V Q j r C
local notation "π₀" => (R).orthogonalProjectionOnto
local notation "N" n:max => cap Y H V n Q Qc j r C
local notation "Test" => Vacancy.observable (tent Y H) r
local notation "Lab" => Beacon (tent Y H) r

local notation "B" => groundAlgebra Y H V Q Qc j r C
local notation "Β" => pruner Y H V Q Qc j r C
local notation "M" s:max => liftCap Y H V Q Qc j r C s
local notation "uℋ" => basisRoom Y H V Q j r C
local notation "U₀" s:max => timePruner Y H V Q Qc j r C s
local notation "p₀" s:max => spacePruner Y H V Q Qc j r C s
local notation "τ" s:max => tick Y H s j 0 r
local notation "ρ" s:max => ripple Y H V s Q.circuit j 0 r C
local notation "P₀" s:max => stretches Y H V Q Qc j r C s
variable {χ : CapCharacter Y H V Q Qc j r C} (U : Birthplace Y H V Q Qc j r C χ)
local notation "λ₀" => vacuum Y H V Q Qc j r C U
local notation "η" s:max => markedActor Y H V Q Qc j r C U s
local notation "η₀" => leave Y H V Q Qc j r C U
open Companies
namespace Actress
open Tapestry
open Spectral Spectral.Alps
local notation "J"=> Diary.jetTime Y H V Q Qc j r C U
local notation "Σ₀" => Label Y H j r
local notation "κ₀"=> Label.money Y H V Q Qc j r C U
local notation "Vγ"=> incubate Y H V Q Qc j r C U
local notation "ψ"=> travel_χ Y H V Q Qc j r C U
variable (F:Label Y H j r)
include V Q Qc C U
section space
variable (s:ℕ)(i:Trans j)(x:ℤ)
lemma spatial_sum(w:ℤ): ψ s i x*ψ s i w=ψ s i (x+w):= (map_mul η₀ _ _).symm.trans (congrArg η₀ (corner_sum Y H V Q Qc j r C s i x w))
lemma spatial_source: ψ s i 0=(1: U.H.Op):= (congrArg η₀ (corner_source Y H V Q Qc j r C s i)).trans (map_one _)
lemma spatial_star : star (ψ s i x) = ψ s i (-x):= (map_star η₀ _).symm.trans (congrArg η₀ (corner_adj Y H V Q Qc j r C s i x))
local notation "yP" t:max=> ψ s i t
omit V Q Qc C U in
private lemma starReal (T:Hilbert)(F:ℤ → T.Op)(p:∀ i j:ℤ,F i*F j=F (i+j))(h: F 0=1)(v: ∀ i,F (-i)=star (F i))(i:ℤ): F i ∈ unitary T.Op:= ⟨by rw [←v,p,neg_add_cancel,h],by rw [←v,p,add_neg_cancel,h]⟩
noncomputable def spatialU: unitary U.H.Op:=by
 let T:U.H.Op:= ψ s i x
 exact ⟨T, starReal U.H (travel_χ Y H V Q Qc j r C U s i) (spatial_sum Y H V Q Qc j r C U s i) (spatial_source Y H V Q Qc j r C U s i) (fun t=> (spatial_star Y H V Q Qc j r C U s i t).symm) x ⟩
-- upstairs any time, lift to ANY higher then carry one smaller rung. use full u shells.
private lemma blownN (w:ℕ)(f:Entry Y H s j r w)(h:CovCover K f.val.val): CovCover K (blown Y H j r s i.val i.property x w f).val.val:= chime_cov K i.val _ (test_entry Y H s j r f).paid.choose_spec h -- grid not equal? syntax
lemma movesF (t:ℕ)(p:s≤t)(q:F.count≤ t): ∃ (F':Label Y H j r), ψ s i x * κ₀ F=κ₀ F' * ψ s i x:=by
 let n':= F.extent Y H j r t; let v:= F.finery Y H Q j r t q; let w:= smill Λ s t x; let Y':= blown Y H j r t i.val i.property w n' v; have h : 0<n':= Nat.mul_pos (pow_pos Λ.R.L.property _) F.paid; have hv: CovCover K Y'.val.val:= blownN Y H V Q Qc j r C U t i w n' v (Label.up_neutral Y H V Q Qc j r C U t F q);
 let F':Label Y H j r:= ⟨t,n',h,Y',hv⟩; let A':= incubate Y H V Q Qc j r C U t n' v h; let θ':= spatialU Y H V Q Qc j r C U t i w; let B':= (κ₀ F'); have he: θ'.val * A'= B'*θ'.val:= sideways_commit Y H V Q Qc j r C U t n' v h i w
 refine ⟨F',?_⟩
 have uu: ψ s i x = ψ t i w:= congrArg η₀ (corner_finer Y H V Q Qc j r C s i t x p); have ut : κ₀ F = A' := Label.compatible Y H V Q Qc j r C U t F q
 exact (congrArg₂ (· * ·) uu ut).trans (he.trans (congrArg (κ₀ F' * ·) uu.symm))
end space
end Actress
end YM.CF.Buffered.Afterglow.Tower.Selection
open YM.CF.Buffered.Afterglow.Tower.Selection.Actress
#print axioms movesF
#print axioms spatialU
