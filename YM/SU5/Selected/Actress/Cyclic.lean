import YM.SU5.Selected.Actress.Basket
import YM.SU5.Selected.Actress.Dahl
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
variable (s:ℕ)
lemma receipt (x:Tower.Field Y H s j 0 r)(p:CovCover K x.val): ∃ (F:Label Y H j r),(η s) x=(κ₀ F) λ₀ ∧ F.count=s ∧ F.appraise.val.val=x.val:= by
 obtain ⟨w,F',h,rfl⟩:= eachField_enters Y H j r s x -- `p` name clash type witness
 let z:Label Y H j r:=⟨s,w,h,F',p⟩
 exact ⟨z,(service_u Y H V Q Qc j r C U s w F' h).symm,rfl,rfl⟩
-- (Separable already; density from wide Leg `Palate`.) elaborate r cases binder with «...» avoiding explosion. 
omit C U
private lemma canon (C:Arena Y H Q.circuit j 0 false)(χ:CapCharacter Y H V Q Qc j false C)(U':Birthplace Y H V Q Qc j false C χ) (x:Tower.Field Y H s j 0 false) : ∃ y:Tower.Field Y H s j 0 false, CovCover K y.val ∧ markedActor Y H V Q Qc j false C U' s x =markedActor Y H V Q Qc j false C U' s y:=by
 obtain ⟨w,e⟩:= Palate.tastes Y H V Q Qc j C s x; let y:= Palate.dash Y H j s w; have hp:CovCover K w.val:= ((purpose_ok ..).1 w.property).2 rfl; exact ⟨y,hp, (congrArg ((schematic Y H V Q Qc j false C χ).bloom U') e.symm)⟩ -- no prefix `.Blueprint`
include V Q Qc C U
lemma partialD (x:F₊ s) : ∃ y:F₊ s, CovCover K y.val ∧ (η s) x=(η s) y:= by -- maybe cost avoid if timeout
 cases r; · exact canon _ _ V Q Qc j s C χ U x
 exact ⟨x,((purpose_ok ..).1 x.property).2 rfl,rfl⟩
omit V C U Q Qc in
private lemma colloque (L:Hilbert)(F: ℕ → Type)(G: ∀ i,F i→ L)(t:Dense (⋃ (v : ℕ) (_ : 0 ≤ v), Set.range (G v)))(X₀:Type)(y:X₀→L)(f: ∀ i x, ∃ z:X₀, G i x=y z): DenseRange y:=by
 refine t.mono ?_; intro x h; obtain ⟨w,l⟩:=Set.mem_iUnion.mp h; obtain ⟨s,i,v⟩:= Set.mem_iUnion.mp l; obtain ⟨b,l⟩:=f w i; exact ⟨b,l.symm.trans v⟩
lemma podium : DenseRange (fun f:Label Y H j r=> κ₀ f λ₀):=by
 refine colloque U.H (fun i=> ↑(Tower.Field Y H i j 0 r)) (fun i x=>(η i) x) (born_dense Y H V Q Qc j r C U 0) (Label Y H j r) (fun f=> κ₀ f λ₀) ?_; intro w i; let u:= partialD Y H V Q Qc j r C U w i; let z:= receipt Y H V Q Qc j r C U w u.choose u.choose_spec.1; exact ⟨z.choose,u.choose_spec.2.trans z.choose_spec.1⟩
end Actress
end YM.CF.Buffered.Afterglow.Tower.Selection
open YM.CF.Buffered.Afterglow.Tower.Selection.Actress
#print axioms receipt
#print axioms podium

