import YM.SU5.Selected.Prag.Burn
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
open Tapestry CF.Pannier.Chancel.Attic.Cairn
open Spectral Spectral.Alps Germ.Alliance
open Fern Fern.Curtain Fern.Planet
open CF.Pannier.Chancel.Attic.Cairn.Giant CF.Pannier.Chancel.Attic.Cairn.Giant.Voice
namespace Mills
variable (s:ℕ)(j:Axis)(X:Giant){W:Window.Family} (F G:X.SpireBook (tent Y H) W) -- fix
local notation "R"=> X.Broad
variable (χ:CapCharacter Y H V Q Qc 3 false (C 3))
local notation "Θ"=> escort Y H V Q Qc 3 false (C 3)
local notation "B₁" v:max=> (Θ v (C v) χ)
variable (U: Birthplace Y H V Q Qc 3 false (C 3) (escort Y H V Q Qc 3 false (C 3) 3 (C 3) χ))
variable (x₀: Voice.Tonic X) {c:ℝ}(p: Planet.Saturn Y H V Q Qc C s X F G χ x₀ c)
local notation "ℓ"=> declination' Y H X
local notation "L"=> (3:Axis)
local notation "y₀"=> (Voice.ink X K F x₀).val
local notation "y₁"=> (Voice.burnish X K F G x₀).val
local notation "y₂"=> (Voice.flame X K F x₀).val
local notation "V₀"=> Summer.Polaris Y H V Q Qc L false (C L) U
local notation "Γ₀"=> Summer.terse Y H V Q Qc C L χ U
local notation "S"=> Summer.skyline Y H V Q Qc C L χ U
local notation "Σ"=> Diary.jetTime Y H V Q Qc L false (C L) U
local notation "κ"=> markedActor Y H V Q Qc L false (C L) U s
local notation "K₁" x:max=> Γ₀ (κ x)
local notation "Δ"=> whenly (timeMesh Λ) s 1
local notation "Ω"=> terse Y H V Q Qc C L χ U (vacuum Y H V Q Qc L false (C L) U)
local notation "Ξ"=> Actress.Label Y H L false
local notation "Φ"=> (V₀).Realm (look L)
local notation "F₊"=> (Tower.Field Y H s L 0 false)
local notation "ρ"=> Torrent.fare
local notation "τ"=> relocate (tent Y H) L
local notation "W'"=> Summer.worldShelf Y H V Q Qc C L χ U
-- prove both strict evolution & cast. actual Burn, not theoretical before anywhere.
local notation "ν" y:max z:max f:max=> Library Y H V Q Qc C L s χ U y z (declination' Y H X) y₀ f X.ascY X.ascX
local notation "M"=> X.ascY
local notation "M'"=> X.ascX
-- carry all members Calendar Choice from $Θ.Gen$. Need `Planet.Time poetic` before.This uses any chronological spine. Etc.
include V Q Qc C U p
lemma aboard:∃ (x y z:F₊) (A B: Ξ), Fierce Y H V Q Qc C s X F G χ U x₀ x y z A B:=by
 obtain ⟨x,y,h⟩:= p.packing 3 U; obtain ⟨x',z,t,t'⟩:= p.wealth U; have hE:x'=x:= Subtype.ext (t.born.1.trans h.born.1.symm); -- avoid subst cost
 have Xf:∀ i:Axis,Shelter Y H M i (declination' Y H X i)∧ ReachS Y H M' i (declination' Y H X i):= p.offsets; let B:=plotted Y H V Q Qc C L s χ U _ x y h Xf; let Z:= plotted Y H V Q Qc C L s χ U _ x z (hE ▸ t : Steams Y H V Q Qc 3 (C 3) (ℓ 3) s U x z (y₀) (y₂) M M') Xf; obtain ⟨A,B',hx⟩:= shelved Y H V Q Qc C L s χ U _ x y B
 exact ⟨x,y,z,A,B',earths Y H V Q Qc C s X F G χ U x₀ p x y z B Z hx⟩
omit U
-- Across axes. preserve no $0 repeated; records.Extra chronological law.$Agenda all points.Scope.Eury. preserve.
variable (U':Birthplace Y H V Q Qc j false (C j) (escort Y H V Q Qc 3 false (C 3) j (C j) χ))
local notation "P"=> (Polaris Y H V Q Qc j false (C j) U')
local notation "U₀" s:max=> ((Polaris Y H V Q Qc j false (C j) U').crew s).play
local notation "Ε₀"=> skyline Y H V Q Qc C j χ U'
local notation "Η₁"=> (P).Realm (look j)
local notation "μ"=> conduct Ε₀
local notation "w"=> worldShelf Y H V Q Qc C j χ U'
local notation "d"=> terse Y H V Q Qc C j χ U'
local notation "ϱ"=> vacuum Y H V Q Qc j false (C j) U'
local notation "γ"=> d ϱ
local notation "c₀"=> Actress.Label Y H j false
-- Can combine next into Story bind $F$ F parameters Horizon Title.P
include U'
lemma wages (u:LoneVac Y H V Q Qc j false (C j) U'):
 Urbana Ε₀ (γ) w (Arden Ε₀)∧ ∃ (x y:Tower.Field Y H s j 0 false)(A B:c₀), Manuscript Y H V Q Qc C j s χ U' x y A B (declination' Y H X) (y₀) (y₁) (M) (M'):=by
 obtain ⟨x,y,h⟩:= p.packing j U'; obtain ⟨A,B,p⟩:= shelved Y H V Q Qc C j s χ U' _ x y (plotted Y H V Q Qc C j s χ U' _ x y h p.offsets); exact ⟨utopia Y H V Q Qc C j χ U' u,x,y,A,B,p⟩
end Mills
end Summer
end YM.CF.Buffered.Afterglow.Tower.Selection
open YM.CF.Buffered.Afterglow.Tower.Selection.Summer.Mills
#print axioms aboard
#print axioms wages
#check @wages
#check @aboard
