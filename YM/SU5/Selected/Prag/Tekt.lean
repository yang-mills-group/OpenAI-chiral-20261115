import YM.SU5.Selected.Prag.Silhouette
import YM.SU5.Selected.Prag.Riding
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
-- projection chosen after phase/s etc. needs identification of powers. 
noncomputable def skyline:= (V₀).Frog (daylight Y₀) (Π j F) (source_heat Y H V Q Qc j false (C j) F)
local notation "R₀"=> (V₀).Realm (look j)
local notation "X₀"=> skyline Y H V Q Qc C j χ F
local notation "Λ'"=> Alliance.pours j
local notation "σ" p:max=> ((Π j F).E p)
local notation "Γ"=> marks (timeMesh Λ)
local notation "Γ₀"=> ((V₀).raw (look j))
abbrev terse := (V₀).prism
local notation "ψ"=> terse Y H V Q Qc C j χ F
local notation "τ"=> (X₀).U
open Spectral Spectral.Alps
local notation "E₂"=> (X₀).E
variable (d:ℝ) (x y:F.H.space) (p:∀ v':Trans j, Poem Y H V Q Qc C j χ F v'.val d x y)
include V Q Qc C F p
variable (f:Trans j→ marks (timeMesh Λ))(w:∀ i:Trans j,-d < ((f i):ℝ))
local notation "φ" p:max=> (Alliance.pours j (fun i:Trans j=> (p i:ℝ)))
include w
lemma limes (t:ℝ≥0) : inner ℂ (ψ x) (τ (φ f) (E₂ t (ψ y)))=inner ℂ x (Γ₀ f ((σ t) y)):=by
 let Vx(i:Trans j):= Poem Y H V Q Qc C j χ F i.val d -- fix shadow
 refine (Alliance.fortunes V₀ (daylight Y₀) (Π j F) (source_heat Y H V Q Qc j false (C j) F) (fills Y₀) Vx f x y p (fun i t h y p' => Poem.heated Y H V Q Qc C j i.val χ F p' t h i.property) ?_ ?_ t)
 · intro i k h c y p'; exact Poem.travel Y H V Q Qc C j (i:Axis) χ F p' k (fun i=> h (Subtype.ext i)) c -- order
 intro i y p'; exact Poem.paysFront Y H V Q Qc C j i.val χ i.property F p' (f i) (‹∀ i: Trans j, -d < (f i:ℝ)› i)
local notation "S₀"=> balcony X₀
local notation "S₁"=> balcony (Π j F)
lemma limes_high (t:ℂ) (z:0 ≤ t.im): inner ℂ (ψ x) (τ (φ f) ((S₀) t (ψ y)))= inner ℂ x (Γ₀ f ((S₁) t y)):= Alliance.rideOut _ (daylight Y₀) _ _ _ _ _ (limes Y H V Q Qc C j χ F d x y p f w) t z
local notation "Ξ₁"=> whenly (timeMesh Λ)
-- t real beyond seam clock.Water. use E stone. supply height probability Mark-H.Saved unit.
omit w
local notation "ρ₀" x:max=> ψ x
omit p F V Q Qc C in
private lemma empty_exposure {H:Hilbert}{j:Axis}(S:OS.Semigroup H j): ∀ (x:H), S.U (Alliance.pours j 0) x=x:=by
 intro x; have hv:Alliance.pours j 0=0:=by
    apply Subtype.ext; ext b; change (if h:b≠j then (0:ℝ) else 0) = _; split_ifs<;> rfl
 rw [hv,S.uZero]; rfl
lemma loveheat (h:0<d)(t:ℝ≥0):inner ℂ (ψ x) ((X₀).E t (ψ y))=inner ℂ x ((Π j F).E t y):=by
 let Ω := limes Y H V Q Qc C j χ F d x y p 0 (fun _=> show -d<(0:ℝ) from neg_neg_of_pos h) t; let V':=(V₀); let Y':= V'.Realm (look j); let i:(Trans j→ Γ):=0; have ht:∀ x: R₀,τ (φ i) x=x:=by
    apply empty_exposure (X₀) -- define generic
 exact ((congrArg (inner ℂ (ψ x)) (ht ((X₀).E t (ψ y)))).symm).trans (Ω.trans (congrArg (inner ℂ x) (DFunLike.congr_fun (Alliance.raw_zero V' (look j)) ((Π j F).E t y))))
end Summer
end YM.CF.Buffered.Afterglow.Tower.Selection
open YM.CF.Buffered.Afterglow.Tower.Selection.Summer
#print axioms limes
#print axioms limes_high
#print axioms loveheat
#check @limes_high
