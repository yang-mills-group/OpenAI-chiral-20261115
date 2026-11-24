import YM.SU5.Selected.Time.Diary
import YM.SU5.FiniteGaugeData.Tower.Sight
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
namespace Summer
local notation "Λ₀"=> timeMesh Λ
local notation "M₁"=> MeshClock.marks (timeMesh Λ)
local notation "V₁"=> travel_χ Y H V Q Qc j r C U
local notation "Β₀"=>leave Y H V Q Qc j r C U
open Germ
variable (v:Trans j)
include V Q Qc C U
private lemma som (s:ℕ)(x y:ℤ): ((V₁ s v x)).comp ((V₁) s v y) = V₁ s v (x+y):= by
    change V₁ s v x* V₁ s v y=_; exact (map_mul (Β₀) _ _).symm.trans (congrArg (Β₀) (corner_sum Y H V Q Qc j r C s v x y))
omit V Q Qc C U in
private lemma loom_cast (Λ:Preparation)(s t:ℕ)(i:ℤ):smill Λ s t (2*i)=2*MeshClock.castor (timeMesh Λ) s t i:=by unfold smill castor; change _=2*((Λ.R.L.val:ℤ)^(t-s)*i); ring
private lemma lowC (s t:ℕ)(q:s ≤ t)(i:ℤ): V₁ s v (2*i)=(V₁) t v (2* MeshClock.castor (timeMesh Λ) s t i):= by rw [←loom_cast]; exact congrArg (Β₀) (corner_finer Y H V Q Qc j r C s v t (2*i) q)
noncomputable def TerraX : Lunation (timeMesh Λ) U.H where
 nav s x:= V₁ s v (2*x)
 zero s:= (congrArg (V₁ s v) (mul_zero ..)).trans ((congrArg (Β₀) (corner_source Y H V Q Qc j r C s v)).trans ((Β₀).map_one))
 limited s i:= le_trans (reserve_norm Y H V Q Qc j r C U ((p₀ s) v (2*i))) (space_cost Y H V Q Qc j r C s v _) -- params test
 sums s i k:= (som Y H V Q Qc j r C U v s (2*i) (2*k)).trans (congrArg (V₁ s v) (mul_add ..).symm)
 changeover s t q i:= lowC Y H V Q Qc j r C U v s t q i

local notation "ρ₀" v:max=> TerraX Y H V Q Qc j r C U v
local notation "W₀" v:max=> Lunation.ship (ρ₀ v)
include V Q Qc C U
omit V U Q Qc C in
private lemma compatible (H:Hilbert)(D: Mesh)(L L': Lunation D H)(p:∀ s i j,Commute (L.nav s i) (L'.nav s j))(x y: marks D): Commute (L.ship x) (L'.ship y):= by obtain ⟨s,i,h⟩:= notch_exists D x; obtain ⟨t,k,h'⟩:=notch_exists D y; let m:=max s t; rw [←h,←h',←notch_up D s m (le_max_left ..), ←notch_up D t m (le_max_right ..), Lunation.navZ, Lunation.navZ]; exact p ..

private lemma sailX_commutes (w: Trans j)(x y:M₁) : Commute ((W₀ v) x) ((W₀ w) y):=by
 refine compatible _ _ (ρ₀ v) (ρ₀ w) (fun m i i' => ?_) x y;  exact (corner_cross Y H V Q Qc j r C m v w _ _).map (Β₀).toAlgHom.toRingHom
noncomputable def Polaris : Alliance (Trans j) (MeshClock.marks (timeMesh Λ)) U.H where
 crew v:= (ρ₀ v).plays
 cCom v w i k:= sailX_commutes Y H V Q Qc j r C U v w i k
local notation "θ"=> Polaris Y H V Q Qc j r C U
local notation "Θ" v:max=> ((θ).crew v).play
local notation "M₀"=> Diary.jetTime Y H V Q Qc j r C U
lemma source_z (s:ℕ)(x:ℤ) : (Θ v) (notch (timeMesh Λ) s x)=(V₁) s v (2*x):= Lunation.navZ (ρ₀ v) ..
lemma source_floor (x:M₁): (Θ v) x λ₀=λ₀:=by obtain ⟨s,i,rfl⟩:= notch_exists _ x; rw [source_z,travel_floor]
lemma source_heat (x:M₁)(t:ℝ≥0) : Commute ((Θ v) x) ((M₀).E t) :=by obtain ⟨s,i,rfl⟩:= notch_exists _ x; rw [source_z]; exact Diary.travel_drive Y H V Q Qc j r C U s v _ t
end Summer
end YM.CF.Buffered.Afterglow.Tower.Selection
open YM.CF.Buffered.Afterglow.Tower.Selection.Summer
#print axioms TerraX
#print axioms sailX_commutes
#print axioms source_z
#print axioms source_heat
#print axioms source_floor
