import YM.SU5.Selected.Actress.Basket
import YM.SU5.Selected.Actress.Scarves
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
local notation "Σ₀"=> Actress.Label Y H j r
local notation "Pη"=> Label.money Y H V Q Qc j r C U
local notation "Z" x:max=> balcony J x
-- Chronometry. at resolution evaluate in chronological order (earliest on left). Points are *empty separation* in gaps, **in addition** to widths! n shifts>=0 times. spine recursively. Applicability $u: ∀ cal-i rank ≤ s$ (finite labels use subtype or Fin).
open YM.Boundary (Distn Probe)
variable {κ:Type*} [Fintype κ] [DecidableEq κ](F:κ→Label Y H j r) (L:List κ) (s:ℕ)
-- trace accounting crew. with value vacuum even if ground degenerate; positive (A) on operators.
noncomputable def Quantity {κ:Type*} (F:κ→Label Y H j r)(L:List κ)(x:κ→ℂ):= inner ℂ λ₀ ((onArc Y H V Q Qc j r C U F L x) λ₀) -- inspect l binder
local notation "γ" L:max=> Quantity Y H V Q Qc j r C U F L
local notation "K₀" L:max=> onArc Y H V Q Qc j r C U F L
local notation "E₀"=> marked Y H V Q Qc j r C χ
local notation "Z₁" i:max z:max v:max=> lode Y H Q j r i F v z L -- parens ℝ
local notation "T₀" s:max=> whenly (timeMesh Λ) s
local notation "π" s:max z:max=> Spectral.Alps.imaginary (fun i:κ=> (T₀ s) (z i)) -- name collision Real.pi; specify PIB
include V Q Qc C U
lemma quota : Continuous (γ L) ∧ AnalyticOnNhd ℂ (γ L) (waist κ):=by
 let f:= trip J (Pη ∘ F) L; have h: (γ L)= fun i=> inner ℂ λ₀ (f i λ₀) := rfl -- maybe expensive unfold
 let p : AnalyticOnNhd ℂ f (waist κ):= fun z t=> flight_yes J _ _ _ (fun i w=> t i)
 let b : U.H.Op →L[ℂ] ℂ:= (innerSL ℂ λ₀).comp (ContinuousLinearMap.apply ℂ U.H.space λ₀)
 exact ⟨(continuous_const.inner (flight_cont J λ₀ _ _)), fun x z=> by
    apply show AnalyticAt ℂ (fun x=> b (f x)) _ from (b.analyticAt _).comp (p x z)⟩
lemma amountQuota (p:∀ i,(F i).count ≤ s)(z:κ→ℕ) : (γ L) (π s z)=E₀ s (toTest Y H j r s (Z₁ s z p)):= expectancy Y H V Q Qc j r C U s F p z L
-- uniqueness: one-ray analytic fact. convert requirement at ANY rank >=s*. Price doesn't have to be same V replica cut? built he moments by Eχ.
lemma decisive (i:ℕ)(f:(κ→ℂ)→ℂ) (hf:ContinuousOn f (ivory κ))(p:AnalyticOnNhd ℂ f (waist κ)) (z:∀ s:ℕ,∀ p':i ≤ s,∀ p:∀ i,(F i).count ≤ s,∀ z:κ→ℕ, f (π s z)=E₀ s (toTest Y H j r s (Z₁ s z p))) : Set.EqOn f (γ L) (ivory κ):=by
 refine tropical f (γ L) hf (quota Y H V Q Qc j r C U F L).1.continuousOn p (quota Y H V Q Qc j r C U F L).2 (fun x=>?_)
 let MM:= timeMesh Λ; let u(s:ℕ)(i:κ) := ⌊ x i / MeshClock.mill  MM s⌋₊+1; let ρq(s:ℕ):= π s (u s)
 have he : Tendsto (fun i=>ρq i) atTop (nhdsWithin (imaginary x) (ivory κ)):=by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_pi_nhds.mpr (fun i=>?_),Eventually.of_forall (fun z=>waist_img (fun i:κ=> whenly MM z (u z i)))⟩; let HQ(t:ℝ≥0):ℂ:= (↑(t:ℝ):ℂ) * Complex.I; exact ((show Continuous HQ from (Complex.continuous_ofReal.comp continuous_subtype_val).mul_const _).continuousAt.tendsto).comp (shade  MM (x i))
 apply tendsto_nhds_unique_of_eventuallyEq ((hf (imaginary x) (waist_img x)).tendsto.comp he) (((quota Y H V Q Qc j r C U F L).1.tendsto _).comp (he.mono_right nhdsWithin_le_nhds)); apply Filter.Eventually.mono ((eventually_ge_atTop i).and (eventually_all.mpr (fun i=> eventually_ge_atTop (F i).count))) (fun t q=> (z t q.1 q.2 (u t)).trans (amountQuota Y H V Q Qc j r C U F L t q.2 (u t)).symm)
-- distn explicit proposition
noncomputable def stackPrice:= temporalJoint (J) λ₀ λ₀ (fun i=> Pη (F i)) L
-- Spectral support statements along each gap real only sages. chronological logs apply at t*** all spatial positions. use `circuit` + gauge q. 
lemma window (t:ℝ)(x:κ→ℝ): (γ L) (fun i=>(x i:ℂ))= inner ℂ λ₀ ((Spectral.Alps.arms (J) (fun i=> Pη (F i)) t L x) λ₀):=
 Spectral.Alps.circuit (J) λ₀ ((OS.Semigroup.fixed ..).2 (time_floor Y H V Q Qc j r C U)) _ L t x
lemma collection(x: Probe (κ→ℝ)):stackPrice Y H V Q Qc j r C U F L x=(∫ i,x i*(γ L) (fun j=>(i j:ℂ))):= Spectral.Alps.consumes (J) λ₀ λ₀ _ L x
lemma forecast (x: Probe ℝ)(u:κ→ℂ)(a b:List κ)(i:κ) (hi:i∉a)(hk:i∉b)(k: L=a++i::b)(p:HasCompactSupport ⇑x)(e:tsupport x ⊆ Set.Iio 0): (∫ p:ℝ, (γ L) (Function.update u i (p:ℂ)) * Boundary.Probe.hat x p)=0:=by rw [k]; exact Spectral.Alps.tested_one J x p e λ₀ λ₀ (fun i=> Pη (F i)) _ _ u i hi hk
end Actress
end YM.CF.Buffered.Afterglow.Tower.Selection
open YM.CF.Buffered.Afterglow.Tower.Selection.Actress
#print axioms Quantity
#print axioms quota
#print axioms amountQuota
#print axioms decisive
#print axioms window
#print axioms collection
#print axioms forecast
