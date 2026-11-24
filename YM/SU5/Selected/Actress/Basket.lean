import YM.SU5.Selected.Actress.Lode
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
local notation "Σ₀"=> Actress.Label Y H j r
local notation "Pη"=> Label.money Y H V Q Qc j r C U
local notation "Z" x:max=> balcony J x
-- Chronometry. at resolution evaluate in chronological order (earliest on left). Points are *empty separation* in gaps, **in addition** to widths! n shifts>=0 times. spine recursively. Applicability $u: ∀ cal-i rank ≤ s$ (finite labels use subtype or Fin).
variable (s:ℕ)
variable {κ:Type*}(F:κ→Label Y H j r)(v:∀ i,(F i).count ≤ s)(z:κ→ℕ)
local notation "h₀" i:max=> (F i).count
local notation "R₁" i:max=> Label.finery Y H Q j r s (F i) (v i)
def Label.extent (x:Label Y H j r):ℕ:=Λ.R.L.val^(s-x.count)*x.span
local notation "L₀" i:max=> Label.extent Y H j r s (F i)
-- Field. Axis strict arbitrary. no condition on overlaps in *space* (B-vectors). At rank s.
noncomputable def lode : List κ→ F₊ s
| []=> unity Y H j 0 r s
| i::l=> (τ s) (2*z i) (slabT Y H s j r _ (R₁ i) (lode l))
local notation "γ"=> lode Y H Q j r s F v z
variable (l₀:List κ)
local notation "μ" n:max=> relocate K j n
local notation "f₀" i:max=> (R₁ i).val.val
local notation "χΩ"=> marked Y H V Q Qc j r C χ
local notation "β" i:max=> whenly (timeMesh Λ) s (z i)
include V Q Qc C U v
lemma inventory(i:κ) : (γ (i::l₀)).val=(μ (z i:ℕ)) ( (f₀ i) * (μ (L₀ i:ℕ)) (γ l₀).val):= (SlabMark.timed_apply Y H j r s _ _).trans (congrArg (μ (z i:ℕ)) (slab_eq Y H s j r _ _ _)) -- p width actual p≥1 needed? no ledger.
lemma picks: CovCover K (γ l₀).val:=by
 induction l₀ with| nil=> exact covariant_one (K)
                   | cons i a u=> rw [inventory Y H V Q Qc j r C U]; let T:= R₁ i; let x:= T.val.val; let G:=(γ a).val; let W': TestFamily K true G:= (toTest Y H j r s (γ a)).property.1
                                  have v':= Label.up_neutral Y H V Q Qc j r C U s (F i) (v i); let k':=(μ (L₀ i:ℕ)) G;
                                  have he: CovCover K k':= chime_cov K j _ W'.paid.choose_spec u
                                  have hk: CovCover K (x*k'):= (covariant_parts K (show CovCover K x from v') he).2; exact chime_cov K j _ ((SlabMark.test_entry Y H s j r T).mul (SlabMark.move_ok K j ((L₀ i:ℕ):ℤ) W')).paid.choose_spec hk -- syntax fragile
-- Mark resolution supported: because F permits all gauges and lift identities, this is expected on fullχ (r=false) & singlet family χ itself only fallback. not invoking spatial localization.
noncomputable def onArc {κ:Type*} (F:κ→Actress.Label Y H j r) := Spectral.Alps.trip (Diary.jetTime Y H V Q Qc j r C U) (fun i=> Label.money Y H V Q Qc j r C U (F i))
local notation "T₀" F:max l:max => onArc Y H V Q Qc j r C U F l
lemma begin {p:ℕ}(x:F₊ s) : balcony (J) ((↑(whenly (timeMesh Λ) s p : ℝ≥0):ℝ)* Complex.I) ((η s) x) = (η s) ((τ s) (2*p) x):=by
 let F:=J; let G:=journey Y H V Q Qc j r C U; have ht: F.E (whenly (timeMesh Λ) s p)=G.double s p:= G.track_even s p; exact (congrArg (fun f:U.H.Op=>f ((η s) x)) ((balcony_high F _).trans ht)).trans (tempo_now Y H V Q Qc j r C U s (2*p) _)
-- caution include v unused auto and depends F. move outside section.
local notation "HK" F:max l:max=> (T₀ F l)
lemma chronology : ((T₀ F l₀) (fun i=> (↑(β i:ℝ≥0):ℝ)*Complex.I)) λ₀= (η s) (γ l₀):=by
 induction l₀ with
 | nil=> change λ₀ = _; exact normal_base Y H V Q Qc j r C U s
 | cons i l h=> let t:= (↑(β i:ℝ≥0):ℝ); let W':= (F i); let a:= Pη (F i); let x:=(γ l); let g: F₊ s:=slabT Y H s j r _ (R₁ i) x; let V':= Label.money Y H V Q Qc j r C U (F i); let f':= (T₀ F l) (fun i=> (↑(β i:ℝ≥0):ℝ)* Complex.I); let E₀:=Z (↑t*Complex.I)
                have hp:a ((η s) x)=(η s) g:= (congrArg (fun i:U.H.Op=> i ((η s) x)) (Label.compatible Y H V Q Qc j r C U s (F i) (v i))).trans (thrills Y H V Q Qc j r C U s (L₀ i) (R₁ i) (Nat.mul_pos (pow_pos Λ.R.L.property _) (F i).paid) x)
                exact ((congrArg E₀ ((congrArg a h).trans hp)).trans (Actress.begin Y H V Q Qc j r C U s F v g))
lemma expectancy : inner ℂ λ₀ (((T₀ F l₀) (fun i=> (↑(β i:ℝ≥0):ℝ)*Complex.I)) λ₀)= (χΩ) s (toTest Y H j r s (γ l₀)):= (congrArg (inner ℂ λ₀) (chronology Y H V Q Qc j r C U s F v z l₀)).trans (actual_expect Y H V Q Qc j r C U s _)
-- risk TC cost notation. ANSI.
end Actress
end YM.CF.Buffered.Afterglow.Tower.Selection
open YM.CF.Buffered.Afterglow.Tower.Selection.Actress
#print axioms Label.upSize
#print axioms inventory
#print axioms picks
#print axioms expectancy
#print axioms onArc
