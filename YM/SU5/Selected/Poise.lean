import YM.SU5.Selected.SignedPlane
import YM.SU5.Selected.Choice

/-! # Law on these same synchronized Euclidean test spaces.

Not normalized by hand on gauges. No factorization assumption across coincident slots or Gauge.
`Consensus` set of functions on whole Even (incl. strict determination offered separately)
with reading laws the component is extreme in. Important that this really descends from the μ
and the ground system over ALL axes. Use RP all registered halfplanes (proved also for odd).
This is not propounding symmetry/cyclic locality already.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 650000
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

local notation "uℋ" => basisRoom Y H V Q j r C
local notation "m" χ:max => marked Y H V Q Qc j r C χ
local notation "M" s:max => liftCap Y H V Q Qc j r C s
local notation "J" => Heat.gaugeShift Λ.block
-- read all words as F∈Test at selected s
abbrev Sample := ℕ→ Test→ ℂ
local notation "Sw" => Sample Y H r
structure Consensus (x : Sw) : Prop where
  -- include normalization unital at each s explicitly
  one (s) : x s (legalOne r)=1
  add (s) (f g) : x s (combined r f g)=x s f+x s g
  scale (s) (f) (z:ℂ) : x s (weighted r f z)=z * x s f
  upward (s) (n) (f) : x (s+n) (Vacancy.upward Y H Q r f s n)=x s f
  shift (s) (a : Axis) (z : ℤ) (f) : x s (stepTest Y H a r z f)=x s f
  flip (s) (a : Axis) (z : ℤ) (f) : x s (looking Y H a r (J z) f)=star (x s f)
  rp (s) (a : Axis) (z : ℤ) (f : Test) (p : Finset Cover) :
    InTest (tent Y H) true p false f.val → Tower.region a (J z) (tent Y H).ℓ p → 0 ≤ x s (glance Y H a r (J z) f)
-- Cauchy using completing the square (can also use Kernel lemma generically). lean see Tune.
variable {x : Sample Y H r} (u : Consensus Y H Q r x) (s : ℕ)
local notation "F" s:max f:max => toTest Y H j r s f
local notation "E" s:max f:max => x s (F s f)
local notation "R₀" s:max f:max g:max => x s (bornTest Y H j r s f g)
local notation "λ₁" s:max => unity Y H j 0 r s
include V Q Qc C
lemma all_together (χ : CapCharacter Y H V Q Qc j r C) : Consensus Y H Q r (m χ) :=
  { one := fun _=> (congrArg χ (read_unit ..)).trans χ.map_one
    add := fun s f g=> (congrArg χ (read_add ..)).trans (χ.map_add _ _)
    scale := fun s f z=> (congrArg χ (read_scale ..)).trans (map_smul χ _ _)
    upward := fun _ _ _=> congrArg χ (read_refines ..)
    flip := fun s i z p=> (congrArg χ (at_seam Y H V Q Qc j r C s z p i)).trans (χ.map_star' _)
    shift := fun s i z p => congrArg χ (stationarity Y H V Q Qc j r C s z p i)
    rp := fun s i z f p t v => by
      obtain ⟨C'⟩ := voyage_H Y H V Q.circuit i 0 r
      rw [←unchanged Y H V Q Qc j r C i C' χ]
      exact rp_rank Y H V Q Qc i r C' (Classical.choice (realizeRoom Y H V Q Qc i r C' _)) s f z p t v }
omit V Qc C
-- competitors
include Q u
namespace Consensus
lemma rpos (a : F₊ s) : 0 ≤ R₀ s a a := by
  have hx := u.rp s j 0
  rw [show J 0=(0:ℤ) from by unfold Heat.gaugeShift; ring] at hx
  obtain ⟨T,p,h⟩ := ((purpose_ok ..).1 a.property).1
  rw [area0] at h; exact hx (F s a) T p h
lemma radd (f g z : F₊ s) : R₀ s (f+g) z = R₀ s f z + R₀ s g z := by
  rw [←u.add]; congr 1; apply Subtype.ext
  change mirror K j 0 (f.val+g.val)*_=_; rw [mirror_plus,add_mul]; rfl
lemma rscale (f g : F₊ s) (z : ℂ) : R₀ s (z • f) g = star z * R₀ s f g := by
  rw [←u.scale]; congr 1; apply Subtype.ext
  change mirror K j 0 (z • f.val)*_=_; rw [mirror_scale]; exact Algebra.smul_mul_assoc ..
lemma rone (f : F₊ s) : R₀ s (λ₁ s) f = E s f := by
  -- use born measure direct identity
  apply congrArg (x s); apply Subtype.ext
  change mirror K j 0 1 * f.val= f.val; rw [mirror_unit,one_mul]
lemma form (f : F₊ s) : R₀ s f (λ₁ s) = star (E s f) := by
  have h := u.flip s j 0 (F s f); rw [show J 0=(0:ℤ) from by unfold Heat.gaugeShift; ring] at h
  rw [←h]; apply congrArg (x s); exact Subtype.ext (mul_one _)

omit Q u in
private lemma complete_square (a w y : ℂ)
    (h : w+a*star a = y) (p : 0 ≤ w) : (‖a‖^2 : ℝ) ≤ y.re := by
  rw [←h]; change _ ≤ (w+a* (starRingEnd ℂ a)).re; rw [Complex.mul_conj,Complex.add_re, Complex.ofReal_re,Complex.normSq_eq_norm_sq]
  linarith only [(show 0 ≤ w.re from (Complex.le_def.mp p).1)]
lemma dominates (f : F₊ s) : ‖E s f‖^2 ≤ (R₀ s f f).re := by
  set a₀ := E s f; let k := f+(-a₀) • (λ₁ s)
  refine complete_square a₀ (R₀ s k k) (R₀ s f f) ?_ (rpos Y H Q j r u s k)
  unfold k
  rw [born_add,u.add,radd Y H Q j r u,radd Y H Q j r u,
      rscale Y H Q j r u,rscale Y H Q j r u,rone Y H Q j r u]
  have he : F s ((-a₀) • (λ₁ s))=weighted r (legalOne r) (-a₀):=Subtype.ext rfl
  rw [rone Y H Q j r u, born_scale,u.scale, form Y H Q j r u,he,u.scale,u.one,star_neg]; unfold a₀; ring

lemma mature (p : F₊ s) (t : ℕ) (q : s ≤ t) : E t (Raise Y H Q.circuit j 0 r s t q p)=E s p := by
  obtain ⟨t,rfl⟩:= Nat.exists_eq_add_of_le q
  rw [←u.upward s t (F s p)]; congr 1; apply Subtype.ext; change stream Y H D s _ p.val= stream Y H D s _ _; rw [show s+t-s=t from by omega]; rfl
-- maybe no goals left
-- linear
noncomputable def read : F₊ s →ₗ[ℂ] ℂ := {
  toFun p := E s p
  map_add' p q := u.add s (F s p) (F s q)
  map_smul' a p := u.scale s (F s p) a }
lemma wake_rule (f : Test) (z : ℤ) : x s (moved Y H j r z f)=x s f := u.shift s j (2*z) f
lemma tick_rule (f : F₊ s) (t : ℕ) : E s (tick Y H s j 0 r t f)=E s f := u.shift s j t (F s f)
lemma sail_rule (f : F₊ s) (v : Trans j) (t : ℤ) : E s (sail Y H s j 0 r v.val v.property t f)=E s f := u.shift s v.val t (F s f)
end Consensus
end YM.CF.Buffered.Afterglow.Tower.Selection
