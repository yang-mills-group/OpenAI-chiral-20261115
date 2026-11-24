import YM.SU5.Selected.Cancellation.Algebra
/-! # A centered calculation *on the joint ground space*

Basic cap arithmetic, and the difference between compressing a reflected product and
multiplying two caps. C*-norms to be used on the ground, *not* the chiral test algebra.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 200000
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
local notation "M" s:max => liftCap Y H V Q Qc j r C s

-- Same as Tapestry.Dome (r=false) resp its neutral subalgebra, but keep one carrier type and
-- arithmetic/space-action theorems usable directly with either of the two Hilbert theories.
section legal
variable (Z : Calibration)
def allTests : Subalgebra ℂ (Family Z) where
  carrier := { f | TestFamily Z true f ∧ (r = true → CovCover Z f) }
  mul_mem' := fun hf hg => ⟨hf.1.mul hg.1, fun u => (covariant_parts Z (hf.2 u) (hg.2 u)).2⟩
  add_mem' := fun hf hg => ⟨hf.1.add hg.1, fun u => (covariant_parts Z (hf.2 u) (hg.2 u)).1⟩
  zero_mem' := ⟨TestFamily.zeroT, fun _ => covariant_zero Z⟩
  one_mem' := ⟨TestFamily.oneT, fun _ => covariant_one Z⟩
  algebraMap_mem' z := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact ⟨TestFamily.oneT.scale z, fun _ => covariant_scale Z (covariant_one Z) z⟩
-- use Operations/unbundled sometimes to keep Vacancy API.
variable {Z}
def legalOne : Vacancy.observable Z r := ⟨1,(allTests r Z).one_mem⟩
def combined (p q : Vacancy.observable Z r) : Vacancy.observable Z r :=
  ⟨p.val+q.val,(allTests r Z).add_mem p.property q.property⟩
def weighted (p : Vacancy.observable Z r) (z : ℂ) : Vacancy.observable Z r :=
  ⟨z • p.val,(allTests r Z).toSubmodule.smul_mem z p.property⟩
def composed (p q : Vacancy.observable Z r) : Vacancy.observable Z r :=
  ⟨p.val*q.val,(allTests r Z).mul_mem p.property q.property⟩
end legal

/-- Relocating is in the axis j; also use this with a different axis later. -/
def moved (z : ℤ) (x : Test) : Test := ⟨relocate K j z x.val,
  move_ok K j z x.property.1,fun h => chime_cov _ _ _ x.property.1.paid.choose_spec (x.property.2 h)⟩

include V Q Qc C
lemma cap_shift (s : ℕ) (z : ℤ) (x : Test) : (N s) (moved Y H j r z x) = (N s) x := by
  let h := Classical.choice (anyporch Y H s j r x)
  let u : Veranda Y H s j r (moved Y H j r z x) := ⟨h.rise-z,h.span,h.pos,h.fwd, by
    rw [h.yes]; change _ = relocate K j _ (relocate K j z x.val)
    rw [relocate_sums K j _ _ x.property.1,sub_add_cancel]⟩
  rw [onAny Y H V s Q Qc j r C u,onAny Y H V s Q Qc j r C h]; rfl

lemma invariant (s : ℕ) (z : ℤ) (x y : Test) (p : y.val = relocate K j z x.val) :
    (M s) y = (M s) x := by
  rw [show y=moved Y H j r z x from Subtype.ext p]; exact Subtype.ext (cap_shift ..)

lemma cap_via_actor (s : ℕ) (x : Test) (z : ℤ) (u : F₊ s) (p : u.val = relocate K j z x.val) :
    (N s) x Ω = π₀ ((φ s) u) := by
  rw [← cap_shift Y H V Q Qc j r C s z x, ← cap_prepares Y H V Q Qc j r C s u,
    show moved Y H j r z x = toTest Y H j r s u from Subtype.ext p.symm]

omit V Q Qc C
/-- One registration for any number of arguments in this support. No covariance tweak. -/
theorem canStart (s : ℕ) (S : Finset Cover) :
    ∃ z : ℕ, Tower.region j (meshface (Λ:=Λ) 0 s) (K).ℓ (plow K j z S) := by
  have ht : Tendsto (fun w : ℕ => ruler (K).B * (w : ℤ)) atTop atTop :=
    Tendsto.const_mul_atTop' (ruler_gene _) tendsto_natCast_atTop_atTop
  obtain ⟨z,v⟩ := ((eventually_all_finset S).mpr
    (fun y _ => ht.eventually_ge_atTop (((K).ℓ:ℤ) - y j))).exists
  refine ⟨z,?_⟩; rw [area0]; intro y ey
  obtain ⟨w,hw,rfl⟩ := plow_stays K j z S ey; rw [moves,if_pos rfl]
  specialize v w hw; omega

def asField (s : ℕ) (x : Test) {S : Finset Cover} (h : InTest K true S false x.val)
    (p : Tower.region j (meshface (Λ:=Λ) 0 s) (K).ℓ S) : F₊ s :=
  ⟨x.val,(purpose_ok ..).2 ⟨(show _ from ⟨S,h,p⟩), x.property.2⟩⟩

def fromCover (s : ℕ) (z : ℕ) (x : Test) {S : Finset Cover} (h : InTest K true S false x.val)
    (p : Tower.region j (meshface (Λ:=Λ) 0 s) (K).ℓ (plow K j z S)) : F₊ s :=
  asField Y H j r s (moved Y H j r z x) (flow_port K j _ h) p

include V Q Qc C
lemma read_unit (s : ℕ) : (M s) (legalOne r) = 1 := by
  apply distinguish Y H V Q Qc j r C
  let h := unity Y H j 0 r s
  change (N s) _ Ω = Ω
  rw [show (legalOne r : Test) = toTest Y H j r s h from Subtype.ext rfl,
    cap_prepares,show (φ s) h = _ from (vacua Y H V Q.circuit j 0 r C s).symm]
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self Ω

lemma read_add (s : ℕ) (F G : Test) : (M s) (combined r F G) = (M s) F + (M s) G := by
  apply distinguish Y H V Q Qc j r C
  obtain ⟨S,p⟩ := F.property.1.paid; obtain ⟨T,q⟩ := G.property.1.paid
  obtain ⟨z,H0⟩ := canStart Y H j s (S∪T)
  let x := fromCover Y H j r s z F (p.mono subset_union_left) H0
  let y := fromCover Y H j r s z G (q.mono subset_union_right) H0
  have he := cap_via_actor Y H V Q Qc j r C s (combined r F G) z (x+y) (chime_plus ..).symm
  change (N s) _ Ω = (N s) F Ω + (N s) G Ω
  rw [he, cap_via_actor Y H V Q Qc j r C s F z x rfl, cap_via_actor Y H V Q Qc j r C s G z y rfl]
  rw [show (φ s) (x+y)=(φ s) x+(φ s) y from (arrows Y H V Q.circuit j 0 r C s).map_add _ _, map_add]

lemma read_scale (s : ℕ) (F : Test) (z : ℂ) : (M s) (weighted r F z) = z • (M s) F := by
  apply distinguish Y H V Q Qc j r C
  let X := Classical.choice (anyporch Y H s j r F)
  let x : F₊ s := X.fwd.val
  have he : (z • x).val = relocate K j X.rise (weighted r F z).val := by
    change z • X.fwd.val.val = relocate K j X.rise (z • F.val)
    rw [X.yes]; exact (chime_scale ..).symm
  change (N s) _ Ω = z • (N s) F Ω
  rw [cap_via_actor Y H V Q Qc j r C s _ X.rise (z • x) he,
    cap_via_actor Y H V Q Qc j r C s F X.rise x X.yes]
  rw [show (φ s) (z • x)=z • (φ s) x from (arrows Y H V Q.circuit j 0 r C s).map_smul _ _, map_smul]

def readout (s : ℕ) : (allTests r K) →ₗ[ℂ] (B) where
  toFun x := (M s) ⟨x.val,x.property⟩
  map_add' x y := read_add Y H V Q Qc j r C s ⟨x.val,x.property⟩ ⟨y.val,y.property⟩
  map_smul' z x := read_scale Y H V Q Qc j r C s ⟨x.val,x.property⟩ z

lemma read_refines (s n : ℕ) (p : Test) : (M (s+n)) (upward Y H Q r p s n) = (M s) p := by
  apply Subtype.ext
  change (N (s+n)) _ = (N s) _
  simpa only [Nat.add_sub_cancel_left] using
    cap_level Y H V s Q Qc j r C (F := p) (s+n) (by omega)

lemma read_mirror (s : ℕ) (p : Test) : (M s) (dual Y H j r p) = star ((M s) p) :=
  Subtype.ext (mirror_cap Y H V s Q Qc j r C).symm

-- universal 'sandwich' prepares operator formula, not limited to norms
lemma cap_sandwich (s w p : ℕ) (x : Entry Y H s j r w) (y : Entry Y H s j r p)
    (h : 0 < w) (q : 0 < p) :
    let μop := boxOp Y H V s Q Qc j r C
    let f := composed r (dual Y H j r (toTest Y H j r s x.val)) (toTest Y H j r s y.val)
    (N s) f = (π₀).comp (((μop w x h).adjoint.comp (μop p y q)).comp ((R).subtypeL)) := by
  dsimp only
  let v := edit Y H s j r w p (inverse Y H s j r w x) y
  let F := composed r (dual Y H j r (toTest Y H j r s x.val)) (toTest Y H j r s y.val)
  have he : toTest Y H j r s v.val = moved Y H j r w F := by
    apply Subtype.ext
    change (edit Y H s j r w p _ y).val.val = relocate K j w (mirror K j 0 x.val.val * y.val.val)
    rw [editor, relocate_mul]; apply congrArg (· * relocate K j w y.val.val)
    change mirror K j (gaugeT K w) x.val.val = _
    have H' := mirror_cancel K j w 0 (test_entry Y H s j r x)
    rwa [gaugeT_zero, sub_zero] at H'
  change (N s) F = _
  rw [← cap_shift Y H V Q Qc j r C s w F,←he]
  rw [cap_zero_porch Y H V Q Qc j r C s (w+p) v (by omega), respects,
    edit_comp Y H V s Q Qc j r C w p _ y h q]
end YM.CF.Buffered.Afterglow.Tower.Selection
