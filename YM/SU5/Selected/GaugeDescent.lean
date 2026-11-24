import YM.SU5.Selected.CapCalc
/-!
# Gauge symmetry descends to the cap algebra

The mixture issue for the `Parcel` test has a resolution already at this stage. The purely
matter words it uses are color-charged even tests, so one must work WITHOUT the optional `strict`
restriction, while requiring the component states still have the full local gauge symmetry. This
is not a global rigid symmetry: if the supported positive field x is gauge moved, we can let
that gauge be the identity on the reflected support of y. Thus the symmetry is available in
*every* state of the actual abelian ground compression algebra.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 240000
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
  (j : Axis) (C : Arena Y H Q.circuit j 0 false)
local notation "R" => Aurora Y H V Q j false C
local notation "A" => Ark.Ht Y H Q.circuit j 0 false C
local notation "W" => floorV Y H Q.circuit j 0 false C
local notation "F₊" n:max => Tower.Field Y H n j 0 false
local notation "φ" n:max => actor Y H n Q.circuit j 0 false C
local notation "Ω" => seat0 Y H V Q j false C
local notation "π₀" => (R).orthogonalProjectionOnto
local notation "N" n:max => cap Y H V n Q Qc j false C
local notation "Test" => Vacancy.observable (tent Y H) false
local notation "Lab" => Beacon (tent Y H) false

local notation "B" => groundAlgebra Y H V Q Qc j false C
local notation "M" s:max => liftCap Y H V Q Qc j false C s
open Tapestry
section localgauge
variable {Z : Calibration} {F G : Family Z} (S : Finset Cover) (u v : Cover → SU.E)
lemma circular_same (p : ∀ x ∈ S, v x = u x) (q : Circular S u F G) : Circular S v F G :=
  fun m g h => q m g fun x a => (h x a).trans (p x a)

lemma trivial_gauge (p : ∀ x ∈ S, v x = 1) (h : InTest Z true S false F) :
    Circular S v F F := by
  let x : Dome Z := ⟨F,Tower.aux_test h⟩
  have a : x ∈ bay Z S true := h
  have z := pennantTrace Z S (1 : Cover → SU.E) a
  rw [pennantId] at z
  exact circular_same S 1 v p z

lemma mirror_gauge (s : ℤ) (p : Circular S u F G) (h : InTest Z true S false G) :
    Circular (reflectedBox j s S) (reflectGauge j s u) (mirror Z j s F) (mirror Z j s G) := by
  intro n w t
  refine reflectHarmony j s (p n (w ∘ (plane j s).anon (Z.c n)) ?_) (h.support n)
  intro i hi
  unfold reflectGauge at t
  change w ((plane j s).anon _ _) = _
  rw [Shape.anno, t _ (mem_image_of_mem _ hi),comp_apply]; apply congrArg u; funext a
  rw [fling_move,fling_move]; split <;> ring

lemma relocate_gauge (z : ℤ) (p : Circular S u F G) (h : InTest Z true S false G) :
    let w := gaugeT Z z
    Circular (plow Z j z S) (reflectGauge j w (reflectGauge j 0 u))
      (relocate Z j z F) (relocate Z j z G) := by
  let w := gaugeT Z z
  have k := mirror_gauge j (reflectedBox j 0 S) (reflectGauge j 0 u) w (mirror_gauge j S u 0 p h) (axial Z j 0 h)
  rw [support_translation, sub_zero] at k; exact k
end localgauge

include V Q C
private lemma gauged_inner (s : ℕ) (S : Finset Cover) (u : Cover → SU.E)
    (x y z : F₊ s) (p : InTest K true S false x.val) (q : InTest K true S false y.val)
    (w : Tower.region j (meshface (Λ:=Λ) 0 s) (K).ℓ S) (h : Circular S u x.val y.val) :
    inner ℂ ((φ s) z) ((φ s) x) = inner ℂ ((φ s) z) ((φ s) y) := by
  rw [stems Y H V,stems Y H V,area0]
  let U := reflectedBox j 0
  obtain ⟨T, ht, pt⟩ := ((purpose_ok ..).1 z.property).1
  have hz : ∀ i ∈ U T, i ∉ S := by
    intro i hi g
    rw [area0] at w pt
    obtain ⟨x',f,rfl⟩ := mem_image.mp hi
    have Hh := pt x' f; specialize w _ g; rw [reflected_coord] at w
    have he : 0 < (K).ℓ := margin_good ..
    omega
  let D' : Cover → SU.E := fun i => if i ∈ S then u i else 1
  let L := S ∪ U T; have e : S ⊆ L := subset_union_left; have f : U T ⊆ L := subset_union_right
  have v := axial K j 0 ht
  have k' : Circular L D' (mirror K j 0 z.val) (mirror K j 0 z.val) := largerGauge f (trivial_gauge (U T) D' (fun i t => if_neg (hz i t)) v)
  have l' : Circular L D' x.val y.val := largerGauge e (circular_same S u D' (fun i hi => if_pos hi) h)
  exact (Papal.ledgerRule Y H V L s).gauge D' _ _ ((v.mono f).mul (p.mono e)) ((v.mono f).mul (q.mono e)) (k'.mul D' L l')

lemma gauged_actor (s : ℕ) (S : Finset Cover) (u : Cover → SU.E)
    (x y : F₊ s) (p : InTest K true S false x.val) (q : InTest K true S false y.val)
    (w : Tower.region j (meshface (Λ:=Λ) 0 s) (K).ℓ S) (h : Circular S u x.val y.val) :
    (φ s) x = (φ s) y := by
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜:=ℂ)).mp
  rw [inner_sub_left,inner_sub_right,inner_sub_right,
    gauged_inner Y H V Q j C s S u x y x p q w h,
    gauged_inner Y H V Q j C s S u x y y p q w h]; abel

include Qc
lemma gauge_in_cap (s : ℕ) (S : Finset Cover) (u : Cover → SU.E)
    (x y : Test) (p : InTest K true S false x.val) (q : InTest K true S false y.val)
    (h : Circular S u x.val y.val) :
    (M s) x = (M s) y := by
  apply distinguish Y H V Q Qc j false C
  obtain ⟨z,w⟩ := canStart Y H j s S
  let x' := fromCover Y H j false s z x p w
  let y' := fromCover Y H j false s z y q w
  change (N s) x Ω = (N s) y Ω
  rw [cap_via_actor Y H V Q Qc j false C s x z x' rfl, cap_via_actor Y H V Q Qc j false C s y z y' rfl,
    gauged_actor Y H V Q j C s _ _ x' y' (flow_port K j _ p) (flow_port K j _ q) w (relocate_gauge j S u z h q)]
open CF.Pannier.Chancel

-- natural statement in Chancel.Scopes, on the entire level space. Arbitrary off-test value
-- (zero); Scopes/Parcel/Filigree can only detect the on-test values.
def accessReading (f : ↑(B) →ₗ[ℂ] ℂ) (s : ℕ) (x : Family K) : ℂ := by
  classical exact if h : TestFamily K true x then f ((M s) (⟨x,h,fun p => by cases p⟩ : Test)) else 0
lemma access_read (f : ↑(B) →ₗ[ℂ] ℂ) (s : ℕ) (x : Test) :
    accessReading Y H V Q Qc j C f s x.val = f ((M s) x) := by
  unfold accessReading; split; rfl; rename_i h; exact (h x.property.1).elim
set_option maxHeartbeats 420000 in
lemma access_scopes (f : ↑(B) →ₗ[ℂ] ℂ) (h : f 1 = 1) (s : ℕ) (S : Finset Cover) :
    Scopes K S (accessReading Y H V Q Qc j C f s) := by
  let read := accessReading Y H V Q Qc j C f s
  let X (x : Family K) (p : InTest K true S false x) : Test := ⟨x,aux_test p,fun p => by cases p⟩
  let m := M s
  constructor
  · rw [show (1:Family K) = (legalOne (Z:=K) false).val from rfl,
      access_read, read_unit]; exact h
  · intro x y hx hy
    change read (combined false (X x hx) (X y hy)).val = read (X x hx).val + read (X y hy).val
    unfold read; rw [access_read Y H V Q Qc j C f s (combined false (X x hx) (X y hy)),
      access_read Y H V Q Qc j C f s (X x hx),access_read Y H V Q Qc j C f s (X y hy),
      read_add Y H V Q Qc j false C s (X x hx) (X y hy)]; exact f.map_add _ _ --]
  · intro x p z
    change read (weighted false (X x p) z).val = z • read (X x p).val
    unfold read; rw [access_read Y H V Q Qc j C f s (weighted false (X x p) z),
      access_read Y H V Q Qc j C f s (X x p),read_scale Y H V Q Qc j false C s (X x p) z]; exact f.map_smul _ _ --]
  intro u x y p q g
  have he : m (X x p) = m (X y q) := gauge_in_cap Y H V Q Qc j C s S u (X x p) (X y q) p q g
  exact (access_read Y H V Q Qc j C f s (X x p)).trans ((congrArg f he).trans (access_read Y H V Q Qc j C f s (X y q)).symm)
end YM.CF.Buffered.Afterglow.Tower.Selection
