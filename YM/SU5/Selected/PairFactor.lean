import YM.SU5.Selected.GaugeDescent

/-!
# Pair-Parcel on mirror-separated footprints

Same diagnosed factorization as in Parcel, but tested on a pair configuration (test support
X at *each* position, shifts + simultaneous gauge on the state). Not an assertion about
factorization LEFT vs RIGHT position. In a product of the pure gauge and pure matter readings
(even ones here), read the mirrored, translated product of the gauge parts using the same state;
likewise the mirrored, translated matter tomes. Compare to their actual joint mixed reading.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 250000
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
local notation "F₊" n:max => Tower.Field Y H n j 0 r

open CF.Pannier.Chancel Tapestry
section
variable (Z : Calibration) (z : ℤ)

abbrev afterShift (x y : Family Z) := mirror Z j 0 (relocate Z j z x) * relocate Z j z y
abbrev visitedPair (S : Finset Cover) := reflectedBox j 0 (plow Z j z S) ∪ plow Z j z S

variable {Z} {S : Finset Cover} {x y : Family Z}
lemma after_ok {r : Bool} (p : InTest Z r S false x) (q : InTest Z r S false y) :
    InTest Z r (visitedPair j Z z S) false (afterShift j Z z x y) :=
  .mul ((axial Z j 0 (flow_port Z j _ p)).mono subset_union_left) ((flow_port Z j _ q).mono subset_union_right)

lemma after_scoped {X : Family Z → ℂ} (h : Scopes Z S X) (hc : Scopes Z (visitedPair j Z z S) X)
    (p : Disjoint (reflectedBox j 0 (plow Z j z S)) (plow Z j z S)) (u : InTest Z true S false x) :
    let F := afterShift j Z z x
    Scopes Z S (fun y => X (F y) + (1-X (F 1))*X y) := by
  let g : Family Z → Family Z := relocate Z j z
  let f := mirror Z j 0 (g x)
  let c := 1-X (afterShift j Z z x 1)
  let P := plow Z j z S
  let M := reflectedBox j 0 P
  have hv : InTest Z true M false f := axial Z j 0 (flow_port Z j _ u)
  let F (y : Family Z) := f * g y
  refine ⟨?_,?_,?_,?_⟩
  · rw [h.unit]; ring
  · intro y w yy ww
    change X (f * g (y+w))+c * X (y+w) = X (F y)+ c * X y + (X (F w)+ c * X w)
    rw [show g (y+w) = g y+ g w from chime_plus .., mul_add, h.plus_v y w yy ww]
    rw [hc.plus_v (F y) (F w) (after_ok j z u yy) (after_ok j z u ww)] -- tune rw
    ring
  · intro y yy d
    change X (f * g (d • y))+ c * X (d • y) = d • (X (F y)+ c * X y)
    rw [show g (d • y) = d • g y from chime_scale .., Algebra.mul_smul_comm, h.scale y yy d]
    rw [hc.scale (F y) (after_ok j z u yy) d]; simp only [smul_eq_mul, F]; ring
  intro T x' y' a b hA
  let T' := reflectGauge j (gaugeT Z z) (reflectGauge j 0 T)
  let m : Cover → SU.E := fun i => if i ∈ P then T' i else 1
  have v := relocate_gauge j S T z hA b
  have hx := circular_same P T' m (fun i hi => if_pos hi) (show Circular P T' (g x') (g y') from v)
  have hg := trivial_gauge M m (fun i hi => if_neg (fun t => Finset.disjoint_left.mp p hi t)) hv
  rw [h.gauge T _ _ a b hA, hc.gauge m _ _ (after_ok j z u a) (after_ok j z u b)
    (Circular.mul m _ (largerGauge (subset_union_left (s₁:=M) (s₂:=P)) hg) (largerGauge subset_union_right hx))]

lemma after_footprint {X : Family Z → ℂ} (h : Scopes Z S X) (hc : Scopes Z (visitedPair j Z z S) X)
    (p : Disjoint (reflectedBox j 0 (plow Z j z S)) (plow Z j z S)) (u : InTest Z true S false x)
    {T : Window.Family} {m : ℕ} {b : Fin m → Cover} (g : Injective b) (y' : y ∈ Lode Z T b S) :
    X (afterShift j Z z x y) = 0 := by
  have e := (after_scoped j z h hc p u).footprint g y'
  rw [h.footprint g y',mul_zero,add_zero] at e; exact e

variable (Z) -- explicit
/-- Factorization under test on two physically placed regions. See file header. Only the original
first link field is used for the scalar parts (`false`). Quantifies the *charged extension* as
in Centrist.Scopes; no `strict` test permission here. All these comparisons use the SAME
representation family. -/
def pairFactors (S : Finset Cover) (T : Window.Family) {m : ℕ} (u : Fin m → Cover)
    (X : Family Z → ℂ) : Prop :=
  ∀ (v w : Family Z), v ∈ Lode Z T u S → w ∈ Lode Z T u S →
    ∀ f g, Coeff false S f → Coeff false S g →
      X (afterShift j Z z (scalar Z f * v) (scalar Z g * w)) =
        X (afterShift j Z z (scalar Z f) (scalar Z g)) * X (afterShift j Z z v w)

-- in particular these products of shifted gauge (resp matter) tests = the usual gauge*matter
-- expression when bundled across regions, on the same test system
lemma resolved_parts (v w : Family Z) (p : InTest Z true S false v) (f g : PairsC → ℂ)
    (h : Coeff false S g) :
    afterShift j Z z (scalar Z f * v) (scalar Z g * w) =
      afterShift j Z z (scalar Z f) (scalar Z g) * afterShift j Z z v w := by
  unfold afterShift; rw [relocate_mul,relocate_mul,mirror_times]
  exact Commute.mul_mul_mul_comm (even_tests Z (reflect_ok Z j _ (move_ok Z j _ (aux_test p))) (move_ok Z j _ (aux_test (InTest.widen (InTest.seed h))))) _ _
lemma after_detect {X : Family Z → ℂ} (h : Scopes Z S X) (hc : Scopes Z (visitedPair j Z z S) X)
    (p : Disjoint (reflectedBox j 0 (plow Z j z S)) (plow Z j z S))
    {T : Window.Family} {m : ℕ} {b : Fin m → Cover} (g : Injective b)
    (u : pairFactors j Z z S T b X) {x y : Family Z} (x' : x ∈ Filigree Z T b S) (y' : y ∈ Filigree Z T b S) :
    X (afterShift j Z z x y) = 0 := by
  let f : Family Z → Family Z := relocate Z j z
  let P := visitedPair j Z z S
  let S' := Filigree Z T b S
  let Ψ (x y : Family Z) := afterShift j Z z x y
  have h₀ : f 0 = 0 := by
    simpa only [zero_smul,f,relocate] using (chime_scale Z j (gaugeT Z z) (F:=0) (0:ℂ))
  have k₀ : mirror Z j 0 0 = 0 := by
    simpa only [star_zero,zero_smul] using (mirror_scale (F:= (0:Family Z)) Z j 0 (0:ℂ)) -- tune
  have ht{a b : Family Z} (h:a∈S') (u:b∈S') : InTest Z true P false (Ψ a b) := after_ok j z (FilTest (W:=T) h).widen (FilTest (W:=T) u).widen
  refine Submodule.span_induction (p:=fun x _ => X (Ψ x y)=0) ?_ ?_ ?_ ?_ x'
  · intro r t; obtain ⟨w,q,e,c,rfl⟩ := t
    let W' := scalar Z q * w
    have hv : W'∈ S' := Submodule.subset_span (show _ ∈ _ from ⟨w,q,e,c,rfl⟩)
    refine Submodule.span_induction (p:=fun y _ => X (Ψ W' y) = 0) ?_ ?_ ?_ ?_ y'
    · intro r t; obtain ⟨v,Q,w₁,d,rfl⟩ := t
      exact (u w v e w₁ q Q c d).trans (by rw [after_footprint j z h hc p (Lode_test e).widen g w₁,mul_zero])
    · change X (_ * f 0) = _; rw [h₀,mul_zero,hc.nil_v]
    · intro a b i j' A' B'
      rw [show Ψ W' (a+b)= Ψ W' a+ Ψ W' b from by unfold Ψ afterShift relocate; rw [chime_plus Z j _ (G:=b) (F:=a),mul_add],hc.plus_v _ _ (ht hv i) (ht hv j'),A',B',add_zero]
    intro a v p H; rw [show Ψ W' (a • v)= a • Ψ W' v from by unfold Ψ afterShift relocate; rw [chime_scale,Algebra.mul_smul_comm], hc.scale _ (ht hv p),H,smul_zero]
  · change X (mirror Z j 0 (f 0)*_)=_; rw [h₀,k₀,zero_mul,hc.nil_v]
  · intro a b i j' A' B'
    rw [show Ψ (a+b) y= Ψ a y+ Ψ b y from by unfold Ψ afterShift relocate; rw [chime_plus,mirror_plus,add_mul], hc.plus_v _ _ (ht i y') (ht j' y'),A',B',add_zero]
  intro a v p H
  rw [show Ψ (a • v) y=star a • Ψ v y from by unfold Ψ afterShift relocate; rw [chime_scale,mirror_scale,Algebra.smul_mul_assoc],hc.scale _ (ht p y'),H,smul_zero]
end
end YM.CF.Buffered.Afterglow.Tower.Selection
