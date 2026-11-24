import YM.SU5.Selected.Fixed
/-!
# Upgrade compressed moments to an abelian algebra

Do this on the joint-zero-energy-and-grid-invariant space, on the very same Coherent history.
All actors of positive marks become caps applied to vacuum (after projecting) so we can
separate in that space if needed. No assumed uniqueness of the original vacuum. Do NOT
transport a claim from smooth-point Euclidean data (`YM/Ground/*`), though analogously we can
use four-index symmetry in the moments proof of commutativity.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 100000
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


variable (s : ℕ)

def toTest (x : F₊ s) : Test := ⟨x.val,
  (exam j _ K ((purpose_ok ..).1 x.property).1).1, ((purpose_ok ..).1 x.property).2⟩

lemma eachField_enters (x : F₊ s) : ∃ w : ℕ, ∃ u : Entry Y H s j r w, 0 < w ∧ u.val = x := by
  obtain ⟨S, t, h⟩ := ((purpose_ok ..).1 x.property).1
  rw [area0] at h
  have he : ∀ᶠ w : ℕ in atTop, ∀ y ∈ S, y j + ((K).ℓ : ℤ) ≤ ruler Λ.block * w := by
    refine (eventually_all_finset S).mpr fun y _ => ?_
    have T : Tendsto (fun w : ℕ => ruler Λ.block * (w : ℤ)) atTop atTop :=
      Tendsto.const_mul_atTop' (ruler_gene _) tendsto_natCast_atTop_atTop
    exact T.eventually (eventually_ge_atTop _)
  obtain ⟨w, p, v⟩ := (he.and (eventually_gt_atTop 0)).exists
  exact ⟨w, (⟨x, S, t, fun y g => ⟨h y g,p y g⟩⟩ : Entry Y H s j r w), v, rfl⟩

def noShift (w : ℕ) (u : Entry Y H s j r w) (hw : 0 < w) :
    Veranda Y H s j r (toTest Y H j r s u.val) where
  rise := 0
  span := w
  pos := hw
  fwd := u
  yes := (relocate_zero K j (test_entry Y H s j r u)).symm

include V Q C
lemma ground_normalized : ‖Ω‖ = 1 := vane Y H V Q.circuit j 0 r C
lemma projection_to (x : (A)) (y : (R)) : inner ℂ (π₀ x) y = inner ℂ x (y : (A)) := by
  -- mathlib
  exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right y x

include Qc
lemma cap_zero_porch (s w : ℕ) (u : Entry Y H s j r w) (p : 0 < w) :
    (N s) (toTest Y H j r s u.val) =
      (π₀).comp ((boxOp Y H V s Q Qc j r C w u p).comp (R).subtypeL) :=
  onAny Y H V s Q Qc j r C (noShift Y H j r s w u p)

lemma cap_prepares (x : F₊ s) : (N s) (toTest Y H j r s x) Ω = π₀ ((φ s) x) := by
  obtain ⟨w,u,p,rfl⟩ := eachField_enters Y H j r s x
  rw [cap_zero_porch Y H V Q Qc j r C s w u p]
  change π₀ (boxOp Y H V s Q Qc j r C w u p W) = _
  rw [lays]

lemma cap_cyclic : DenseRange (fun L : Lab => (N L.1) L.2 Ω) := by
  have hπ : Surjective (π₀) := fun p => ⟨_, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self p⟩
  have he := hπ.denseRange.dense_image (π₀).continuous (sounds Y H V Q.circuit j 0 r C)
  refine he.mono ?_
  rintro x ⟨y, ty, rfl⟩
  obtain ⟨s0,z,rfl⟩ := Set.mem_iUnion.mp ty
  exact ⟨(s0,toTest Y H j r s0 z), cap_prepares Y H V Q Qc j r C s0 z⟩

/-- `Nodup` in `any_order` constrains the indices, not the observables *assigned to* them. -/
lemma exchange (p q u v : Lab) :
    let m (i : Lab) := (N i.1) i.2
    inner ℂ Ω (m p (m q (m u (m v Ω)))) = inner ℂ Ω (m p (m u (m q (m v Ω)))) := by
  let X : Fin 4 → Lab := ![p,q,u,v]
  have he := any_order Y H V Q Qc j r C X [0,1,2,3] [0,2,1,3] (by decide) (.cons 0 (.swap ..))
  exact he -- defeq?

lemma cap_commute (u v : Lab) : Commute ((N u.1) u.2) ((N v.1) v.2) := by
  let m (i : Lab) := (N i.1) i.2
  have he (w z : Lab) : inner ℂ (m w Ω) (m u (m v (m z Ω))) = inner ℂ (m w Ω) (m v (m u (m z Ω))) := by
    let y : Lab := (w.1, dual Y H j r w.2)
    have hx : m y = (m w).adjoint := (mirror_cap Y H V w.1 Q Qc j r C).symm
    have e := exchange Y H V Q Qc j r C y u v z
    change inner ℂ Ω (m y _) = inner ℂ Ω (m y _) at e
    rwa [hx, ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right] at e
  have hd := cap_cyclic Y H V Q Qc j r C
  change m u * m v = m v * m u
  apply DFunLike.coe_injective
  refine hd.equalizer (m u * m v).continuous (m v * m u).continuous (funext fun z => hd.eq_of_inner_right ℂ ?_)
  exact fun w => he w z

def familyCaps : Set (↑(R) →L[ℂ] ↑(R)) := Set.range fun u : Lab => (N u.1) u.2
omit V Q C Qc in
private theorem topops (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X] : IsSemitopologicalSemiring (X →L[ℂ] X) := inferInstance
omit V Q C Qc in
private theorem starops (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X] : ContinuousStar (X →L[ℂ] X) := inferInstance
instance groundSemitop : IsSemitopologicalSemiring (↑(R) →L[ℂ] ↑(R)) := topops ↑(R)
instance groundStarCont : ContinuousStar (↑(R) →L[ℂ] ↑(R)) := starops ↑(R)
#check groundSemitop

def groundAlgebra : StarSubalgebra ℂ (↑(R) →L[ℂ] ↑(R)) :=
  (StarAlgebra.adjoin ℂ (familyCaps Y H V Q Qc j r C)).topologicalClosure
local notation "B" => groundAlgebra Y H V Q Qc j r C

lemma caps_star {x : (R) →L[ℂ] (R)} (p : x ∈ familyCaps Y H V Q Qc j r C) :
    star x ∈ familyCaps Y H V Q Qc j r C := by
  obtain ⟨⟨n,f⟩,rfl⟩ := p
  exact ⟨⟨n,dual Y H j r f⟩,(mirror_cap Y H V n Q Qc j r C).symm⟩

lemma ground_abelian (x y : B) : x * y = y * x := by
  let S := familyCaps Y H V Q Qc j r C
  have hv : ∀ f ∈ S, ∀ g ∈ S, f*g = g*f := by
    rintro _ ⟨s,rfl⟩ _ ⟨t,rfl⟩
    exact cap_commute Y H V Q Qc j r C s t
  let U := StarAlgebra.adjoin ℂ S
  haveI : IsMulCommutative U := StarAlgebra.isMulCommutative_adjoin ℂ hv
    (fun x hx y hy => hv _ hx _ (caps_star Y H V Q Qc j r C hy))
  letI := U.commSemiringTopologicalClosure (fun x y => IsMulCommutative.is_comm.comm x y)
  exact mul_comm (G := ↑(U.topologicalClosure)) x y

def liftCap (F : Test) : B :=
  ⟨(N s) F, StarSubalgebra.le_topologicalClosure _
    (StarAlgebra.subset_adjoin ℂ (familyCaps Y H V Q Qc j r C) ⟨(s,F),rfl⟩)⟩

lemma distinguish (x y : B) (h : x.val Ω = y.val Ω) : x = y := by
  apply Subtype.ext; apply DFunLike.coe_injective
  refine (cap_cyclic Y H V Q Qc j r C).equalizer x.val.continuous y.val.continuous ?_
  funext i
  let f := liftCap Y H V Q Qc j r C i.1 i.2
  change (x*f).val Ω = (y*f).val Ω
  rw [ground_abelian Y H V Q Qc j r C x f, ground_abelian Y H V Q Qc j r C y f]
  exact congrArg f.val h

/-- Can `letI` to use commutative spectral machinery. -/
noncomputable abbrev spectrumData : CommCStarAlgebra B := by
  haveI : IsClosed (↑(B) : Set (↑(R) →L[ℂ] ↑(R))) := isClosed_closure
  exact { (StarSubalgebra.cstarAlgebra (B)) with
    mul_comm := ground_abelian Y H V Q Qc j r C }
end YM.CF.Buffered.Afterglow.Tower.Selection
