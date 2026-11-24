import YM.SU5.Selected.Support
import Mathlib.Analysis.CStarAlgebra.Classes

/-!
# The abelian joint vacuum algebra

We do this on the big Hilbert space (the test extension on which one can ask `Parcel`).
Use `obs`/`Dome` labels from the one history; no post-limit extra charged degrees of freedom.

Products *in this abelian algebra* are products of **compressed** operators. Not claiming
multiplicativity from the Euclidean labels. Repeated insertion of THE SAME observable is
needed (e.g. for the square norm argument in conditioning). `Nodup` in `any_order`
constrains the list of **indices**, not the image; in our applications
we can supply the actual permutations with distinct indices, assigning the same input
several times if need be.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

/-- Keeping the history arguments together, not assuming any further field laws. -/
structure Spine where
  par : Preparation
  width : ℕ
  run : Course par (VolumeCape.Dream.Nimbus width)
  large : Real.exp 1 ≤ par.x
  period : ℕ → ℕ
  cutoff : ℕ → ℕ
  ultraviolet : ℕ → Family (tent run large) → ℕ → ℂ
  E : ℕ → Family (tent run large) → ℂ
  law : Universal run large period cutoff ultraviolet E
  projection : GroundExtension (i := period) (k := cutoff) (E := E) run large

namespace Spine
variable (P : Spine) (j : Axis)
abbrev calibration := tent P.run P.large
abbrev refineTest := P.projection.refine
abbrev history := P.projection.history
abbrev room : Arena P.run P.large P.history.circuit j 0 false :=
  Classical.choice (voyage_H P.run P.large P.law P.history.circuit j 0 false)
abbrev Hil := Ark.Ht P.run P.large P.history.circuit j 0 false (P.room j)
abbrev vacuum := Aurora P.run P.large P.law P.history j false (P.room j)
-- Note: capital Hil is a full Hilbert bundle, not just its type. Don't change unit.
abbrev groundZero := Vacancy.seat0 P.run P.large P.law P.history j false (P.room j)
abbrev floorVec := floorV P.run P.large P.history.circuit j 0 false (P.room j)
abbrev piZero := (P.vacuum j).orthogonalProjectionOnto
abbrev inHil := (P.vacuum j).subtypeL
abbrev Vox (s : ℕ) := Tower.Field P.run P.large s j 0 false
abbrev piece (s : ℕ) := actor P.run P.large s P.history.circuit j 0 false (P.room j)
abbrev Card (s w : ℕ) := Entry P.run P.large s j false w
abbrev Box (s w : ℕ) (p : 0 < w) (x : P.Card j s w) :=
  boxOp P.run P.large P.law s P.history P.projection.clipped j false (P.room j) w x p
abbrev Test := Dome P.calibration
abbrev obs (f : P.Test) : observable P.calibration false :=
  ⟨f.val, (marque P.calibration).mp f.property, by simp⟩
abbrev compressed (s : ℕ) (f : P.Test) :=
  Vacancy.cap P.run P.large P.law s P.history P.projection.clipped j false (P.room j) (P.obs f)
abbrev labelled (v : ℕ × P.Test) := P.compressed j v.1 v.2
abbrev reflectTest := aureole P.calibration j 0
abbrev entryTest (s : ℕ) {w : ℕ} (x : P.Card j s w) : P.Test :=
  ⟨x.val.val, (marque P.calibration).mpr (test_entry ..)⟩
abbrev voxTest (s : ℕ) (x : P.Vox j s) : P.Test :=
  ⟨x.val, (marque P.calibration).mpr (field_test ..)⟩

variable {w : ℕ}
local notation "ω" => P.groundZero j
local notation "Φ" => P.labelled j

lemma unit_norm : ‖P.floorVec j‖ = 1 := vane P.run P.large P.law ..
lemma ground_norm : ‖P.groundZero j‖ = 1 := P.unit_norm j

instance floor_nontrivial : Nontrivial (P.Hil j) :=
  nontrivial_of_ne (P.floorVec j) 0 (norm_pos_iff.mp (by rw [P.unit_norm]; norm_num))
instance ground_nontrivial : Nontrivial (P.vacuum j) :=
  nontrivial_of_ne (P.groundZero j) 0 (norm_pos_iff.mp (by rw [P.ground_norm]; norm_num))

lemma occupied (s : ℕ) (f : P.Test) : inner ℂ ω (P.compressed j s f ω) = P.E s f.val :=
  Vacancy.inspected ..
lemma reflected (s : ℕ) (f : P.Test) : star (P.compressed j s f) = P.compressed j s (P.reflectTest j f) :=
  Vacancy.mirror_cap ..

/-- Every positive-side mark fits into a finite Entry with the SAME Family;
    no need to use decay bounds near the reflection plane. -/
lemma fits (s : ℕ) (x : P.Vox j s) : ∃ w : ℕ, 0 < w ∧
    ∃ f : P.Card j s w, f.val=x := by
  obtain ⟨h,_⟩ := (purpose_ok ..).1 x.property
  obtain ⟨S,u,p⟩ := (h : ∃ S : Finset Cover, InTest P.calibration true S false x.val ∧
    Tower.region j (meshface (Λ:=P.par) 0 s) P.calibration.ℓ S)
  have hp : ∀ i ∈ S, ∀ᶠ w : ℕ in atTop, i j+(P.calibration.ℓ:ℤ) ≤
      ruler P.par.block*w := by
    intro i _; let v : ℤ := i j+P.calibration.ℓ
    filter_upwards [eventually_ge_atTop v.toNat] with w k
    have h : v ≤ (w:ℤ) := by omega
    have h' : (w:ℤ) ≤ ruler P.par.block*w := le_mul_of_one_le_left (by positivity) (ruler_gene _)
    exact h.trans h'
  obtain ⟨w,a,b⟩ := ((eventually_gt_atTop (0:ℕ)).and ((S.eventually_all).mpr hp)).exists
  rw [area0] at p
  exact ⟨w,a,⟨x,S,u,fun i v=>⟨p i v,b i v⟩⟩,rfl⟩

/-- Box compression, a grid-aligned placement. -/
lemma compresses (s w : ℕ) (p : 0 < w) (f : P.Card j s w) :
    P.compressed j s (P.entryTest j s f) = (P.piZero j).comp
      ((P.Box j s w p f).comp (P.inHil j)) := by
  let h : Veranda P.run P.large s j false (P.obs (P.entryTest j s f)) :=
    ⟨0,w,p,f,(relocate_zero _ _ (test_entry ..)).symm⟩
  exact onAny P.run P.large P.law s P.history P.projection.clipped j false (P.room j) h
lemma seed (s : ℕ) (x : P.Vox j s) :
    P.compressed j s (P.voxTest j s x) ω = P.piZero j (P.piece j s x) := by
  obtain ⟨w,p,f,rfl⟩ := P.fits j s x
  rw [show P.voxTest j s f.val=P.entryTest j s f from rfl,P.compresses j s w p f]
  exact congrArg (P.piZero j) (SlabMark.lays P.run P.large P.law s P.history
    P.projection.clipped j false (P.room j) w f p)

lemma spanning : Dense (Submodule.span ℂ (Set.range (fun v=> Φ v ω)) : Set (P.vacuum j)) := by
  let W := Submodule.span ℂ (Set.range (fun v=> Φ v ω))
  let C := (show _root_.YM.Kernel.Gram _ from P.room j)
  have hh : DenseRange ((P.piZero j) ∘ C.stems) :=
    (show DenseRange _ from (show Surjective (P.piZero j) from
      fun x : P.vacuum j => ⟨x.val, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self x⟩).denseRange).comp C.whole (P.piZero j).continuous
  apply hh.mono; rintro _ ⟨a,rfl⟩; dsimp only [Function.comp_apply]
  change (P.piZero j) (C.stems a) ∈ W
  induction a using Finsupp.induction_linear with
  | zero => rw [map_zero,map_zero]; exact W.zero_mem
  | add p q hp hq => rw [map_add,map_add]; exact W.add_mem hp hq
  | single i c => rw [_root_.YM.Kernel.Gram.stems,Finsupp.linearCombination_single,map_smul]
                  apply W.smul_mem; apply Submodule.subset_span
                  exact ⟨(i.1,P.voxTest j i.1 i.2), P.seed j i.1 i.2⟩

lemma extGroundVector {x y : P.vacuum j} (h : ∀ v, inner ℂ (P.labelled j v ω) x =
    inner ℂ (P.labelled j v ω) y) : x=y := by
  apply Subtype.ext; apply all_voices P.run P.large P.history.circuit j 0 false _
  intro s a
  change inner ℂ (P.piece j s a) x.val = _
  have hp := h (s,P.voxTest j s a)
  change inner ℂ (P.compressed j s (P.voxTest j s a) ω) x =
    inner ℂ (P.compressed j s (P.voxTest j s a) ω) y at hp
  rwa [P.seed, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right] at hp
lemma extGroundOperator {D : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D]
    (T U : (P.vacuum j) →L[ℂ] D) (h : ∀ v, T (P.labelled j v ω)=U (P.labelled j v ω)) : T=U := by
  exact ContinuousLinearMap.ext_on (P.spanning j) (by
    rintro _ ⟨v,rfl⟩; exact h v)

lemma commutes (f g : ℕ × P.Test) : Commute (P.labelled j f) (P.labelled j g) := by
  apply P.extGroundOperator
  intro k; apply P.extGroundVector j; intro t
  change inner ℂ (Φ t ω) (Φ f (Φ g (Φ k ω))) = inner ℂ (Φ t ω) (Φ g (Φ f (Φ k ω)))
  let u := (t.1, P.reflectTest j t.2)
  have he : ContinuousLinearMap.adjoint (Φ t)= Φ u := P.reflected j t.1 t.2
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.adjoint_inner_right, he]
  let X (v : ℕ × P.Test) : Beacon P.calibration false := (v.1,P.obs v.2)
  let F : Fin 4→ Beacon P.calibration false := ![X u, X f, X g, X k]
  exact Vacancy.any_order P.run P.large P.law P.history P.projection.clipped j false
    (P.room j) F [0,1,2,3] [0,2,1,3] (by decide) (.cons _ (.swap ..))

abbrev GroundOp := (P.vacuum j) →L[ℂ] (P.vacuum j)
abbrev groundHil : Hilbert := { space := P.vacuum j }

-- As at Phase/Mixture: help typeclass inference through the Hilbert bundle
lemma hilbertTop (H : Hilbert) : IsTopologicalRing H.Op := inferInstance
instance : IsTopologicalRing (P.GroundOp j) := hilbertTop (P.groundHil j)
lemma hilbertStar (H : Hilbert) : ContinuousStar H.Op := inferInstance
instance : ContinuousStar (P.GroundOp j) := hilbertStar (P.groundHil j)

/-- Compression algebra, all rungs, ordinary operator star. -/
def compressionAlgebra : StarSubalgebra ℂ ((P.vacuum j)→L[ℂ] (P.vacuum j)) :=
  (StarAlgebra.adjoin ℂ (Set.range (P.labelled j))).topologicalClosure
abbrev Ensemble : Type := ↑(P.compressionAlgebra j)
instance closureC : IsClosed (P.compressionAlgebra j : Set ((P.vacuum j)→L[ℂ] (P.vacuum j))) :=
  isClosed_closure

instance ensembleAbelian : CommCStarAlgebra (P.Ensemble j) :=
  { StarSubalgebra.cstarAlgebra (P.compressionAlgebra j) with
    mul_comm := by
      let T:=StarAlgebra.adjoin ℂ (Set.range (P.labelled j))
      haveI : IsMulCommutative T:=StarAlgebra.isMulCommutative_adjoin ℂ (by
        rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩; exact P.commutes j x y) (by
        rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩
        unfold labelled; rw [P.reflected]; exact P.commutes j x (y.1,P.reflectTest j y.2))
      letI := T.commSemiringTopologicalClosure (fun x y=> IsMulCommutative.is_comm.comm x y)
      exact fun (x y:T.topologicalClosure)=> mul_comm x y }

/-- cap in the conditioning algebra. -/
noncomputable def preRead (v : ℕ × P.Test) : P.Ensemble j :=
  ⟨P.labelled j v, StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin _ _ (Set.mem_range_self v))⟩

lemma separating (b : P.Ensemble j) (zero : b.val (P.groundZero j)=0) : b=0 := by
  apply Subtype.ext; change b.val=0
  apply P.extGroundOperator j; intro v
  let u:=P.preRead j v
  change (b*u).val ω=0
  rw [mul_comm b]; change u.val (b.val (P.groundZero j))=0; rw [zero,map_zero]
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.separating
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.compresses
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.reflected
#check @YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.ensembleAbelian
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.ensembleAbelian
