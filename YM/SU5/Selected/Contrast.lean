import YM.SU5.Selected.Single
import Mathlib.Analysis.CStarAlgebra.GelfandDuality

/-!
# Survival estimate in the spectrum of the compressed algebra

Test only the physical-resolution interaction `Parcel` of the question: in the extension
with fixed observable assignments and indicated local gauge symmetry, not a claim about curvature
alone, not a witness distinguishing dynamics in all possible changes of variables (could also
detect correlations from gauging/blocking), not excluding purely gauge-frame correlations
of independently dressed fields, not S-matrix interaction. But **not** just a connected
reading in the presence of unknown ground state degeneracy: because we use the
charged slices and conditioning on this tower we can obtain nonvanishing read estimates using only the same compression data.
Work with ℂ-valued state on the resolution test algebra; asking if it factors on those
gauge × matter choices. The original `F` (uniform lower estimate) is a neutral composite,
on the original first links with continuous coefficient. We also pay a *specific*
positive estimate (possibly smaller) on a monomial of the Parcel form in its Filigree
space. Not claiming that the gauge and matter factors, or that second product, are
separately gauge neutral: this comparison uses the covariant **extension**.

This file just purchases the detection set and proves it is nonempty even on pure
characters of the compression C⋆-algebra. By itself this does **NOT** pay for selection of
an ergodic spacetime state (rank one joint ground): that comparison has to use the uncompressed
fields too. So intentionally leave the points satisfying the **strict** > 1/8 estimate as
a whole open set here, in the actual compression spectrum topology.
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
namespace Spine
variable (P : Spine) (j : Axis)

variable (s : ℕ)
local notation "K" => P.calibration
open WeakDual CF.Pannier.Chancel
local notation "ω" => P.groundZero j
abbrev Spectrum0 : Type := characterSpace ℂ (P.Ensemble j)
-- Give function to avoid uniform space inference issues.
noncomputable def chi (x : P.Spectrum0 j) : P.Ensemble j →⋆ₐ[ℂ] ℂ :=
  (ContinuousMap.evalStarAlgHom ℂ ℂ x).comp
    (gelfandStarTransform (P.Ensemble j): P.Ensemble j →⋆ₐ[ℂ] C(P.Spectrum0 j,ℂ))
lemma chi_eval (x : P.Spectrum0 j) (T : P.Ensemble j) :
    P.chi j x T= (gelfandStarTransform (P.Ensemble j) T) x := rfl
lemma chi_joint (T : P.Ensemble j) : Continuous (fun x=> P.chi j x T) :=
  (gelfandStarTransform (P.Ensemble j) T).continuous
lemma chi_all (T : P.Ensemble j) (h : ∀ x, P.chi j x T=0) : T=0 :=
  (gelfandStarTransform (P.Ensemble j)).injective (by rw [map_zero]; exact ContinuousMap.ext h)
lemma chi_one_top (T : P.Ensemble j) {a : ℝ} (p : 0<a) (h : a ≤ ‖T‖) :
    ∃ x : P.Spectrum0 j, a ≤ ‖P.chi j x T‖ := by
  by_contra! hz
  have ht: Isometry (gelfandStarTransform (P.Ensemble j)):=gelfandTransform_isometry (P.Ensemble j)
  exact ((ht.norm_map_of_map_zero (map_zero _) T) ▸ ((ContinuousMap.norm_lt_iff _ p).mpr hz) : ‖T‖ < a).not_ge h
lemma detects_original (f : P.Test) : ‖P.E s f.val‖ ≤ ‖P.reading j s f‖ := by
  rw [←P.occupied j s]; apply le_trans (norm_inner_le_norm ..)
  rw [P.ground_norm,one_mul]; exact le_trans (ContinuousLinearMap.le_opNorm ..) (by rw [P.ground_norm,mul_one]; exact le_of_eq rfl)
-- Set values also at off-test arguments only because `Parcel` takes `Family → ℂ`. **No**
-- claim off the algebra.
variable (x : P.Spectrum0 j)
def singleState : P.Test →ₗ[ℂ] ℂ := (P.chi j x).toLinearMap ∘ₗ P.reading j s
lemma single_state (f : P.Test) : P.singleState j s x f=P.chi j x (P.reading j s f):=rfl
def persona (F : Family P.calibration) : ℂ := if h : TestFamily P.calibration true F then
  P.singleState j s x (show P.Test from ⟨F,h⟩) else 0
lemma personality (f : P.Test) : P.persona j s x f.val=P.singleState j s x f:= dif_pos f.property
abbrev art (F : Family K) (h : TestFamily K true F) : P.Test := ⟨F,h⟩

lemma represents (S : Finset Cover) : Scopes K S (P.persona j s x) := by
  let E':=P.persona j s x
  refine ⟨?_,fun f g p q=>?_,fun f p z=>?_,fun t f F p u v=>?_⟩
  · change E' (1:P.Test).val=1; unfold E'; rw [P.personality,P.single_state,P.reading_unit,map_one]
  · let x':=P.art f (aux_test p); let y:=P.art g (aux_test q)
    change E' (x'+y).val= E' x'.val+E' y.val
    simp_rw [E',P.personality,map_add]
  · let a:=P.art f (aux_test p)
    change E' (z • a).val=z • E' a.val
    simp_rw [E',P.personality,map_smul]
  let a:=P.art f (aux_test p); let b:=P.art F (aux_test u)
  change E' a.val=E' b.val
  rw [show b=pennant K t a from (appointed K S t a b v u).symm]
  simp_rw [E',P.personality,P.single_state,P.reading_gauge]

def opening (f : P.Test) : Set (P.Spectrum0 j) := {x | 1/8 < ‖P.singleState j s x f‖}
lemma aperture (f : P.Test) (h : 1/4 ≤ ‖P.E s f.val‖) : IsOpen (P.opening j s f) ∧
    (P.opening j s f).Nonempty := by
  obtain ⟨x,p⟩:= P.chi_one_top j (P.reading j s f) (by norm_num : (0:ℝ)<1/4) (h.trans (P.detects_original j s f))
  refine ⟨(P.chi_joint j _).norm.isOpen_preimage _ isOpen_Ioi, x,?_⟩
  exact lt_of_lt_of_le (by norm_num : (1:ℝ)/8<1/4) p

variable {m : ℕ} (b : Fin m→ Cover) (S : Finset Cover) (z : SU.Slot)
local notation "L" => Lode P.calibration (Window.family z) b S
local notation "M" => Filigree P.calibration (Window.family z) b S
lemma erased (p : Injective b) (f : P.Test) (t : f.val∈ L) : P.reading j s f=0 := by
  apply P.chi_all j; intro x
  rw [← P.single_state, ← P.personality]; exact (P.represents j s x S).footprint p t
/-!
Because the pure matter reading on these tomes vanishes *as a compressed operator*,
there is no spurious failure of Parcel from mixing-vacua correlations. Even
at the level of expectations of products of compressed operators with ONE such
pure matter factor of a mixed tome, the products vanish. In particular they are NOT
in general equal to the compressed operators for the original products. -/
lemma erases_product (p : Injective b) (f g : P.Test) (t : g.val∈ L) :
    P.compressed j s f * P.compressed j s g = 0 := by rw [← P.at_label j s g,P.erased j s b S z p g t]; exact mul_zero _

/-- Quantitative nonfactorization supported in one gauge-matter-resolution experiment.
    Asks both about `Parcel` and about compression of the test-level product. -/
structure Retained (f : P.Test) : Prop where
  marked : f.val∈ M
  public_ : f.val∈ observ K S false
  mixed : 1/8 < ‖P.singleState j s x f‖
  fails : ¬CF.Pannier.Chancel.Parcel K (Window.family z) b S (P.persona j s x)
  signal : ∃ (F B : P.Test), (∃ w : PairsC→ℂ, Coeff false S w ∧ F.val = Buffered.scalar K w) ∧
    B.val∈ L ∧ P.reading j s B=0 ∧ (F*B).val ∈ M ∧
    ∃ c : ℝ, 0 < c ∧ c ≤ ‖P.singleState j s x (F*B)- P.singleState j s x F * P.singleState j s x B‖ ∧
      c ≤ ‖P.chi j x (P.reading j s (F*B)-P.reading j s F* P.reading j s B)‖
lemma retention (p : Injective b) (f : P.Test) (h : f.val∈ M) (q : f.val∈ observ K S false)
    (t : x∈P.opening j s f) : P.Retained j s x b S z f := by
  change 1/8 < ‖P.singleState j s x f‖ at t
  have hp : ¬ CF.Pannier.Chancel.Parcel K (Window.family z) b S (P.persona j s x) :=by
    intro u; rw [← P.personality, (P.represents j s x S).detects p u h,norm_zero] at t; norm_num at t
  refine ⟨h,q,t,hp,?_⟩
  rw [CF.Pannier.Chancel.Parcel] at hp
  -- choose indicated factors, then an actual positive number c. Don't require any
  -- uniformity in changing support at the new resolution.
  push Not at hp
  obtain ⟨G,t,w,p',u⟩:= hp
  let B:= P.art G (aux_test (Lode_test t|>.widen))
  let F:= P.art (Buffered.scalar K w) (aux_test ((InTest.seed p').widen))
  change P.persona j s x (F*B).val ≠ P.persona j s x F.val * P.persona j s x B.val at u
  simp_rw [P.personality] at u
  refine ⟨F,B,⟨w,p',rfl⟩,t,P.erased j s b S z p B t,
    Submodule.subset_span (s:={v| ∃ (x:Family K) (z:PairsC→ℂ), x∈ L ∧ Coeff false S z∧ v=Buffered.scalar K z*x})
      ⟨G,w,t,p',rfl⟩,_, norm_pos_iff.mpr (sub_ne_zero.mpr u),le_rfl,(le_of_eq ?_)⟩
  rw [map_sub,map_mul (P.chi j x)]; rfl

end Spine
open CF.Pannier.Chancel FixedProbe
/-- A checkpoint: singles **and** separation and product failure on the specified ground law,
    for a nonempty open set of characters of its actual compression algebra on the chosen
    axis. Not yet claiming to have selected an ergodic component (some/all characters in
    that set could need this check). -/
theorem projection_test (ε η : ℝ) (p : 0<η) (z : SU.Slot) (o : Cover) :
    ∃ P : Spine, P.par.nominated (VolumeCape.Dream.Nimbus P.width) ∧ ε<P.par.x ∧ P.par.d ≤ η ∧
    ∃ (Z C : ℝ) (q d w s N : ℕ), Papal.Cornet P.run P.large q d w C Z ∧
    let S := Sen o (payout d q w); let b:=booty o d q
    ∃ (F : FixedProbe.KernelTest P.run P.large) (f : P.Test), f.val=F.val ∧
      FixedProbe.AnchorGap (Λ:=P.par) s b S ∧ Carries P.run P.large P.law s P.projection F S N ∧
      1/4 ≤ ‖P.E s F.val‖ ∧ ∀ j : Axis, IsOpen (P.opening j s f) ∧ (P.opening j s f).Nonempty ∧
        ∀ x∈ P.opening j s f, P.Retained j s x b S z f := by
  obtain ⟨Λ,l,Z,large,bound,nom,H,Y,q,d,w,C,g,a,k,I,E,V,⟨G⟩,_⟩:=
    Papal.mixed_law_with_ground ε η p
  let P:Spine:=⟨Λ,l,Y,H,a,k,I,E,V,G⟩
  let S := Sen o (payout d q w); let b:=booty o d q
  obtain ⟨s,F,N,u,v,h,t⟩:= (FixedProbe.current Y H V G g z o).exists
  let f := P.art F.val F.property.1
  refine ⟨P,nom,large,bound,Z,C,q,d,w,s,N,g,F,f,rfl,u,h,t,fun j=>?_⟩
  obtain ⟨a,r⟩:= P.aperture j s f t
  exact ⟨a,r,fun x p=> P.retention j s x b S z (g.cents o) f v h.firstPane p⟩

end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#check @YM.CF.Buffered.Afterglow.Tower.VacuumSelection.projection_test
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.projection_test
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.erases_product
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.erased
