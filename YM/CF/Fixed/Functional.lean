import YM.CF.Fixed.MirrorFunctional
import YM.CF.Fixed.Pass

/-!
The same state in all entries, conjugate-linear in the first polynomial
and linear in the second for the reflected product. (Complex convention is
proved for the actual complex readings.) Analytic integrability is independent
of a mass estimate on normalized ratios.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 220000
noncomputable section
namespace YM.CF.Fixed
open Function NormedSpace Filter Metric Finset Lattice Wilson Cube MeasureTheory Spire
open SU Lat Fock Scroll Tulip Skye Scree RG Dial
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology
attribute [local instance] opCStarAlgebra

variable {N : Side}

lemma integrable_functional {F : Orbit N→ Phys N} (H: Integrable F (city N)) (X: Test N) (K:Continuous X) :
    Integrable (fun i: Orbit N=> beamZ N (acts (X i.1) (F i))) (city N) := by
  let f : Pane N → Phys N →L[ℂ] ℂ := fun i => (innerSL ℂ (mateK N)).comp (acts (X i))
  have he : Continuous f:= continuous_const.clm_comp (acts_cont.comp K)
  obtain ⟨C,hC⟩:= (isCompact_range he.norm).bddAbove
  have h (x):‖f x‖≤C:= hC (Set.mem_range_self _)
  apply Integrable.mono' (H.norm.const_mul C) ?_ ?_
  · have ht : Continuous (fun x : Pane N × Phys N => f x.1 x.2) := (he.comp continuous_fst).clm_apply continuous_snd
    have hu:AEStronglyMeasurable (fun v:Orbit N=>(v.1,F v)) (city N):=(show Measurable (fun x:Orbit N=> x.1) from measurable_fst).aestronglyMeasurable.prodMk H.aestronglyMeasurable
    change AEStronglyMeasurable ((fun z : Pane N × Phys N=> (f z.1) z.2) ∘ (fun i:Orbit N=>(i.1,F i))) (city N)
    exact ht.comp_aestronglyMeasurable hu
  apply Eventually.of_forall
  intro x
  exact ((f _).le_opNorm (F x)).trans (mul_le_mul_of_nonneg_right (h x.1) (norm_nonneg _))

section
open Paige Peaks Vault
variable {m B L:Side} {j:ℕ} {ho: Odd L.val} {Y:Pricing j L ho (Thread j)} {d:ℝ}
local notation "N_"=> mid m B
variable (U:Grasp Y B d) (V:GramM (mid m B)) (F:Loom (mid m B))
lemma functional_normalized (X : Test (mid m B)) :
    functional ((partitionZ V U F)⁻¹ • denZ V U F) X = evalNormalized U V F X := by
  rw [functional_scale,evalNormalized,numerator,div_eq_mul_inv,mul_comm]
end

section axioms
/-- Internal finite-test-layout (no claim of spacetime/cutoff limit).
Separation, locality and gauge invariance reside in `probes`; use a single W
across all its local subalgebras including mixed tests. -/
structure Normalized (W: Test N→ ℂ) : Prop where
  unit : W 1=1
  plus(X Y:Test N)(hX:Probe X)(hY:Probe Y):W (X+Y)=W X+W Y
  times(X:Test N)(c:ℂ)(h:Probe X):W (c•X)= c*W X

lemma functional_zero (F: Orbit N→Phys N) : functional F 0=0:=by unfold functional; simp [beamZ]
lemma functional_cash (F:Orbit N→Phys N) (X:Test N) (c:ℂ) : functional F (c•X)= c*functional F X:=by
  unfold functional; simp_rw [Pi.smul_apply, act_smul, beamZ, inner_smul_right]; exact integral_const_mul ..
lemma functional_add (F: Orbit N→Phys N)(h:Integrable F (city N)) (X Y:Test N) (p:Continuous X)(q:Continuous Y) :
    functional F (X+Y)=functional F X+functional F Y:=by
  unfold functional; simp_rw [Pi.add_apply, act_add, beamZ, inner_add_right]; exact integral_add
    (integrable_functional h X p) (integrable_functional h Y q)
lemma functional_normal (F:Orbit N→ Phys N) (h:Integrable F (city N)) (e:functional F 1=1): Normalized (functional F):=
  ⟨e,fun X Y hX hY=> functional_add F h X Y ((show InRegion (univ:Support (More N)) false X from hX).cont) ((show InRegion (univ:Support (More N)) false Y from hY).cont), fun X c _=> functional_cash F X c⟩

section
open Paige Peaks Vault
variable {m B L:Side} {j:ℕ} {ho:Odd L.val} {Y:Pricing j L ho (Thread j)} {d:ℝ}
local notation "N_" => mid m B
variable (U:Grasp Y B d) (V:GramM (mid m B)) (F:Loom (mid m B))
lemma equiv_normalized (e:Integrable (denZ V U F) (city N_)) :
    Normalized (evalNormalized U V F) ↔ partitionZ V U F≠0 := by
  constructor
  · intro A h
    have p:=A.unit; unfold evalNormalized at p; rw [h,div_zero] at p; exact zero_ne_one p
  intro p
  rw [show evalNormalized U V F=functional ((partitionZ V U F)⁻¹ • denZ V U F) from funext fun X => (functional_normalized U V F X).symm]
  apply functional_normal _ (e.smul (partitionZ V U F)⁻¹)
  rw [functional_normalized,evalNormalized,numerator_one,div_self p]
end

lemma probe_reflect_product (i) {F G:Test N}(h:Probe F)(k:Probe G): Probe (reflectTest i false F*G) :=
  (probes _).mul_mem (probe_reflect i h) k

lemma probe_sum {I:Type*} {F:I→Test N} (H:Finset I) (p:∀ i,Probe (F i)) : Probe (∑ i∈H,F i) :=
  Subalgebra.sum_mem _ (fun i _=>p i)
lemma probe_cash {F:Test N} (c:ℂ) (p:Probe F) : Probe (c • F) :=
  Subalgebra.smul_mem _ p _
lemma positive_cash {F:Test N}(i)(c:ℂ)(p:PositiveTest i F): PositiveTest i (c • F):=
  Subalgebra.smul_mem _ p _
lemma positive_sum {I:Type*} (i:Axis) (X: Test N→ Prop) (h:X=PositiveTest i)(H:Finset I)(F:I→ Test N)(p:∀ j,X (F j)) : X (∑ j∈H,F j):=by
  subst X; exact Subalgebra.sum_mem _ (fun j _=>p j)
variable {W:Test N→ ℂ} (h: Normalized W) {I:Type*}
namespace Normalized
include h
lemma zero : W 0=0:=by have e:= h.times 1 0 (Subalgebra.one_mem _); simpa using e
lemma sum (T : Finset I) (F:I→ Test N) (p: ∀ i, Probe (F i)) :W (∑ i∈T,F i)=∑ i∈T,W (F i) := by
  classical
  induction T using Finset.induction_on with
  | empty=> simp [zero h]
  | insert i T w ih=> rw [sum_insert w,sum_insert w, h.plus _ _ (p i) (probe_sum T p),ih]
end Normalized
lemma reflectTest_zero (i : Axis) (b : Bool) : reflectTest (N:=N) i b 0=0:=by funext V; simp [reflectTest,Reed.reverseW,Fock.theta_zero]
lemma reflectTest_sum (i : Axis) (b : Bool) (F:I→Test N)(S:Finset I) :
    reflectTest i b (∑ i∈S,F i)=∑ i'∈S, reflectTest i b (F i') := by
  classical
  induction S using Finset.induction_on with
  | empty=> simp [reflectTest_zero]
  | insert j T t ih => rw [sum_insert t,sum_insert t,reflectTest_add, ih]

include h
lemma gram_sum_equiv [Fintype I] (i:Axis) (F : I→ Test N)(p:∀ j,Probe (F j)) (x:I→ℂ) :
    W (reflectTest i false (∑ t,x t • F t) * (∑ t,x t • F t))=
      dotProduct (star x) ((gram i W F).mulVec x) := by
  classical
  let U : I→ Test N:= fun t=> reflectTest i false (x t • F t)
  rw [reflectTest_sum,Finset.sum_mul]
  change W (∑ t,U t * ∑ z,x z • F z) = _
  have he : Probe (∑ t,x t • F t):=probe_sum univ (fun t=>probe_cash (x t) (p t))
  rw [h.sum univ (fun t=>U t * ∑ z,x z•F z) (fun t=>probe_reflect_product i (probe_cash (x t) (p t)) he)]
  unfold dotProduct Matrix.mulVec; apply sum_congr rfl; intro t _
  rw [Finset.mul_sum, h.sum univ _ (fun j=>probe_reflect_product i (probe_cash _ (p t)) (probe_cash _ (p j)))]
  unfold dotProduct; rw [Finset.mul_sum]; apply sum_congr rfl; intro j _
  rw [reflectTest_smul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul, h.times _ _ (probe_reflect_product i (p t) (p j))]; change _ = star (x t)*(W _*x j); ring

open scoped ComplexOrder
lemma gram_of_positive [Fintype I] (i:Axis) (F:I→Test N) (p:∀ j, PositiveTest i (F j))
    (q:∀ f:Test N,Probe f → W (reflectTest i false f)=star (W f))
    (v:∀ f:Test N, PositiveTest i f → 0≤ W (reflectTest i false f*f)): (gram i W F).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  have ht:∀ j, Probe (F j):=fun j=> positive_to_probe i (p j)
  exact ⟨gram_hermitian i F ht q,fun x=> by rw [← gram_sum_equiv h i F ht x]; exact v _ (positive_sum i _ rfl _ _ (fun j=>positive_cash i _ (p j)))⟩

end axioms
end YM.CF.Fixed
