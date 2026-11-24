import YM.CF.Fixed.MirrorFunctional
/-!
Slot inequalities in the manuscript are on bounded Borel tests using ONLY the single true gauge
link field in their kernel arguments; evaluated on `Phys` (matter action on `SU.Slot`). The marks
must be in the even subalgebra with *both* gauge link endpoints in the support, and fermion modes
at nodes there. This is NOT `Fixed.Probe`; continuity, gauge invariance, and restriction
to `Reed.Fine` are not part of the pressure estimate (the construction notes eq:num extended to
marks; VolumeD-sew lines 47–65 and 432–440; thm:B-main).
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress
open Function MeasureTheory Filter Finset Lattice SU Lat Cube Skye Scree Fixed Fock Scroll Dial
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
attribute [local instance] opCStarAlgebra
open Tulip
scoped instance opMeas (I:Type*) [Fintype I] [DecidableEq I] : MeasurableSpace (Op I) := borel _
scoped instance opBorel (I:Type*) [Fintype I] [DecidableEq I] : BorelSpace (Op I) := ⟨rfl⟩
variable {N : Side} (S : Support (More N)) (F : Fixed.Test N)

structure IsMark (C : ℝ) : Prop where
  reads : LocalOn S F
  even (U : Pane N) : Sector (matterRegion N S) false (F U)
  borel : Measurable F
  cost (U : Pane N) : ‖F U‖ ≤ C

namespace IsMark
variable {F} {D C : ℝ} {G : Fixed.Test N} {T : Support (More N)}
lemma one : IsMark S 1 1 := ⟨fun _ _ _ => rfl, fun _=>Sector.one, measurable_const,
    fun U=>by rw [Pi.one_apply,norm_one]⟩
lemma zero : IsMark S 0 0 := ⟨fun _ _ _=>rfl, fun _=> .zero _, measurable_const, by simp⟩
lemma sum {I : Type} (X : Finset I) (F : I → Fixed.Test N) (c : I → ℝ) (h : ∀ i∈X, IsMark S (F i) (c i)) :
    IsMark S (∑ i∈X,F i) (∑ i∈X,c i) := by
  classical
  induction X using Finset.induction_on with
  | empty=> simp only [sum_empty]; apply zero
  | @insert i s hi ih=>
    simp only [sum_insert hi]; let E:=h i (mem_insert_self ..); let D:=ih fun j hj=>h j (mem_insert_of_mem hj)
    exact ⟨fun _ _ p=>congrArg₂ (·+·) (E.reads _ _ p) (D.reads _ _ p),
      fun U=>(E.even U).add (D.even U), E.borel.add D.borel,
      fun U=>(norm_add_le ..).trans (add_le_add (E.cost U) (D.cost U))⟩
variable {S}
lemma nonneg (H : IsMark S F C) : 0 ≤ C := (norm_nonneg (F 1)).trans (H.cost 1)
lemma mul (E : IsMark S F C) (H : IsMark S G D) : IsMark S (F*G) (C*D) := by
  exact ⟨fun _ _ p=>congrArg₂ (·*·) (E.reads _ _ p) (H.reads _ _ p),
    fun U=>(E.even U).mul (H.even U), E.borel.mul H.borel,
    fun U=>(norm_mul_le ..).trans (mul_le_mul (E.cost U) (H.cost U) (norm_nonneg _) E.nonneg)⟩
lemma factor {c : Pane N → ℂ} (E : IsMark S F C) (p : LocalOn S c) (m : Measurable c)
    (b : ∀ U, ‖c U‖ ≤ D) : IsMark S (fun U=> c U • F U) (D*C) := by
  exact ⟨fun _ _ q=> congrArg₂ (fun (x:ℂ) (y:FC (Single N))=> x • y) (p _ _ q) (E.reads _ _ q),
    fun U=> (E.even U).scale _, m.smul E.borel,
    fun U=>by rw [norm_smul]; exact mul_le_mul (b U) (E.cost U) (norm_nonneg _) ((norm_nonneg _).trans (b U))⟩
lemma weaken (H : IsMark S F C) (e : S⊆T) (g : C ≤ D) : IsMark T F D := by
  refine ⟨fun _ _ p=> H.reads _ _ (agrees_mono p e), fun U=>?_, H.borel, fun U=>(H.cost U).trans g⟩
  have u : matterRegion N S ⊆ matterRegion N T := fun _ hh => (mem_matterRegion ..).mpr (e ((mem_matterRegion ..).mp hh))
  generalize hy : F U = R
  have hh : Sector (matterRegion N S) false R := hy ▸ H.even U
  -- generalize bit
  suffices ∀ (b) (F : FC (Single N)), Sector (matterRegion N S) b F → Sector (matterRegion N T) b F from this _ _ hh
  intro b F h
  induction h with
  | zero=> apply Sector.zero
  | one=> exact Sector.one
  | up _ h=> exact .up _ (u h)
  | down _ h=> exact .down _ (u h)
  | add _ _ ih it=> exact ih.add it
  | mul _ _ ih it=> exact ih.mul it
  | scale _ _ ih=> exact ih.scale _
lemma commute (H : IsMark S F C) (E : IsMark T G D) (h : Disjoint S T) : Commute F G := by
  have p : Disjoint (matterRegion N S) (matterRegion N T) := disjoint_left.mpr fun i x y=>
    disjoint_left.mp h ((mem_matterRegion ..).mp x) ((mem_matterRegion ..).mp y)
  exact funext fun U : Pane N => ((H.even U).apart (E.even U) p).trans (one_smul ℂ _)

variable {I : Type*} (F' : I → Fixed.Test N) (c : I → ℝ)
lemma list_product (p : List I) (h : ∀ i ∈ p, IsMark S (F' i) (c i)) :
    IsMark S (p.map F').prod (p.map c).prod := by
  induction p with
  | nil => apply one
  | cons i p ih => exact (h i (by simp)).mul (ih fun j hj=> h j (by simp [hj]))
end IsMark

section numer
open Paige Peaks Vault Wilson
variable {S F} {C : ℝ} {u : Orbit N → Phys N}

def integrand (F : Fixed.Test N) (u : Orbit N → Phys N) (y : Orbit N) : ℂ := beamZ N (acts (F y.1) (u y))

lemma integrable {N : Side} {S : Support (More N)} {F : Fixed.Test N} {u : Orbit N → Phys N}
    (E : IsMark S F C) (H : Integrable u (city N)) : Integrable (integrand F u) (city _) := by
  let f := fun z : FC (Single N) × Phys N => beamZ N (acts z.1 z.2)
  have hf : Continuous f := continuous_const.inner ((acts_cont.comp continuous_fst).clm_apply continuous_snd)
  have e : AEStronglyMeasurable (fun z : Orbit N=> (F z.1, u z)) (city N) :=
    ((E.borel.comp measurable_fst).aestronglyMeasurable (μ:=city N)).prodMk H.1
  change Integrable (f ∘ (fun z : Orbit N=> (F z.1, u z))) (city N)
  refine Integrable.mono' (H.norm.const_mul (‖mateK N‖ * C))
    (hf.comp_aestronglyMeasurable e)
    (Eventually.of_forall fun z=>?_)
  refine (norm_inner_le_norm ..).trans ?_
  rw [mul_assoc]; refine mul_le_mul_of_nonneg_left ((ContinuousLinearMap.le_opNorm ..).trans
    (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))) (norm_nonneg _)
  refine le_trans (le_of_eq ?_) (E.cost z.1)
  exact Matrix.l2_opNorm_toEuclideanCLM _

variable {m B L:Side} {j:ℕ} {ho: Odd L.val} {Y:Pricing j L ho (Thread j)} {d:ℝ}
variable (U:Grasp Y B d) (V:GramM (mid m B)) (W:Loom (mid m B))
open NormedSpace in
lemma strip (z : Orbit (mid m B)) : Fixed.rescaleOffset U V W z =
    Complex.exp (-(↑(V.path.inChannels V.funds V.p V.beta z.1) : ℂ) - Pec.pigment V.J.I (W z)) •
    acts (tank (spar j V.J.M (W z)) (V.board z)) (relV U V.J (W z)) := by
  rw [rescaleOffset,Pi.smul_apply,denZ,smul_smul,←Complex.exp_add,GramM.betaL,GramM.H0]; congr 2; abel

def reading : Fixed.Test (mid m B) → ℂ := Fixed.functional (Fixed.rescaleOffset U V W)

lemma reading_apply (T : Fixed.Test (mid m B)) : reading U V W T =
    ∫ y : Orbit (mid m B), integrand T (Fixed.rescaleOffset U V W) y
      ∂((prior SU.group (More (mid m B))).prod (depot (mid m B))) := rfl
lemma reading_eq (T : Fixed.Test (mid m B)) : reading U V W T =
    Complex.exp (-V.v) * Fixed.numerator U V W T := Fixed.functional_scale ..
lemma reading_one : reading U V W 1= Fixed.scaledZ U V W := Fixed.scaledZ_one ..
lemma reading_integrable {S : Support (More (mid m B))} {F : Fixed.Test (mid m B)}
    (h : Integrable (denZ V U W) (city _)) (p : IsMark S F C) :
    Integrable (integrand F (Fixed.rescaleOffset U V W)) (city _) := integrable p (h.smul _)
end numer
end YM.CF.BPress
