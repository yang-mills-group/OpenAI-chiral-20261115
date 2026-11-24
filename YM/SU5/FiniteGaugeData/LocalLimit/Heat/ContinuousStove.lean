import YM.CF.Vp929.Stage.Plant
import YM.CF.Ups.Lush

/-!
# Dominated continuity on one torus pair

Before determining the wave. Uses only physical input continuity, and permits
continuous tests of the (candidate, not solved) wave.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Girt Pyx
namespace LocalLimit
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
variable {d : ℝ} {m n B : Side} {U : Grasp V.U B d}
  {x r b C c ε : ℝ} {q : Chi} (G : Ratio (mid m B) (mid n B))
  (F₁ : Scree.Loom (mid m B)) (F₂ : Scree.Loom (mid n B))
  (S : StepData (Domain m B) (Domain n B))
  (hs : S.ratio=ratio G) (H : S.patch.Branches S.kernel SU.group)
local notation "D" => mid n B
local notation "Ω" => mid m B
local notation "μ" => city (mid n B)

include hs H
lemma continuous_stove {T : Type*} [TopologicalSpace T] [FirstCountableTopology T]
    (Z : T → GramM D) (W : T → SpaceM) (hu : ∀ t, Nonempty (BaseL U G (Z t) F₁ F₂ q ε))
    (hc : ∀ t y, ‖denZ (Z t) U F₂ y‖ ≤ C)
    (hp : ∀ᵐ y ∂ city (mid n B), Continuous fun t=> denZ (Z t) U F₂ y)
    (hβ : Continuous fun t=> (Z t).beta) (hw : Continuous W)
    (hbr : ∀ t, |(Z t).beta| ≤ b) (hwr : ∀ t, ‖W t‖ ≤ r) (y : Orbit Ω) :
    Continuous fun t => stove U F₁ (Z t) F₂ G S q ε (W t).val y := by
  let A(t:T) := Fps (j:=K.j) G F₁ F₂ q ε S (Z t).beta (W t) y
  let I(t:T) := integrated U F₁ (Z t) F₂ G S q ε (W t).val y
  have hi t z : I t z = A t z (denZ (Z t) U F₂ z) := by simpa only [one_smul] using
    (Fps_path (R:=Z t) G F₁ F₂ q ε S y z U (W t) 1).symm
  cases isEmpty_or_nonempty T
  · exact continuous_iff_continuousAt.mpr fun t=> isEmptyElim t
  let z : T := Classical.arbitrary _
  let Z' := Classical.choice (hu z)
  have hr : 0 ≤ r := (norm_nonneg _).trans (hwr z)
  obtain ⟨K',HK⟩ := earn_ps U G F₁ F₂ q ε Z' S hs H y b r hr
  let D' := K'+|K'|
  have he : 0 ≤ D' := by dsimp only [D']; linarith [neg_le_abs K']
  change Continuous fun t=> ∫ z,I t z ∂μ
  apply continuous_of_dominated (bound:=fun _=> D'*C) ?_ ?_ (integrable_const _) ?_
  · intro t
    let f := Girt.buoy (Classical.choice (hu t)) S hs H (W t).val
    exact (f.meas.comp (measurable_const (a:=y)|>.prodMk measurable_id)).aestronglyMeasurable
  · intro t; apply Eventually.of_forall; intro i
    rw [hi]; refine ((A t i).le_opNorm ..).trans (mul_le_mul ((HK _ (hwr t) _ (hbr t)).2 i|>.trans (le_add_of_nonneg_right (abs_nonneg _))) (hc t i) (norm_nonneg _) he)
  exact hp.mono fun i p=> (((color_ps U G F₁ F₂ q ε Z' S hs H y i).comp (hβ.prodMk hw)).clm_apply p).congr fun t=> (hi t i).symm

end LocalLimit
end YM.CF.Py.Rate
