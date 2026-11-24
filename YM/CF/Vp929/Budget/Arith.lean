import YM.CF.Vp929.Budget.Correction
import YM.CF.Roots.Seat
import YM.CF.Fixed.Voltage.Replica

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
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
open Ione Beau Haro Cascade Fixed.Voltage
open scoped Mew

variable {s : Side} {p : BudgetPoint} {j L : ℕ} {h a b : ℝ} {P Q : Corr s} {I : Interest s}
protected lemma Cost.mono (A : Cost p h a P) (q : a ≤ b) : Cost p h b P :=
  ⟨upgradeI _ _ A.inc q, upgradeD _ _ A.dark q⟩
protected lemma Charged.mono (A : Charged p I j L h a P) (q : a ≤ b) : Charged p I j L h b P :=
  { A with toCost := A.toCost.mono q }
lemma dark_smul {Q : Sweep s → Prop} {F : ForceBudget s} (A : Dark Q F p h a) (b : ℝ) : Dark Q (b • F) p h (|b| *a) := by
  obtain ⟨f,t,z⟩:= A.weight
  refine ⟨⟨|b| • f, ?_, fun x=>?_⟩, fun s S V B X W T p=>?_⟩
  · intro X; change ForceB p X (b • F X) h (|b| *f X)
    simpa only [Complex.norm_real, Real.norm_eq_abs, Complex.coe_smul] using Roots.dúe X (F X) (t X) (b:ℂ)
  · refine (mul_le_mul_of_nonneg_left (z x) (abs_nonneg b)).trans' (le_of_eq ?_)
    rw [mul_sum]; apply sum_congr rfl; intro i _; split <;> simp only [mul_zero, BudgetPoint.mass, Pi.smul_apply, smul_eq_mul] <;> ring
  simp only [Pi.smul_apply,map_smul,A.face s S V B X W T p]
protected lemma Cost.add (A : Cost p h a P) (B : Cost p h b Q) : Cost p h (a+b) (P+Q) :=
  ⟨Ione.addT p A.inc B.inc, cloudy p Utrue A.dark B.dark⟩
protected lemma Cost.smul (A : Cost p h a P) (c : ℝ) : Cost p h (|c| *a) (c • P) :=
  ⟨crestV _ _ A.inc _, dark_smul A.dark _⟩
abbrev potions (S : Finset (Scree.Hub s)) (M : Male) (j : ℕ) : RegBudget s →ₗ[ℝ] (Bloch.Momentum → Tap.Pal) :=
  { toFun := fun F=> Tap.potion j M (heroP (frame_P S F))
    map_add' := fun F G => by
      funext x
      rw [map_add]; unfold Tap.potion; rw [show heroP ((frame_P S) F+(frame_P S) G) x = heroP (frame_P S F) x + heroP (frame_P S G) x from ?_, mul_add,add_mul]; rfl
      apply eq_add_of_sub_eq; rw [← Exa.weights,add_sub_cancel_right]
    map_smul' := fun a F=> by
      funext x; rw [map_smul]; unfold Tap.potion; rw [coreF,Matrix.mul_smul,Matrix.smul_mul]; rfl }
protected lemma Charged.add (A : Charged p I j L h a P) (B : Charged p I j L h b Q) (hh : 0 ≤ h) :
    Charged p I j L h (a+b) (P+Q) := by
  refine ⟨A.toCost.add B.toCost, (Lord.merge ⟨A.inc,A.dawn⟩ hh ⟨B.inc,B.dawn⟩).theme, ?_⟩
  let Ψ:= potions (s:=s) (treeΘ p L) I.M j
  change Tap.NullW (Ψ (P.1+Q.1)); have hP : Tap.NullW (Ψ P.1) := A.warp; have hQ : Tap.NullW (Ψ Q.1) := B.warp
  rw [map_add]; refine ⟨by rw [Pi.add_apply,hP.still,hQ.still,add_zero], fun i=>?_⟩
  exact ((hP.free i).add (hQ.free i)).congr_deriv (add_zero _)
protected lemma Charged.smul (A : Charged p I j L h a P) (c : ℝ) (hh : 0 ≤ h) : Charged p I j L h (|c| *a) (c • P) := by
  refine ⟨A.toCost.smul c,(Lord.scale ⟨A.inc,A.dawn⟩ hh c).theme,?_⟩
  let Ψ:= potions (s:=s) (treeΘ p L) I.M j
  change Tap.NullW (Ψ (c • P.1)); have hP : Tap.NullW (Ψ P.1) := A.warp
  rw [map_smul]; refine ⟨by rw [Pi.smul_apply,hP.still,smul_zero], fun i=>?_⟩
  exact ((hP.free i).const_smul c).congr_deriv (smul_zero _)
protected lemma Cost.sub (A : Cost p h a P) (B : Cost p h b Q) : Cost p h (a+b) (P-Q) := by
  simpa [sub_eq_add_neg] using A.add (B.smul (-1))
protected lemma Charged.sub (A : Charged p I j L h a P) (B : Charged p I j L h b Q) (hh : 0 ≤ h) :
    Charged p I j L h (a+b) (P-Q) := by simpa [sub_eq_add_neg] using A.add (B.smul (-1) hh) hh
protected lemma Charged.zero : Charged p I j L h 0 (0:Corr s) := by
  refine ⟨⟨(Vale.lye Utrue p h).1,(Vale.lye Utrue p h).2⟩,fun _ _ _=> none_q _,?_⟩
  change Tap.NullW (potions _ I.M j (0:RegBudget s)); rw [map_zero]; exact ⟨rfl,fun i=>hasDerivAt_const ..⟩
protected lemma Cost.nonneg (A : Cost p h a P) (hh : 1 ≤ h) : 0 ≤ a := spent_E p P.1 A.inc hh
end YM.CF.Py.Rate
