import YM.CF.Pso.Plight
import YM.CF.Pso.Fume
import YM.CF.Ione.Lean
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Trails
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Links
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Ione
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}
open Vow Salt
variable (P:BudgetPoint)(s:Sweep n)
local notation "Ta"=> actY s
local notation "HQ"=> (hail_Q s).val
local notation "Φg"=> (Finset (Dwell n))
open Vow Larch
open Bake Lilt Rue Trees
variable (E:Pax n)(F:Pax n)(K:Cusp n)
local notation "T0"=> Sweep n
local notation "Γ"=> (plight_C n)
local notation "Hz"=> Scree.Hub n
local notation "B'"=> P.B
local notation "P'"=> (P.supportExponent+1+1)
variable {C:Type}[TopologicalSpace C] (i: Aura n)
variable (Z1 Z2:C→ Pax n)(A:Seat n)
variable (τ:Ids n) (V:Orbit n) (T: C → RegBudget n)(L: C → Cusp n) (p2:PointF Z2)(p:PointF Z1)
local notation "E1" z:max=> FeeD P (Z1 z)
local notation "UΠ" z:max=> curr_X P (Z2 z) (Z1 z) (1,τ)
local notation "Ω" z:max=> curr_r P (Z2 z) (Z1 z) (1,τ)
variable (A1:C→Aura n→ℝ){γ:ℝ}(t:C→ℝ)(hp1:1 ≤ h)
variable (hg: ∀ k, Ready Palot.stern P.B (A1 k) (P.supportExponent+1+1) γ 1 (degreePrice P.B γ 1)) (pK:∀ k,∀ i,Medal P i.val ∅ (Z1 k i) h (A1 k i))
variable (hg':0 ≤ degreePrice P.B γ 1)(hx:degreePrice P.B γ 1 <1)
include p2 p hp1 hg pK hg' hx
lemma off_u: let F(k):=writ_E (T k)+cast_E (UΠ k) τ;
           PointK L→(∀ x:Scree.Hub n,∀ i:Pane n,Continuous (fun z=>T z x i))→ PointK (fun z=>writ_K (L z)+nextE (Ω z)) ∧ ∀ x:Scree.Hub n,∀ i:Pane n,Continuous (fun z=> F z x i):=by
 intro F v t0; have he:= lore_B Z1 P hp1 (fun i k _=>p i k) A1 (by linarith [P.exponent_pos] : 0 ≤ P.supportExponent+1+1) hg pK hg' hx
 have hj(i:Aura n)(y:Orbit n):Continuous fun z:C=> vault_Z ((FeeD P (Z1 z) i y)-(Z2 z i y)):=by
    let F(x:Cipher n):= vault_Z x; exact (Complex.continuous_re.comp (continuous_subtype_val.matrix_elem ∅ ∅)).comp ((he i y).sub (p2 i y)) -- v shadow
 have ht(i:Aura n):Continuous (fun z:C=>curr_r P (Z2 z) (Z1 z) (1,τ) i):=by
    unfold curr_r Mat_R; simp_rw [Pi.smul_apply,Finset.sum_apply, zeal_F]; exact ((continuous_finsetSum univ (fun s (_:s ∈ (univ:Finset (Sweep n)))=> hj (moldA s i) (1,τ))).const_smul (plight_C n))
 have hn:PointF (fun z:C=>curr_X P (Z2 z) (Z1 z) (1,τ)):=by
    intro i y; unfold curr_X zenS; dsimp only; split; swap; · exact continuous_const
    exact (((he i y).sub (p2 i y)).sub ((ht i).smul continuous_const))
 constructor
 · intro i D y; simp_rw [Pi.add_apply,writ_K,Pi.smul_apply,Finset.sum_apply]; apply Continuous.add _ ((ht i).smul continuous_const|>.neg); refine Continuous.const_smul (g:=fun z:C=> ∑ j:Sweep n,force_V j (L z) i D y) (continuous_finsetSum _ (fun j _=>?_)) (plight_C n); unfold force_V turn_V; exact (suit_Y j⁻¹).toLinearMap.continuous_of_finiteDimensional.comp (v _ _ _) -- tune N
 intro i y; unfold F; simp_rw [Pi.add_apply,writ_E, Pi.smul_apply,Finset.sum_apply]; refine Continuous.add (Continuous.const_smul (g:=fun z:C=> ∑ j:Sweep n, base_Q j (T z) i y) (continuous_finsetSum _ (fun j _=>?_)) (plight_C n)) (Continuous.const_smul (hn (lagE i) (y,τ)) (bassH (lagE i))) -- tune
 exact (suit_Y j⁻¹).toLinearMap.continuous_of_finiteDimensional.comp (t0 _ _)
end YM.CF.Ione
