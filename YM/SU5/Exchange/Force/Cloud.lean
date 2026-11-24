import YM.CF.Stax.Flow
import YM.CF.Vow.Year
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Vow
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

-- Authored extension of Fair.enough_v. Retain radius even after
-- reconstruction from opaque inputs W when the nonzero premise is paid.
open Rue Trees
lemma wholeHalo (δ:ℕ) (K W:Cusp n)
 (u : ∀ (X:Aura n), ∀ D⊆X.val, Stax.Lives P δ X D (K X D))
 (X:Aura n) (D:Support (More n)) (l:D⊆X.val) : Stax.Lives P δ X D (glowV K W X D):=by
 intro V h
 unfold glowV mintF at h; rw [if_pos l, Finset.sum_apply] at h
 obtain ⟨T,-,p⟩:=exists_ne_zero_of_sum_ne_zero h
 rw [gear_v] at p
 split at p; swap; · exact False.elim (p rfl)
 rename_i v
 have he(j:Aura n)(t:j∈T.toLeft) : halo δ (D∩j.val) ⊆ j.val ∧ D∩j.val ⊆ flags P.threshold V.1:=by
    apply u j (D∩j.val) inter_subset_right V; intro z; apply p; rw [Pi.mul_apply,Finset.prod_apply, prod_eq_zero t z, zero_mul]
 have hh:= deck_r X T l v; constructor
 · intro i g; obtain ⟨a,s,f⟩:=halo_spec.mp g; obtain ⟨j,m,d⟩:= hh a s; exact (stun_v X T v j m).2 ((he j m).1 (halo_spec.mpr ⟨a,d,f⟩))
 intro i g; obtain ⟨j,t,d⟩:= hh i g; exact (he j t).2 d

def FlagWidth (p : BudgetPoint) (K : ForceBudget n) (N : ℕ): Prop:=
 ∀ i:Force n, Stax.Lives p N (lordD i) i.val.2 (K i)
lemma glowWidth (δ:ℕ) (K W:Cusp n)
 (u : ∀ (X:Aura n), ∀ D⊆X.val, Stax.Lives P δ X D (K X D)) :
 FlagWidth P (budgetR (glowV K W)) δ:= by
 intro i V t; refine wholeHalo δ K W u (lordD i) i.val.2 i.property.2 V ?_
 change bassH (lordD i) • glowV K W (lordD i) i.val.2 V ≠ 0 at t
 intro v; rw [v] at t; exact t (smul_zero _)
end YM.CF.Vow
