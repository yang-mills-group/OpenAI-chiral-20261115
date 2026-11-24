import YM.CF.Sour.Penny
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
variable (δ:ℕ)(H:Aura n→Firing n)(P:BudgetPoint)(h:ℝ)(z:Aura n→ℝ)
structure Bias (δ:ℕ)(H:Aura n→Firing n)(P:BudgetPoint)(h:ℝ)(z:Aura n→ℝ): Prop where
 valid:∀ i:Aura n,∀ x:Orbit n,Sector (camp i.val) false (H i x)
 weight: 0 ≤ z
 scope:∀ X Y:Aura n,∀ D:Support (More n),Y.val⊆X.val→D⊆X.val→halo δ D ⊆ X.val→Marque P X Y D (H Y) h (z Y)
namespace Bias
variable {δ H P h z}
abbrev αt(Y:Aura n)(X:Aura n)(D:Support (More n))(d:ℕ):Prop:= Y.val⊆X.val∧D⊆X.val ∧ halo d D ⊆ X.val
variable (g: Bias δ H P h z)
def payX (g:Bias δ H P h z):Rinse SA (Copy n):=fun X D Y F=>if e:αt Y X D δ then (g.scope X Y D e.1 e.2.1 e.2.2).toCrate.motion F else 0
lemma truth(X:Aura n)(D:Support (More n))(Y:Aura n)(F:Copy n)(v:αt Y X D δ)(i:Orbit n): (g.payX X D Y F i).val=Sault.rind (coll_T P X D (H Y) i*(F i).val):=by rw [payX,dif_pos v]; rfl
lemma buys (W:3 ≤ P.B)(hw:0 ≤ h): Stax.Pitch P h δ g.payX z (fun i Y=> H Y i):=by
 refine ⟨g.weight,fun X D Y=>?_,fun X D u Y v l F f=>?_,fun y X=> g.valid X y,?_⟩
 · unfold payX; split; rename_i e; exact funext fun i=> (g.scope X Y D e.1 e.2.1 e.2.2).toCrate.lit0 i 0 rfl -- tune
   rfl
 · unfold payX; split; rename_i e; exact Marque.book (g.scope X Y D v u e.2.2) f W v hw (g.weight Y) -- tune explicit
   refine ⟨Medal.zeroT.big (mul_nonneg (g.weight _) (f.merit.wage hw)),fun i p=>False.elim (p rfl)⟩
 intro X Y i x v c F D f; have he: pingS P.threshold (X.val\D) i.1:= (shoreK _ _ x _).mp (by refine Finset.disjoint_left.mpr fun {j} k l=>?_ ; exact (mem_sdiff.mp k).2 (mem_inter.mpr ⟨l,(mem_sdiff.mp k).1⟩)) -- orientation
 unfold payX; split
 next p=>
    change Sault.rind (coll_T _ _ _ _ _* _) = _; rw [(g.scope X Y D p.1 p.2.1 p.2.2).toCrate.pointV i ⟨he,inter_subset_left⟩]
 next p => rw [show F i=0 from by by_contra h; exact p ⟨v,inter_subset_right,(f.loaf i h).1⟩]; simp [Sault.rind]
end Bias
end YM.CF.Sour
