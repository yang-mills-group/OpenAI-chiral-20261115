import YM.CF.Rive.Moor
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Rive
open Larch
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
-- second grade corrections.L General receipt.One-ball log-tail. split off constants or scalar portal. reserve α budgeting.
open Trees Ursell Push.AbsoluteSums.Graph
open Lilt Bake Vow
variable {F G E Q:Pax n}(Y:Aura n)(V:Orbit n) {A C H W L':Aura n→ℝ}{z u γ δ q v β:ℝ}
-- structural.Normal P. Keep.Hit.Utils
open Salt Ione Bake
local notation "η"=> P.supportExponent+1+1
variable (T V':RegBudget n)(α:ℝ)(hu:0<α)(ht:Ready Palot.stern P.B A (P.supportExponent+1+1) γ δ q)(hy:1 ≤ h)
variable (u0:∀ X,Medal P X.val ∅ (F X) h (A X))(hv: ∀ X,Medal P X.val ∅ (G X) h (A X))(hp:∀ X,Medal P X.val ∅ (F X-G X) h (α⁻¹*A X))(WDX:∀ X:Aura n,Medal P X.val ∅ (E X) h (W X))
-- F new.OP.Like tiny.G old. Earth.P.F.
-- clip tiny ERP for exponent after.Series.Post.Fl. receipts.Compt.
-- x output shaped.M evaluate at Fourier lifts. replace T .* P-.Fee.Q normalized. Pure eligible with mask extensions.
variable (D:Pax n)(pX:∀ X:Aura n,∀ x:Orbit n, F X x-G X x= D X x+ E X x)(pU:∀ X:Aura n,∀ x:Orbit n,¬ visible P X.val ∅ x.1 → D X x=0)
include pX pU hu ht hy u0 hv hp WDX
lemma liftT : Medal P Y.val ∅ (FeeD P F Y - FeeD P G Y- D Y) h (Larch.rentD α W A Y) :=by
 let H:= spinD P Y F 2; let I:= E Y+ (funge Y F 0 1-funge Y G 0 1)+H+ -(spinD P Y G 2)
 have he :0≤ P.supportExponent+1+1:=(add_pos (add_pos P.exponent_pos zero_lt_one) zero_lt_one).le
 rw [show FeeD P F Y- FeeD P G Y-D Y=zenS P Y.val ∅ I from ?_]; swap
 · funext x; unfold zenS; split; swap; next h=> change FeeD P F Y x-FeeD P G Y x-_=0; rw [pU Y x h]; unfold FeeD spinD lasting zenS; rw [if_neg h,if_neg h]; simp
   next u=> change FeeD P F Y x-FeeD P G Y x-D Y x= _; rw [past Y x ht hy u0 he u, past Y x ht hy hv he u,show F Y x=D Y x+E Y x+G Y x from sub_eq_iff_eq_add.mp (pX ..)]; change (_+_+(_:Cipher n)+_+_) - _- _=E _ _+(_-_) +_+ -_; abel -- tune
 exact Larch.heft_zen _ _ _ hy ((((WDX Y).plus (Vow.tenderH Y ht hy he u0 hv α⁻¹ (inv_pos.mpr hu) hp)).plus (Vow.glenP Y hy u0 ht he 2)).plus ((Vow.glenP Y hy hv ht he 2).negT))
lemma loft_T (o:Seat n)(u: tallB W P.B (P.supportExponent+1+1) o ≤ b): tallB (rentD α W A) P.B (P.supportExponent+1+1) o≤ b+2*α⁻¹*(γ*q^1*(1-q)⁻¹)+2*(γ*q^2*(1-q)⁻¹):=by
 let Y:=γ*q^2*(1-q)⁻¹; rw [two_mul Y, ←add_assoc]; unfold tallB; simp_rw [rentD,add_mul,sum_add_distrib,mul_assoc (2*α⁻¹), ← mul_sum _ _ (2*α⁻¹)]
 have he :0≤ P.supportExponent+1+1:=(add_pos (add_pos P.exponent_pos zero_lt_one) zero_lt_one).le
 exact add_le_add (add_le_add (add_le_add u (mul_le_mul_of_nonneg_left (Vow.thinX ht he o 1) (by positivity))) (Vow.thinX ht he o 2)) (Vow.thinX ht he o 2)
end YM.CF.Rive
