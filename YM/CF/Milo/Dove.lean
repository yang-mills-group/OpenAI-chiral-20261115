import YM.CF.Milo.Chart
import YM.CF.Pith.Pole
import YM.CF.Ione.Pose
import YM.CF.Pith.LogP
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Larch
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
abbrev orbV(T:RegBudget n)(X:Aura n)(V:Orbit n):Cipher n:=∑ j∈ web0 X, T j V.1
abbrev Nu(P:BudgetPoint)(F G:Pax n)(T:RegBudget n): Pax n:=fun X=>zenS P X.val ∅ (fun i=> FeeD P F X i - FeeD P G X i-orbV T X i)
variable (pX:∀ (X:Aura n)(V:Orbit n),F X V=G X V+orbV T X V+ E X V)
-- clip tiny ERP for exponent after.Series.Post.Fl. receipts.Compt.
abbrev rentD(W:Aura n→ℝ)(C:Aura n→ℝ)(V:Aura n) := W V+2*α⁻¹*spanD V C 1+spanD V C 2+spanD V C 2
abbrev tinK:= Nu P F G T
local notation "N'"=> Nu P F G T
lemma heft_zen(X D:Support (More n))(H:Copy n)(p:1≤h)(s:Medal P X D H h a): Medal P X D (zenS P X D H) h a:=by
 let V(i:ℕ):Copy n:=if i=0 then H else 0; let W(i:ℕ):=if i=0 then a else 0; have he(i):Medal P X D (V i) h (W i):=by unfold V W; split; exact s; exact Medal.zeroT
 have ht: Summable W:= summable_of_ne_finset_zero (s:={0}) (fun i h=> if_neg (by simpa using h))
 have hs:= Vow.vaut he ht p; rw [show (∑' i,W i)=a from ?_, show lasting P X D V=zenS P X D H from ?_] at hs; exact hs
 swap
 · rw [tsum_eq_single 0]; exact if_pos rfl; intro b hb; exact if_neg hb
 unfold lasting; apply congrArg; funext i; rw [tsum_eq_single 0]; unfold V; rw [if_pos rfl]; intro b hb; unfold V; rw [if_neg hb]; rfl
include ht u0 hv hp WDX pX hu hy
lemma α_G(X:Aura n):Medal P X.val ∅ (N' X) h (rentD α W A X):=by
 let δ:= spinD P X F 2; let r:= (funge X F 0 1 - funge X G 0 1); let Z:= E X + r+δ + -(spinD P X G 2)
 have he :0≤ P.supportExponent+1+1:=(add_pos (add_pos P.exponent_pos zero_lt_one) zero_lt_one).le
 have hh: N' X= zenS P X.val ∅ Z:=by
    funext x; unfold Nu zenS; split_ifs with u; swap; exact rfl
    dsimp only; rw [past X x ht hy u0 he u,past X x ht hy hv he u]; rw [pX]; unfold Z; change _=E _ _+(_-_) +_ + -_; abel
 rw [hh]; exact heft_zen _ _ _ hy ((((WDX X).plus (Vow.tenderH X ht hy he u0 hv α⁻¹ (inv_pos.mpr hu) hp)).plus (Vow.glenP X hy u0 ht he 2)).plus ((Vow.glenP X hy hv ht he 2).negT))
lemma cost_p(o:Seat n)(u: tallB W P.B (P.supportExponent+1+1) o ≤ b): tallB (rentD α W A) P.B (P.supportExponent+1+1) o≤ b+2*α⁻¹*(γ*q^1*(1-q)⁻¹)+2*(γ*q^2*(1-q)⁻¹):=by
 let Y:=γ*q^2*(1-q)⁻¹; rw [two_mul Y, ←add_assoc]; unfold tallB; simp_rw [rentD,add_mul,sum_add_distrib,mul_assoc (2*α⁻¹), ← mul_sum _ _ (2*α⁻¹)]
 have he :0≤ P.supportExponent+1+1:=(add_pos (add_pos P.exponent_pos zero_lt_one) zero_lt_one).le; -- tune
 refine add_le_add (add_le_add (add_le_add u (mul_le_mul_of_nonneg_left (Vow.thinX ht he o 1) (by positivity))) (Vow.thinX ht he o 2)) (Vow.thinX ht he o 2)
omit ht u0 hv hp WDX pX hu hy
end YM.CF.Larch
