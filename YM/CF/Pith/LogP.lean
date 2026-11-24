import YM.CF.Pith.Rang
import YM.CF.Pith.Snow
import YM.CF.Vow.Pear
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
-- F - E_oldQ - G_scalar = Paid_H
abbrev GrainP (G:Pax n):Prop:=∀ i:Aura n,∃ v:ℝ,G i=(fun _=> Lilt.thim n v)
local notation "N'"=> P.B
local notation "wP"=> (P.supportExponent+1)
variable (α:ℝ)(hu:1 ≤α)(ht:Ready Palot.stern P.B A (P.supportExponent+1+1) γ δ q)(hy:1 ≤ h)(Z:GrainP G)
variable (u0:∀ X,Medal P X.val ∅ (F X) h (A X))(hv: ∀ X,Medal P X.val ∅ (G X) h (A X))(hp:∀ X,Medal P X.val ∅ (F X-G X) h (α⁻¹*A X))(WDX:∀ X:Aura n,Medal P X.val ∅ (F X-G X-E X) h (W X))
-- Order-one quadratic pure $
local notation "Πq"=> Aura n
include Z
lemma hymnG(X:Aura n)(m:ℕ)(i:Tuple (Aura n) m):∃ v:ℝ,sta G X 0 ⟨m,i⟩=v • (1:Copy n):=by
 choose c h using Z; unfold sta; split; swap; · exact ⟨0,(zero_smul ..).symm⟩
 unfold guava; simp_rw [h]; let K:ℝ:= coefficient gRule i / ((m+1).factorial:ℝ); let j(w):= c (i w); have ht : (∏ w,j w) • (1:Copy n)=∏ w,j w • (1:Copy n):=by -- graph K Power factor frac cast tune
    generalize (univ:Finset (Option (Fin m)))=S; induction S using Finset.induction_on with
    | empty=> simp
    | insert a S p ih=> rw [prod_insert p,prod_insert p]; rw [mul_smul, ih, smul_mul_assoc, one_mul] -- gen all S remove
 -- existence value any new
 refine ⟨K*∏ w,j w,?_⟩
 rw [mul_smul,ht]; rfl
abbrev branch_P (U:Pax n)(i:Aura n):Copy n:= U i+funge i U 0 1
lemma stem_P: GrainP (branch_P G):=by
 intro i; obtain ⟨x,h⟩:= Z i; choose v V using (hymnG (G:=G) Z i 1); unfold branch_P funge; simp_rw [h,V] -- h dangerous rewrite G i inside
 refine ⟨x+∑ j:Tuple (Aura n) 1,v j,funext fun j=>?_⟩
 change Lilt.thim n x+ (∑ j,v j • (1:Copy n)) j=Lilt.thim n _; unfold Lilt.thim; rw [add_smul,sum_smul,Finset.sum_apply]; rfl
omit Z
abbrev taper_R(H G E:Pax n)(P:BudgetPoint)(X:Aura n):Copy n:= (H X-G X-E X)+(funge X H 0 1-funge X G 0 1)+spinD P X H 2
abbrev Cap_p (A W:Aura n→ℝ)(b:ℝ)(X:Aura n):ℝ:= W X+2*b⁻¹ * spanD X A 1+spanD X A 2
include ht hy u0
lemma tone_G (i:Aura n)(v:visible P i.val ∅ V.1) : FeeD P F i V = (branch_P G) i V + E i V + taper_R F G E P i V:=by
 have hv:0 ≤ P.supportExponent+1+1:=(add_pos (add_pos P.exponent_pos zero_lt_one) zero_lt_one).le
 rw [past i V ht hy u0 hv v]; unfold taper_R branch_P; simp only [Pi.add_apply,Pi.sub_apply]; abel
include hv hu hp WDX
lemma stick_H (i:Aura n): Medal P i.val ∅ (taper_R F G E P i) h (Cap_p A W α i) :=by
 let k:= (add_pos (add_pos P.exponent_pos zero_lt_one) zero_lt_one).le
 exact ((WDX _).plus (tenderH i ht hy k u0 hv _ (inv_pos.mpr (zero_lt_one.trans_le hu)) hp)).plus (Vow.glenP i hy u0 ht k 2) -- tune Arg
abbrev Caph(b v q γ:ℝ):ℝ:= v+ 2*b⁻¹ * (γ*q^1*(1-q)⁻¹)+ γ*q^2*(1-q)⁻¹
lemma years_C (xX:Seat n)(p: tallB W P.B (P.supportExponent+1+1+1) xX ≤ β) : tallB (Cap_p A W α) N' (P.supportExponent+1+1) xX ≤ Caph α β q γ:=by -- xX variable
 unfold Cap_p tallB; simp_rw [add_mul,sum_add_distrib]; simp_rw [mul_assoc (2*α⁻¹),←mul_sum _ _ (2*α⁻¹)]
 have hk:0 ≤ P.supportExponent+1+1:=(add_pos (add_pos P.exponent_pos zero_lt_one) zero_lt_one).le; refine add_le_add (add_le_add (le_trans ?_ p) (mul_le_mul_of_nonneg_left (thinX ht hk xX 1) (mul_nonneg (by norm_num) (inv_nonneg.mpr (zero_le_one.trans hu))))) (thinX ht hk xX 2)
 refine sum_le_sum fun i t=> mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right (show wP+1≤ wP+1+1 from le_add_of_nonneg_right zero_le_one) (Nat.cast_nonneg _))) ((WDX i).wage (zero_le_one.trans hy))
end YM.CF.Larch
