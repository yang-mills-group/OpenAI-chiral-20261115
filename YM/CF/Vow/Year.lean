import YM.CF.Vow.Core
import YM.CF.Vow.Pole
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
variable{n:Side} {P: BudgetPoint}{ℓ' y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Rue Trees
variable {w:Aura n→ℝ} {K Q:Cusp n} {C:blazeK n}
variable {U':Pax n}{L₁ L₂ L₃ γ γ' q q' δ δ' z κ:ℝ} {N:ℕ}(v:ArmsK P K C h)(x:∀ X:Aura n,∀ D:Support (More n),D.Nonempty→D⊆X.val→Medal P X.val D (Q X D) h (w X))(mB:0≤w)
variable {A:Aura n→ℝ}(t:Ready stern N A (a+δ') γ δ q)(hp:0≤ a)(g:∀ X:Aura n,Medal P X.val ∅ (U' X) h (A X))(y':0 < δ')(z':1 ≤ h)(hC:1≤κ)
abbrev bagU(A L:Aura n→ℝ):Aura n→ℝ:=fun x=>Real.exp 1 *(spanD x A 0 + L x)
local notation "Yc"=> ℝ
include t y' g z' hp mB x
variable(et:∀ i,w i+ γ*q^0*(1-q)⁻¹ ≤1)
include et
lemma perilS(X:Aura n)(D:Support (More n))(p:D⊆X.val) : Medal P X.val D ((boastV (FeeD P U') Q) X D) h (bagU A w X):=by
 let G':= spanD X A 0; let hm : Medal P X.val ∅ (FeeD P U' X) h G':= glenP _ z' g t (hp.trans (le_add_of_nonneg_right y'.le)) _
 have h':0 ≤ h:=zero_le_one.trans z'; have he:0 ≤ G' := hm.wage h'; let c:= γ*q^0*(1-q)⁻¹
 have hV :G' ≤ c:=by
    obtain ⟨i,p⟩:=X.property; have ht:0 ≤ a +δ':=add_nonneg hp y'.le
    apply le_trans ((le_mul_of_one_le_right he (show 1 ≤ Trees.currency N (a+δ') X.val from Real.one_le_exp (mul_nonneg ht (by positivity)))).trans (single_le_sum (s:= univ.filter fun x:Aura n=> i∈x.val) (f:=fun (x:Aura n)=>spanD x A 0 * Trees.currency N (a+δ') x.val ) (fun x _=> mul_nonneg ((glenP x z' g t ht 0).wage h') (Real.exp_pos _).le) (mem_filter.mpr ⟨mem_univ _,p⟩)))
    exact thinX (q:=q) t ht i 0 -- tune argument order
 by_cases hx:D.Nonempty
 · change Medal _ _ D (fun j=> _ ) _ _; unfold boastV; simp only [hx,↓reduceIte]; refine Medal.big ((x X D hx p).expressT h') ?_; exact mul_le_mul (Real.exp_monotone ((le_add_of_nonneg_right (he.trans hV)).trans (et X))) (le_add_of_nonneg_left he) (mB X) (Real.exp_pos _).le
 rw [not_nonempty_iff_eq_empty.mp hx]; unfold boastV; simp only [Finset.not_nonempty_empty,↓reduceIte]; refine hm.negT.expressT h' |>.big ?_; apply mul_le_mul (Real.exp_monotone (hV.trans ((le_add_of_nonneg_left (mB X)).trans (et X)))) (le_add_of_nonneg_right (mB X)) he (Real.exp_pos _).le
-- natural gauges ready bound.C
abbrev tallB (C: Aura n→ℝ)(N:ℕ)(a:ℝ)(x:Seat n):=∑ i:Aura n with x∈i.val,C i * currency N a i.val
include hC v
variable (au:∀ i:Seat n,tallB w N (a+δ') i ≤ L₁) (av:∀ i:Seat n,tallB (hymn C) N (a+δ') i ≤ L₂) (qV: degreePrice N γ' δ' ≤q') (qH:q'< 1)(ph:0< γ')(hpS:κ*L₂+Real.exp 1*(γ*q^0*(1-q)⁻¹+L₁) ≤γ')
include au av qV qH ph hpS
local notation "K'"=> loftP C (bagU A w) κ
local notation "WQ"=> boastV (FeeD P U') Q
local notation "Θ"=> Palot.stern ∘ Palot.dock
private lemma sway_x : Ready Θ N K' a γ' δ' q':=by
 let Ep:=perilS x mB t hp g y' z' et; have hu:=guessV K WQ C _ v Ep (zero_le_one.trans z') κ hC; refine ⟨ph,y',qV,qH,hu,fun i=> ?_⟩
 let f(j: Palot.Duo (More n)):= if i∈Θ j then K' j * Trees.currency N (a+δ') (Θ j) else 0; have hx(x):0 ≤ f x:=by unfold f; split; exact mul_nonneg (hu x) (Real.exp_pos _).le; exact le_rfl
 apply budget_of_sum hx; intro T; refine (sum_le_sum_of_subset_of_nonneg (f:=f) (subset_univ _) fun x _ _=>hx x).trans (le_trans ?_ hpS); rw [Fintype.sum_sum_type]; refine add_le_add ?_ ?_
 · apply le_trans _ (mul_le_mul_of_nonneg_left (av i) (zero_le_one.trans hC)); unfold tallB; rw [mul_sum,sum_filter]; apply sum_le_sum; intro j _; unfold f; change (ite (i ∈ j.val) _ _)≤ _; split_ifs; · simp only [loftP,Function.comp_apply,Palot.dock,Sum.elim_inl,mul_assoc]; exact le_rfl
   exact le_rfl
 apply le_trans _ (mul_le_mul_of_nonneg_left (add_le_add (thinX t (add_nonneg hp y'.le) i 0) (au i)) (Real.exp_pos _).le); unfold tallB; rw [←sum_add_distrib,mul_sum,sum_filter]; apply sum_le_sum; intro j _; unfold f; change ite (i∈ j.val) _ _ ≤ _; split_ifs
 · apply le_of_eq; unfold bagU loftP; simp only [Function.comp_apply,Palot.dock,Sum.elim_inr,id_eq,Palot.stern]; ring
 exact le_rfl
lemma rent_x : ArmsK P (roomV P U' K Q) (windF C (bagU A w)) h ∧ ∀ i:Seat n, κ*tallB (hymn (windF C (bagU A w))) N a i ≤ γ'*q'^0*(1-q')⁻¹:=by
 let Q':=perilS x mB t hp g y' z' et; have h':=zero_le_one.trans z'; let T:=sway_x v x mB t hp g y' z' hC et au av qV qH ph hpS; exact ⟨trialsB v Q' h', fun i=> chisel K WQ _ _ v Q' h' κ hC i hp T⟩ -- tune
end YM.CF.Vow
