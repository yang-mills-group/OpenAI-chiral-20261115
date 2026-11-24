import YM.CF.Pith.Pole
import YM.CF.Hype.Ace
import YM.CF.Hype.Migrate
import YM.CF.Bake.Layer
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
local notation "Ink" n=> Hake.Raid (Dwell n)
open Rue Trees Bake Vow Larch -- remove
variable {γ c d e v q α γ' KU b:ℝ}{K K':Cusp n} {L:blazeK n}{F E:Pax n}{Q:Aura n→ℝ} (Wp:Wisp P F E h γ c d) (T: ArmsK P K L h) (R: RegBudget n)(u:∀ V:Orbit n,FleetS P.threshold V.1→exponentL P R V.1+fuelV P K' V=coldE P E V)(η0:1 ≤ h)
abbrev owed_E(n:Side)(z:ℝ):= Lilt.thim n z
-- Some helpers
local notation "ιn"=> Aura n
local notation "qn"=> degreePrice P.B γ 1
abbrev nextE {n:Side}(T: Aura n→ℝ):Cusp n:=fun i D _=> -(owed_E n (T i))
local notation "σn"=> (P.supportExponent+1+1)
local notation "U'S"=> (γ * (degreePrice P.B γ 1) ^0*(1-degreePrice P.B γ 1)⁻¹)
-- unmarked scalar pressure. the residual separated when cut. combine only at last. P-input R.E Sup.
lemma crep(P:BudgetPoint)(V:Orbit n)(G H:Pax n):coldE P (G+H) V=coldE P G V+coldE P H V:=by unfold coldE; simp only [Pi.add_apply,Finset.sum_add_distrib]
lemma ripe_H(P:BudgetPoint)(V:Orbit n)(G H:RegBudget n): exponentL P (G+H) V.1=exponentL P G V.1+exponentL P H V.1:=by unfold exponentL; simp_rw [numb_b P _ _ V]; rw [←Finset.sum_add_distrib]; exact sum_congr rfl fun i _=>march_add V P (lagE i) _ _ -- tune
private lemma lay_G(X:Scree.Hub n) (a:Pax n)(v:Turf a)(τ:Ids n) (p:knotD (lagE X)=X): a (lagE X)=oV (cloveE a τ X):=by rw [Bake.cloveE,if_pos p]; exact funext fun j=> v (lagE X) j τ
lemma width_v (P:BudgetPoint)(a:Pax n)(v:Turf a)(τ:Ids n)(p:∀ j,Medal P j.val ∅ (a j) h (Q j))(t:0≤h)(g:∀ o:Seat n,tallB Q P.B (P.supportExponent+1+1) o ≤ d): IncX (fun _=>False) (sunY univ knotD (fun i:ιn=>cloveE a τ (knotD i))) P h (reserveT P.power P.order P.B 1*d):=by -- note equality cloveE_F
 let F(i:ιn):=a i; let L(i:ιn):= fareX P.B P i.val* Q i
 refine feat_v univ knotD _ L P _ (fun i _=>?_ ) (fun i=>?_)
 · have hp:knotD (lagE (knotD i))=knotD i:=by rw [yelp]
   have hv:= lay_G _ a v τ hp; rw [yelp] at hv; apply (show Medal P (knotD i).val.2 ∅ _ _ _ from ?_).preservesE τ t _; exact hv ▸ p i -- tune
 let R:=reserveT P.power P.order P.B 1; let N:= univ.filter fun j:ιn=> (knotD j).val.1=i; let U':=P.supportExponent+1; have hx:0≤Q:=fun i=>(p _).wage t; have hi:= (tall_m (k:=P.B) Q hx (le_add_of_nonneg_right zero_le_one) i).trans (g i); -- inst a
 apply le_trans _ (mul_le_mul_of_nonneg_left (show ∑ j∈N,Q j* Trees.currency P.B U' j.val ≤ d from ?_) (show 0≤ R from by unfold R reserveT coin_n stilK; positivity)); swap; · exact (sum_le_sum_of_subset_of_nonneg (show N⊆ _ from (fun j u=>mem_filter.mpr ⟨mem_univ _, show i∈j.val from (mem_filter.mp u).2 ▸ (fastX j)⟩)) (fun j _ _=>mul_nonneg (hx j) (Real.exp_pos _).le)).trans hi
 rw [mul_sum]; apply sum_le_sum; intro j t
 have hh:= Nor.coinPay P j.val 1 zero_lt_one (k:=P.B)
 let x:= L j; change P.mass j.val x ≤ _
 calc
    _ = (Trees.currency P.B P.supportExponent j.val*Q j)*fareX P.B P j.val:= by unfold x L BudgetPoint.mass Trees.currency; ring
    _ ≤ (Trees.currency P.B P.supportExponent j.val*Q j)*(R*Real.exp (1*coverNumber P.B j.val)):= mul_le_mul_of_nonneg_left hh (mul_nonneg (Real.exp_pos _).le (hx j))
    _ = _:=by unfold Trees.currency U'; rw [add_mul,Real.exp_add]; ring
lemma fair_v (P:BudgetPoint)(a:Pax n)(v:Turf a)(τ:Ids n)(Vv:Orbit n): exponentL P (sunY univ knotD (fun i:ιn=>cloveE a τ (knotD i))) Vv.1=coldE P a Vv:=by
 rw [release_v]; unfold coldE; rw [sum_filter]; refine sum_congr rfl fun i _=>?_ ; have p:knotD (lagE (knotD i))= knotD i:=by rw [yelp]
 have h:=lay_G _ a v τ p; rw [yelp] at h; rw [yelp]; change Vow.march _ _ (oV (cloveE a τ _)) _=_; rw [←h]; rfl
include η0
lemma nom_F (P:BudgetPoint)(i:Aura n)(p:ℝ)(v:Medal P i.val ∅ (fun _ :Orbit n=> owed_E n p) h c)(D:Support (More n)): Medal P i.val D (fun _ :Orbit n=> -(owed_E n p)) h c:=by
 let τ:Ids n:=Classical.arbitrary _
 have he: ‖owed_E n p‖≤c:=v.capF η0 (1,τ) (by rw [sdiff_empty]; exact ping_f P _)
 have hx:‖(1: Cipher n)‖=1:=by change ‖(1: FC (Dwell n))‖=1; rw [CStarRing.norm_one]
 apply Medal.negT (F:=(fun _=> owed_E n p))
 apply Medal.big ((Medal.oneT (X:=i.val) (D:=D)).rum p); exact le_trans (le_of_eq (by change ‖p‖*1=‖p • (1:FC (Dwell n))‖; rw [norm_smul]; rw [show ‖(1:FC (Dwell n))‖=1 from hx])) he
end YM.CF.Larch
