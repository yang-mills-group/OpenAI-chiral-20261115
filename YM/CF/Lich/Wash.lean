import YM.CF.Lich.Bloss
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Lich
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
-- separate path ledger Φ.M.Target.S.P
variable {N P B:Side}(G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(x e:ℝ)(T:Tube SU.group S)
variable{r n j d:ℕ}
namespace Muster
variable{G S x e T}
variable(A:Muster G S x e T)
variable(U: Monk SU.group S)(V W:Rent0 G e) -- V true W at ζ=0
local notation "θ"=> A.room
local notation "j"=> A.loft
local notation "β"=> A.beta
local notation "q"=> A.trot
local notation "α"=> A.ang
local notation "γ"=> A.fee
local notation "l"=> A.post
local notation "F"=> U.sent x T q θ l β
local notation "Y"=> (U.park,U.k)
local notation "K"=> U.key.dome (j*radiusB x)
local notation "Q'"=> A.LawQ
local notation "YY"=> A.Beds
-- account per site
-- far components plus interior.Optional momentum.
open Corne
open Vol
variable (s:Signed)
local notation "X₀"=>(turnStore s U.key).costs
local notation "K₁"=> traceZ (turnStore s U.key).flags
local notation "U₀"=> pull s 0 F
local notation "V₀"=> pull s 0 U.V
local notation "m"=> Domain N B
local notation "m'"=> Domain P B
local notation "V'"=> A.phaseLow.threshold
local notation "U'"=> A.phaseUp.threshold
local notation "b₀"=> Stores.till x
local notation "b'"=> b₀/S.patch.L.val
local notation "Δ"=> (α+γ)
variable(k:ℕ){c f:Side}{b z σ C D:ℝ}
lemma perkM {w: ℕ→ Atom SU.group n}{f:ℕ→ℝ}(U:Config SU.group c)(i:Site c)(p:SumBudget (fun i=>(w i).budget σ) b)(h:0<σ)(H:∀ v, |f v| ≤ |(w v).unmasked U i|): Summable f:=by
 have ht(v:ℕ): ‖f v‖ ≤ (w v).budget σ*(2:ℝ)^n:= le_trans (H _) (((w v).unmasked_bound ..).trans (mul_le_mul_of_nonneg_right ((w v).lower_budget σ h) (by positivity)))
 exact Summable.of_norm_bounded ((p.2.1).mul_right _) ht
lemma fork_b(i: Site m')(Q:ℕ→Atom SU.group d)(p:SumBudget (fun i=>(Q i).budget σ) b)(h:0<σ): ∑ t,extU A U s k t i Q = Cloak.park F s U.key q A.phaseUp Q i:=by
 unfold extU; apply storyW; refine perkM U₀ i p h (fun V=>?_); unfold lush_k east; split
 next w=>
    rw [abs_mul]; apply mul_le_of_le_one_left (by positivity); unfold nose wrapM shutters; rw [abs_prod]; apply prod_le_one; · intro i _; positivity
    intro u _; unfold Chi.innerShare; rw [abs_of_nonneg (show 0≤ _ from (A.trot.range _).1)]; apply (A.trot.range _).2
 simp
lemma foster_s (i:Site m)(Q:ℕ→Atom SU.group d)(p:SumBudget (fun i=>(Q i).budget σ) b)(h:0<σ): ∑ t,extV A U s k t i Q= visit U.V s U.key A.phaseLow Q i:=by unfold extV; apply storyW; exact perkM V₀ i p h fun z=> by unfold peer_k; split; exact le_rfl; simp
lemma rover (i:Site m')(p:T.up.Bounds T.high σ C D): ∑ L,river A U s k L i= leftV T F s U.key q A.phaseUp x β i:=by
 unfold river leftV; simp_rw [sum_add_distrib,←mul_sum,sum_add_distrib]; rw [fork_b A U s k i _ (pastA _ p.width p.three b₀) (half_pos p.width),fork_b A U s k i _ (pastA _ p.width p.four b₀) (half_pos p.width),fork_b A U s k i _ (pastA _ p.width p.two b₀) (half_pos p.width)]; unfold sapU; rw [storyW]; exact perkM U₀ i (hurry p b₀) (half_pos p.width) fun z=>by unfold Cloak.sleeve; split; exact le_rfl; simp
lemma foible(i:Site m)(p:T.down.Bounds T.low σ C D):∑ L,flows A U s k L i=rightV T U.V s U.key A.phaseLow x Δ β i:=by
 unfold flows rightV; simp_rw [sum_add_distrib,←mul_sum,sum_add_distrib]; rw [foster_s A U s k i _ (pastA _ p.width p.three b') (half_pos p.width),foster_s A U s k i _ (pastA _ p.width p.four b') (half_pos p.width),foster_s A U s k i _ (pastA _ p.width p.two b') (half_pos p.width),foster_s A U s k i _ (barn p.three b') p.width,foster_s A U s k i _ (barn p.four b') p.width]; unfold sapC; rw [storyW]; exact perkM V₀ i (hurry p b') (half_pos p.width) fun z=>by unfold Cloak.sleeve; split; exact le_rfl; simp
lemma quarry {z' C' k':ℝ}(p:T.up.Bounds T.high σ C D)(hz:T.down.Bounds T.low z' C' k'):∑ i, shardy A U k i=tollG A U:=by
 unfold shardy tollG averaged; rw [sum_neg_distrib,←mul_sum,sum_comm]; congr 2; refine sum_congr rfl fun i _=>?_ ; rw [sum_sub_distrib,sum_comm (f:=river A U i k),sum_comm (f:=flows A U i k)]; simp_rw [rover A U i k _ p,foible A U i k _ hz]
end Muster
end YM.CF.Lich
