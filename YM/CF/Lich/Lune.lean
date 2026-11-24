import YM.CF.Lich.Rune
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
open CF.Jet
variable(n)
local notation "N'"=> (Fintype.card SU.group.ColorIndex:ℝ)
local notation "m"=> More (mid N B)
variable(T)
def quota(n j':ℕ)(C D:ℝ):=N'^(j'+1+1)*(2^n*C*(2^n*D)^j') -- binder μ
variable{C a b c s z:ℝ}{k:ℕ}
local notation "Z₀"=> kist U
open Matrix Further.CurvedGaussianJets.Tracks PhysicalNext.OrderedAffine2B.SymFare Order
lemma crook (w: Run (U.zoo x) (k+1))(p:NameX T U x q θ l n C a b c z): Allows n (fun u:Directions SU.group m=> vent (T:=T) (U.atop u x) (show Run ((U.atop u x).zoo x) _ from w)) 0 ((2:ℝ)⁻¹*quota n k C (C*tipPay a x)):=by
 let D:=bar_t p.price.center w; have he:= D.smul (-(2:ℝ)⁻¹); rw [abs_neg,abs_of_pos (by positivity)] at he; unfold quota; apply he.germ; filter_upwards with i; change (- (2:ℝ)⁻¹* _)= vent (T:=T) _ _; unfold vent; rw [one_div]; rfl
lemma stick_w (w:Run (U.zoo x) (k+1))(p:NameX T U x q θ l n C a b c z):Allows n (fun u=> pes T x q θ l (U.atop u x) w) 0 (((2:ℝ)⁻¹*quota n k C (C*tipPay a x)+(2:ℝ)⁻¹ *quota n k b b)+quota n k c c):=by -- tune
 have h:= (bar_t p.price.core w).smul (2:ℝ)⁻¹; rw [abs_of_pos (by positivity)] at h; apply (((crook T n A U w p).add (h.mono (by rfl))).add (bar_t p.price.modes w)).germ; filter_upwards with i; unfold pes; rw [one_div]; unfold vent; rw [one_div]; rfl -- tune params
variable(w:LinkS S k)
lemma spiritH (p:NameX T U x q θ l n C a b c z)(hz:0≤b)(hx:0≤c): Allows n (fun u=> Tarn.pave T x q θ l w (U.atop u x)) 0 (((2:ℝ)⁻¹*quota n k C (C*tipPay a x)+(2:ℝ)⁻¹*quota n k b b)+quota n k c c):=by
 by_cases he:∃ V:Run (U.zoo x) (k+1), stave V=w
 · obtain ⟨j',rfl⟩:=he; apply (stick_w T n A U j' p).germ; filter_upwards with u; exact (paved ..).symm -- tune
 have ht:0≤C:=p.posT; apply (Jet.allows_const 0 (v:=(0:ℝ)) ?_).germ ?_
 · rw [norm_zero]; unfold quota tipPay; positivity
 filter_upwards with u; have hg:¬ ∃ v:Run ((U.atop u x).zoo x) (k+1), Tarn.stave v=w:= he; unfold Tarn.pave; rw [dif_neg hg]
lemma meritH (p:NameX T U x q θ l n C a b c z): |paveB (x:=x) T w U| ≤ (2:ℝ)⁻¹*quota n k C (C*tipPay a x):=by
 by_cases he:∃ V:Run (U.zoo x) (k+1),stave V=w -- notation
 · obtain ⟨v,rfl⟩:=he; rw [stationB]; have hp:= (crook T n A U v p).value; unfold vent at *; dsimp only [Monk.atop] at hp; simp only [Vmove,smul_zero,Work.G07.at_zero_increment] at hp; exact hp -- tune proof_ir
 rw [paveB,dif_neg he,abs_zero]; have ht:=p.posT; unfold quota tipPay; positivity
abbrev fareI (C a b c x:ℝ)(n k:ℕ):= quota n k C (C*tipPay a x)+(2:ℝ)⁻¹*quota n k b b+quota n k c c
lemma luxeS (o:Site m)(p:NameX T U x q θ l n C a b c z)(hn:NameX T Z₀ x q θ l n C a b c z)(hz:0≤b)(hx:0≤c): Allows n (fun i=>leys A (U.atop i x) o w) 0 (fareI C a b c x n k) :=by
 have hr:=Newt.subtract_p (spiritH T n A U w p hz hx) (Jet.allows_const (n:=n) _ (v:=paveB (x:=x) T w (kist U)) (meritH T n A (kist U) w hn)); have he:= hr.smul (plant S o w)
 exact he.mono ((mul_le_of_le_one_left hr.nonneg plant_v).trans_eq (by unfold fareI; ring)) -- tune signature
end Muster
end YM.CF.Lich
