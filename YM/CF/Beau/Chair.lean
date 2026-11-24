import YM.CF.Beau.Spree
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Beau
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
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k' m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
open Ione
local notation "N"=> P.order
local notation "Xo"=>Skye.Seat n
open Ione Larch
open Taxi Geo RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup
local notation "Hz"=> Scree.Hub n
variable(P:BudgetPoint)(E: RegBudget n)(L:ℕ)
abbrev chute(P:BudgetPoint)(L:ℕ)(x:Scree.Hub n):Prop:=Pave P L x.val.2
def caw(P:BudgetPoint)(L:ℕ)(E:RegBudget n):RegBudget n:= fun X=>if chute P L X then E X else 0
def can_V(P:BudgetPoint)(L:ℕ)(E:RegBudget n):RegBudget n:= fun X=>if chute P L X then 0 else E X
local notation "T"=> caw P L E
local notation "T'"=> can_V P L E
local notation "Ω"=> P.supportExponent
variable (p:IncX Utrue E P h a)(v:1 ≤ h)
lemma craftL:T+T'=E:=by funext X U; unfold caw can_V; simp only [Pi.add_apply]; split<;> simp
lemma dawnZ(s:Sweep n)(X: Hz): chute P L X↔ chute P L (moveHub s X):=by unfold chute Pave; rw [show coverNumber _ (moveHub s X).val.2= _ from glow_q s P.B _]
lemma grit_p{X:Scree.Hub n}{W:InkD n}(t:PressB P X W h a)(u:0≤h):0≤a:= (Taxi.eraF W X t u 1 (ping_f P _)).grade
abbrev chipT (P:BudgetPoint)(L:ℕ)(K:Scree.Hub n→ℝ):Scree.Hub n→ℝ:= fun X=> if chute P L X then K X else 0
include p v
lemma slat_F : IncX Utrue T' P h a ∧ Ionic P L T':=by
 obtain ⟨A,t,l⟩:=p.weight; refine ⟨⟨⟨(fun X=> if chute P L X then 0 else A X),fun X=>?_ ,fun i=>?_⟩,fun s v U b i x=>?_ ⟩,fun i x q=>?_⟩
 · unfold can_V; dsimp only; split; exact Vale.rinse ..; exact t X
 · refine (sum_le_sum ?_).trans (l i); intro j _; by_cases h: i=j.val.1
   · rw [if_pos h, if_pos h]; dsimp only; split; unfold BudgetPoint.mass; rw [mul_zero]; have hp:= grit_p P (t j) (zero_le_one.trans v); positivity; exact le_rfl -- tune
   rw [if_neg h, if_neg h]
 · unfold can_V; simp only [←dawnZ]; split; exact Eq.symm (map_zero _); exact p.face s v U b i x
 unfold can_V; rw [if_pos q]; exact none_q _
lemma stake_V : (∃ (A:Hz→ℝ), (∀ X:Hz,PressB P X (T X) h (chipT P L A X)) ∧∀ i:Skye.Seat n,(∑ X:Hz with X.val.1=i,P.mass X.val.2 (chipT P L A X)) ≤ a)∧(∀ s:Sweep n,∀ X:Hz,∀ V:Pane n,T (moveHub s X) (flashA s V)=suit_Y s (T X V))∧ Pant T:=by
 obtain ⟨A,t,l⟩:=p.weight
 have ht(s:Sweep n)(X:Hz)(V:Pane n): T (moveHub s X) (flashA s V)=suit_Y s (T X V):=by
    unfold caw; simp only [←dawnZ]; split; exact p.face s trivial _ (spinZ ..) X V; exact Eq.symm (map_zero _)

 refine ⟨⟨A,fun X=>?_ ,fun i=>?_⟩,ht,fun s=>⟨_,fun i W=>(ht s i W).trans (tama s _ (spinZ s.charge s.s) _).symm⟩ ⟩
 · unfold caw chipT; split; exact t _; exact Vale.rinse ..
 rw [sum_filter]; refine (sum_le_sum ?_).trans (l i); intro j _; simp only [eq_comm (a:=i)]; split; swap; exact le_rfl
 unfold BudgetPoint.mass; refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le; unfold chipT; split; exact le_rfl; exact grit_p P (t j) (zero_le_one.trans v)
omit p v
-- geometry normal chart and cost
lemma crop_p(X:Hz)(h:Fintype.card (Fin 6) ≤P.B):coverNumber P.B (Taxi.villa X) ≤ coverNumber P.B X.val.2+81:=by
 let Z:= X.val.2; let o:= X.val.1; have ht:=Corona.meets_sum X.property (halo_subset 6 _ (mem_singleton_self o)) P.B
 refine ht.trans (Nat.add_le_add_left ?_ _)
 have he:=Corona.tile o 1 P.B P.B_pos; exact (Corona.cover_mono (Corona.halo_mono (by simpa using h) (Subset.refl _)) _).trans he
abbrev hinge_P(B L:ℕ):=(L+81)*(4*B+2)+2*B
lemma reachX(X:Hz)(h:chute P L X)(y:Xo)(u:y∈ villa X)(hp:6 ≤P.B):separation X.val.1 y≤ hinge_P P.B L:=by
 let V:= coverNumber P.B X.val.2; have hx: V^3 < L:=h; have hv:V≤L:=by by_cases p: 1≤V; exact ((pow_one V).symm.trans_le (pow_le_pow_right₀ p (show 1≤3 by decide))).trans hx.le; omega
 exact (Corona.extent (villa X) P.B (stateT X).property u).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ ((crop_p P X (by simpa using hp)).trans (Nat.add_le_add_right hv _))) _)
lemma latch_K(x:ℝ)(p:0≤x)(Y:Hz)(h:6 ≤ P.B) : P.mass (villa Y) x ≤ Real.exp (81*Ω) *P.mass Y.val.2 x:=by
 unfold BudgetPoint.mass; rw [← mul_assoc, ← Real.exp_add]; refine mul_le_mul_of_nonneg_right (Real.exp_monotone ?_) p; have hp:(coverNumber P.B (villa Y):ℝ) ≤coverNumber P.B Y.val.2+ 81:=by exact_mod_cast crop_p P Y (by simpa using h)
 nlinarith [P.exponent_pos]
lemma roof_P(h:6≤ P.B)(t:10*hinge_P P.B L < (More n).val)(X:Hz)(p:Pave P L X.val.2):Nonwrapping (villa X) X.val.1:=by intro i v; rw [separation_comm]; exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (reachX P L X p i v h)) t
end YM.CF.Beau
