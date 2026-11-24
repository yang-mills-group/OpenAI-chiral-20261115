import YM.CF.Ione.Tape
import YM.SU5.Silk.Clock.Duty
import YM.CF.Ione.Rank
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Links
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Ione
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
variable {X D Y Z:Support (More n)}
open Vow Salt
variable (P:BudgetPoint)(s:Sweep n)
local notation "Ta"=> actY s
local notation "HQ"=> (hail_Q s).val
local notation "Φg"=> (Finset (Dwell n))
variable {F: Copy n} (T X D Y':Support (More n))(V':Orbit n)
open Clock
lemma full_medal (s:Sweep n)(sW:s∈Whirl n)(p:Vow.Medal P (actY s X) (actY s D) F h a)(hv:0 ≤ h): Vow.Medal P X D (turn_V s F) h (strive_E P.order*a):=by
 let K:=suit_Y s⁻¹; refine ⟨⟨fun i j h c=> ?_ , fun i=> tape_C s X ▸ rich_F s⁻¹ _ _ (p.lit (yellA s i)), (K.toLinearMap.continuous_of_finiteDimensional).measurable.comp (p.keeps.comp (((revM s).measurable.comp measurable_fst).prodMk ((tuft s).measurable.comp measurable_snd))),fun (V:Orbit n) g=>?_⟩, ?_⟩
 · obtain ⟨x,t⟩:= yellow s i j X h c; exact congrArg K (p.same _ _ x t)
 · let f:= (polarT s.charge ∘g) ∘ (castX s).anon n; have hV: yellA s (Lattice.gauge g V.1, threadG g V.2)=(Lattice.gauge f (flashA s V.1),threadG f (bun s V.2)):=by
      refine Prod.ext (revG ..) (funext fun i=> ?_); change bun s (threadG g V.2) i= threadG f (bun s V.2) i; simp only [bun,man,threadG, map_mul,map_inv]; rfl
   simp only [turn_V,Function.comp_apply,hV]; rw [show F _= _ from p.gaugeX (yellA s V) f]; exact gauge_E s g _ -- tune
 obtain ⟨C,v,j,w⟩:=p.pays; let o:= P.order; let B(z):= (o+1:ℝ)*composeCost o (o.factorial*C z) 1; have hb(k):B k=strive_E o*C k:=by unfold B strive_E composeCost; ring
 have he:0 ≤ strive_E o:=by unfold strive_E composeCost; positivity
 have hB:0 ≤ B:=fun i=>(hb i).symm ▸ (mul_nonneg he (v i))
 refine ⟨allV s⁻¹ B,all_p s⁻¹ B hB, ?_, ?_⟩; swap
 · have ht:= full_tariff s⁻¹ (inv_mem sW) B hB (Wray.stake h) (Wray.stake h) (fun i j hx=>by unfold Wray.stake; rw [inkE s⁻¹ i j hx]) (fun i=>pow_nonneg hv _); refine ht.trans ?_; unfold joinV; simp_rw [hb,mul_left_comm _ (strive_E _),←mul_sum]; exact mul_le_mul_of_nonneg_left w he -- namespace stake
 intro V t Y y; have hc: actY s (X\D)= actY s X \ actY s D:=by unfold actY; rw [Finset.map_sdiff]; -- macro actY s shadow
 let W:= yellA s V; have h':= j W ((hc ▸ (glowA ..|>.mpr t))) (show actY s D ⊆ actY s Y from Finset.map_subset_map.mpr y); let F':=fun i:DN=> F (pressQ P (actY s Y) W.1 i,W.2); let Vx:=door_b s V.1
 have ht: ‖Vx‖ ≤1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun i=> by rw [one_mul]; exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun b=> (cod_E s V.1 i b).trans_le (norm_le_pi_norm ..)
 let Q(v:Φg)(i:DN):= Spire.payZ s⁻¹ (crumb (F' (Vx i)).val v)
 have hq(z:Φg): Pence o (Q z) 0 (B z):=by
    let Yt:= composeCost o (o.factorial*C z) 1; let Y'(i:DN):= crumb (F' i).val z; have h':Allows o Y' (Vx 0) ((o.factorial:ℝ)* C z):= (map_zero Vx).symm ▸ (h'.haveP z).pay
    have hp:= h'.comp (allows_linear ht (show ‖Vx 0‖ ≤1 from by rw [map_zero,norm_zero]; exact zero_le_one)); unfold Q Spire.payZ; simp_rw [←castT]; apply Rue.bare_p _ Yt; refine (show Allows o _ _ Yt from ?_); rw [←one_mul Yt] -- tune
    exact hp.linear (cast_B (wageZ _)) (cap_X _)
 let Yt(i:DN):=turn_V s F (pressQ P Y V.1 i,V.2); refine ⟨Eventually.of_forall (fun i=> (fineShape (Yt i)).allP),fun i=>?_ ⟩
 change Pence o (fun z=>crumb (Yt z).val i) 0 _; have hY(z:DN): crumb (Yt z).val i= ∑ j:Φg,(hail_Q s⁻¹).val i j * Q j z:=by
    unfold Yt turn_V; simp only [yellA,Function.comp_apply,parl_v]; exact roseQ ..
 unfold allV; let V:=fun j:Φg=> (hail_Q s⁻¹).val i j • Q j; rw [show (fun z=> crumb (Yt z).val i)=∑ j:Φg,V j from funext fun z=> Eq.trans (hY z) (by rw [Finset.sum_apply]; rfl)]; exact Pence.money fun j _=> (hq j).σ _
end YM.CF.Ione
