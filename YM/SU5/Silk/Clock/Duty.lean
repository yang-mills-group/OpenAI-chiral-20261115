import YM.CF.Ione.Rank
import YM.SU5.Silk.Clock.Ion
import YM.CF.Ione.Lark
import YM.CF.Ione.Crore
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
open Clock
abbrev allV (s:Sweep n)(A:Finset (Dwell n)→ℝ)(i:Finset (Dwell n)):ℝ:=∑ j:Finset (Dwell n),‖(hail_Q s).val i j‖* A j
lemma all_p (A:Φg→ℝ)(p:0≤A):0 ≤ allV s A:= fun i=> Finset.sum_nonneg (fun j _=>mul_nonneg (norm_nonneg _) (p _))
lemma full_tariff(hS:s∈ Whirl n)(F:Φg→ℝ)(v:0≤F)(G H:Φg→ℝ)(T:∀ i j:Φg,HQ i j≠0→G i ≤H j)(Z:0 ≤ H): joinV G (allV s F)≤ joinV H F:=by
 unfold joinV; rw [sum_congr rfl (g:=fun i=>∑ j:Φg,(‖HQ i j‖ * F j)*G i) ?_]; swap; · intro i _; rw [mul_comm,allV,sum_mul]
 rw [sum_comm]; apply sum_le_sum; intro i _; have hp:= sum_le_sum (f:=fun j:Φg=> ‖HQ j i‖*F i* G j) (s:=univ) (g:=fun j=> ‖HQ j i‖* (H i*F i)) fun j _=> by
    by_cases h:HQ j i=0; simp [h]; refine (mul_le_mul_of_nonneg_left (T j i h) (mul_nonneg (norm_nonneg _) (v _))).trans_eq ?_; ring
 apply hp.trans; rw [←sum_mul]; exact mul_le_of_le_one_left (mul_nonneg (Z _) (v _)) (fee_column s hS i)
variable {F:InkD n}(p:Scree.Hub n)(c':ℝ)(V:Pane n)
lemma pay_all_F (sW:s∈ Whirl n)(t:PressB P (moveHub s p) F h c')(x:0≤h): PressB P p (step_F s F) h (duty_Q P.order P.power*c'):=by
 let Y:= moveHub s p; let o:=Y.val.1; let e:=Y.val.2; have hp:boxA s o=p.val.1:=(boxA s).apply_symm_apply _; have hz: actY s⁻¹ Y.val.2=p.val.2:=by unfold Y; ext; simp [actY,moveHub, sitU]
 refine ⟨fun i j v=>?_ ,fun V=>hz ▸ rich_F s⁻¹ Y.val.2 _ (t.fitted (flashA s V)),((suit_Y s⁻¹).toLinearMap.continuous_of_finiteDimensional).measurable.comp (t.measureV.comp (revM s).measurable),fun V g=>?_ ,?_⟩
 · refine congrArg (suit_Y s⁻¹) (t.term _ _ ?_) -- tune
   apply flashD; rw [show (moveHub s p).val.2.map (boxA s).toEmbedding=p.val.2 from by ext; simp [moveHub]]; exact v
 · simp only [step_F,Function.comp_apply]; rw [revG,t.gaugeV]; exact gauge_E s g _
 obtain ⟨A,v,f,g⟩:=t.worth; let r:= P.order; let K(i):= composeCost P.order (A i) ((2:ℝ)^P.power); have hb(i):K i=duty_Q P.order P.power*A i:=by unfold K duty_Q composeCost; ring
 have hu:0 ≤ duty_Q P.order P.power:=by unfold duty_Q composeCost; positivity
 have hv:0 ≤ K:=fun i=>(hb i).symm ▸ (mul_nonneg hu (v i))
 refine ⟨allV s⁻¹ K,all_p s⁻¹ K hv,?_,?_⟩; swap
 · have ht:= full_tariff s⁻¹ (inv_mem sW) K hv (Scree.tariff P p.val.1 h) (Scree.tariff P o h) (fun i j hx=>by rw [←hp]; exact (show (boxA s⁻¹).symm=boxA s from by rw [sitU]; rfl) ▸ (tune_L s⁻¹ i j o P hx h x)) (fun i=>by unfold Scree.tariff; exact mul_nonneg (pow_nonneg (by positivity) _) (pow_nonneg x _)) -- tune dependent notation
   refine ht.trans ?_; unfold joinV; simp_rw [hb, mul_left_comm _ (duty_Q _ _),←mul_sum]; exact mul_le_mul_of_nonneg_left g hu -- simp bomb
 intro V p' i; let Z:= door_b s V; let W:= flashA s V; let C:= s⁻¹; let R:= fun j:Φg=> fun x:tangD n=> crumb (F (increment W (Z x))).val j
 have hf := f W ((glowA ..).mpr p'); have h' (j:Φg): Signs P p.val.1 (R j) (K j):= hp ▸ port_l P s V (hf j)
 let T' (j:DN):= step_F s F (increment V j)
 change Signs P p.val.1 (fun j=>crumb (T' j).val i) (allV _ _ _); have hx(x:DN): crumb (T' x).val i=∑ j:Φg,(hail_Q C).val i j * Spire.payZ C (R j x):=by
    unfold T' step_F; simp only [Function.comp_apply,tour_p]; exact roseQ ..
 unfold allV; simp_rw [hx]; exact haloI (fun j (_:j∈(univ:Finset Φg))=> star_P P _ (h' j) (wageZ C))
end YM.CF.Ione
