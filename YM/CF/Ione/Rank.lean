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
abbrev bushV (s:Sweep n)(A:Finset (Dwell n)→ℝ)(k:ℕ):Finset (Dwell n)→ℝ:=fun i=>if i.card=k then ∑ j:Finset (Dwell n),‖(hail_Q s).val i j‖* A j else 0
def cast_B(t:Bool):ℂ→L[ℝ]ℂ:= if t then Complex.conjCLE else ContinuousLinearMap.id ℝ ℂ
lemma castT(t:Bool)(v:ℂ): cast_B t v=cSignX t v:=by cases t<;>rfl
lemma cap_X(t:Bool): ‖cast_B t‖ ≤ 1:=by refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun i=>?_ ; cases t; rw [one_mul]; exact le_rfl; change ‖star i‖≤1*‖i‖; simp
lemma star_P {F:tangD n→ℂ}(i:ℂ){v:ℝ}{p:Seat n}(t:Signs P p F v)(b:Bool): Signs P p (fun x=>i*cSignX b (F x)) (‖i‖*v):=by
 let L:ℂ→L[ℝ]ℂ:=i • cast_B b; have hl: ‖L‖≤ ‖i‖:= (norm_smul i (cast_B b)).trans_le (mul_le_of_le_one_right (norm_nonneg _) (cap_X _)); apply skills; simp_rw [←castT]; exact (skin t).linear L hl
lemma tariff_Q (F:Φg→ℝ)(v:0≤F)(G H:Φg→ℝ)(T:∀ i j:Φg,HQ i j≠0→G i ≤H j)(Z:0 ≤ H): joinV G (bushV s F k)≤ (fare_T k:ℝ)*joinV H F:=by
 unfold joinV; let B:= (univ:Finset (Finset (Dwell n))).filter fun i=>i.card=k
 rw [←sum_subset (subset_univ B) (fun i _ g=> by rw [show bushV s F k i=0 from if_neg fun v=> g (mem_filter.mpr ⟨mem_univ _,v⟩),mul_zero])]; rw [sum_congr rfl (g:=fun i=>∑ j:Φg,(‖HQ i j‖ * F j)*G i) ?_]; swap; · intro i p; rw [mul_comm,bushV,if_pos (mem_filter.mp p).2,sum_mul]
 rw [sum_comm,mul_sum]; apply sum_le_sum; intro i _; have hp:= sum_le_sum (f:=fun j:Φg=> ‖HQ j i‖*F i* G j) (s:=B) (g:=fun j=> ‖HQ j i‖* (H i*F i)) fun j _=> by
    by_cases h:HQ j i=0; simp [h]; refine (mul_le_mul_of_nonneg_left (T j i h) (mul_nonneg (norm_nonneg _) (v _))).trans_eq ?_; ring
 apply hp.trans; rw [←sum_mul]; apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Z i) (v i)); by_cases h:i.card=k; · apply (sum_le_sum_of_subset_of_nonneg (subset_univ B) (fun j _ _=>norm_nonneg _)).trans; rw [←h]; exact trill_Q s i
 rw [sum_eq_zero]; positivity
 intro j p; rw [show HQ j i=0 from (Classical.byContradiction fun w=> h (((inkE s j i w).symm.trans (mem_filter.mp p).2))),norm_zero] -- tune
lemma bush_p (A:Finset (Dwell n)→ℝ)(p:0≤A):0 ≤ bushV s A k:=by intro i; unfold bushV; split; exact sum_nonneg (fun j _=>mul_nonneg (norm_nonneg _) (p _)); exact le_rfl
-- reg.Ref.S harvest
variable {F:InkD n}(p:Scree.Hub n)(c':ℝ)(V:Pane n)
abbrev step_F(s:Sweep n)(F:InkD n): InkD n:=suit_Y s⁻¹ ∘ F ∘ flashA s
abbrev restK (F:InkD n):InkD n:= wage_Q 2 ∘ F
lemma gauge_E (G:Seat n→ SU.E)(Y:Cipher n):suit_Y s⁻¹ (paintR false false (tradew n ((polarT s.charge ∘ G) ∘ (castX s).anon n)) Y) = paintR false false (tradew n G) (suit_Y s⁻¹ Y):=by
 let U:=suit_Y s⁻¹ Y; have ht:suit_Y s U=Y:=by unfold U; rw [moon_Y,inv_mul_cancel,toon_Q]
 nth_rw 1 [←ht]; rw [←boom_Q,moon_Y,mul_inv_cancel,toon_Q]; -- tune
abbrev duty_Q(k p:ℕ):=composeCost k 1 ((2:ℝ)^p)
lemma consume_F (t:PressB P (moveHub s p) F h c')(x:0≤h): PressB P p (step_F s (restK F)) h ((fare_T 2:ℝ)*(duty_Q P.order P.power*c')):=by
 let Y:= moveHub s p; let o:=Y.val.1; let e:=Y.val.2; have hp:boxA s o=p.val.1:=(boxA s).apply_symm_apply _; have hz: actY s⁻¹ Y.val.2=p.val.2:=by unfold Y; ext; simp [actY,moveHub, sitU]
 refine ⟨fun i j v=>?_ ,fun V=>hz ▸ rich_F s⁻¹ Y.val.2 _ (worthS 2 _ _ (t.fitted (flashA s V))),((suit_Y s⁻¹).toLinearMap.continuous_of_finiteDimensional).measurable.comp (((peek_P 2).measurable.comp t.measureV).comp (revM s).measurable),fun V g=>?_ ,?_⟩
 · refine congrArg (suit_Y s⁻¹) (congrArg (wage_Q 2) (t.term _ _ ?_)) -- tune
   apply flashD; rw [show (moveHub s p).val.2.map (boxA s).toEmbedding=p.val.2 from by ext; simp [moveHub]]; exact v
 · simp only [step_F, restK,Function.comp_apply]; rw [revG,t.gaugeV,pose_U]; exact gauge_E s g _
 obtain ⟨A,v,f,g⟩:=t.worth; let r:= P.order; let K(i):= composeCost P.order (A i) ((2:ℝ)^P.power); have hb(i):K i=duty_Q P.order P.power*A i:=by unfold K duty_Q composeCost; ring
 have hu:0 ≤ duty_Q P.order P.power:=by unfold duty_Q composeCost; positivity
 have hv:0 ≤ K:=fun i=>(hb i).symm ▸ (mul_nonneg hu (v i))
 refine ⟨bushV s⁻¹ K 2,bush_p s⁻¹ K hv,?_,?_⟩; swap
 · have ht:= tariff_Q (k:=2) s⁻¹ K hv (Scree.tariff P p.val.1 h) (Scree.tariff P o h) (fun i j hx=>by rw [←hp]; exact (show (boxA s⁻¹).symm=boxA s from by rw [sitU]; rfl) ▸ (tune_L s⁻¹ i j o P hx h x)) (fun i=>by unfold Scree.tariff; exact mul_nonneg (pow_nonneg (by positivity) _) (pow_nonneg x _)) -- tune dependent notation
   refine ht.trans (mul_le_mul_of_nonneg_left ?_ (by positivity)); unfold joinV; simp_rw [hb, mul_left_comm _ (duty_Q _ _),←mul_sum]; exact mul_le_mul_of_nonneg_left g hu -- simp bomb
 intro V p' i; let Z:= door_b s V; let W:= flashA s V; let C:= s⁻¹; let R:= fun j:Φg=> fun x:tangD n=> crumb (F (increment W (Z x))).val j
 have hf := f W ((glowA ..).mpr p'); have h' (j:Φg): Signs P p.val.1 (R j) (K j):= hp ▸ port_l P s V (hf j)
 let T' (j:DN):= step_F s (restK F) (increment V j)
 change Signs P p.val.1 (fun j=>crumb (T' j).val i) (bushV _ _ _ _); have hx(x:DN): crumb (T' x).val i=if i.card=2 then ∑ j:Φg,(hail_Q C).val i j * Spire.payZ C (R j x) else 0:=by
    unfold T' step_F restK; simp only [Function.comp_apply,tour_p]; rw [show suit_Y s⁻¹ (wage_Q 2 _)=wage_Q 2 _ from (pose_U ..).symm,price_X,roseQ]; -- tune
 unfold bushV; split; next g=> simp_rw [hx,if_pos g]; exact haloI (fun j (_:j∈(univ:Finset Φg))=> star_P P _ (h' j) (wageZ C))
 next g=> simp_rw [hx,if_neg g]; exact hail (show ‖(0:ℂ)‖≤0 by rw [norm_zero]) -- tune
end YM.CF.Ione
