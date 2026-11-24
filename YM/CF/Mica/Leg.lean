import YM.CF.Beau.Pour
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
-- reg.Ref.S harvest
variable {F:InkD n}(p:Scree.Hub n)(c':ℝ)(V:Pane n)
abbrev sage_L (F:InkD n):InkD n:= wage_Q 0 ∘ F
lemma swirl_x (t:PressB P (moveHub s p) F h c')(x:0≤h): PressB P p (step_F s (sage_L F)) h ((fare_T 0:ℝ)*(duty_Q P.order P.power*c')):=by
 let Y:= moveHub s p; let o:=Y.val.1; let e:=Y.val.2; have hp:boxA s o=p.val.1:=(boxA s).apply_symm_apply _; have hz: actY s⁻¹ Y.val.2=p.val.2:=by unfold Y; ext; simp [actY,moveHub, sitU]
 refine ⟨fun i j v=>?_ ,fun V=>hz ▸ rich_F s⁻¹ Y.val.2 _ (worthS 0 _ _ (t.fitted (flashA s V))),((suit_Y s⁻¹).toLinearMap.continuous_of_finiteDimensional).measurable.comp (((peek_P 0).measurable.comp t.measureV).comp (revM s).measurable),fun V g=>?_ ,?_⟩
 · refine congrArg (suit_Y s⁻¹) (congrArg (wage_Q 0) (t.term _ _ ?_)) -- tune
   apply flashD; rw [show (moveHub s p).val.2.map (boxA s).toEmbedding=p.val.2 from by ext; simp [moveHub]]; exact v
 · simp only [step_F, sage_L,Function.comp_apply]; rw [revG,t.gaugeV,pose_U]; exact gauge_E s g _
 obtain ⟨A,v,f,g⟩:=t.worth; let r:= P.order; let K(i):= composeCost P.order (A i) ((2:ℝ)^P.power); have hb(i):K i=duty_Q P.order P.power*A i:=by unfold K duty_Q composeCost; ring
 have hu:0 ≤ duty_Q P.order P.power:=by unfold duty_Q composeCost; positivity
 have hv:0 ≤ K:=fun i=>(hb i).symm ▸ (mul_nonneg hu (v i))
 refine ⟨bushV s⁻¹ K 0,bush_p s⁻¹ K hv,?_,?_⟩; swap
 · have ht:= tariff_Q (k:=0) s⁻¹ K hv (Scree.tariff P p.val.1 h) (Scree.tariff P o h) (fun i j hx=>by rw [←hp]; exact (show (boxA s⁻¹).symm=boxA s from by rw [sitU]; rfl) ▸ (tune_L s⁻¹ i j o P hx h x)) (fun i=>by unfold Scree.tariff; exact mul_nonneg (pow_nonneg (by positivity) _) (pow_nonneg x _)) -- tune dependent notation
   refine ht.trans (mul_le_mul_of_nonneg_left ?_ (by positivity)); unfold joinV; simp_rw [hb, mul_left_comm _ (duty_Q _ _),←mul_sum]; exact mul_le_mul_of_nonneg_left g hu -- simp bomb
 intro V p' i; let Z:= door_b s V; let W:= flashA s V; let C:= s⁻¹; let R:= fun j:Φg=> fun x:tangD n=> crumb (F (increment W (Z x))).val j
 have hf := f W ((glowA ..).mpr p'); have h' (j:Φg): Signs P p.val.1 (R j) (K j):= hp ▸ port_l P s V (hf j)
 let T' (j:DN):= step_F s (sage_L F) (increment V j)
 change Signs P p.val.1 (fun j=>crumb (T' j).val i) (bushV _ _ _ _); have hx(x:DN): crumb (T' x).val i=if i.card=0 then ∑ j:Φg,(hail_Q C).val i j * Spire.payZ C (R j x) else 0:=by
    unfold T' step_F sage_L; simp only [Function.comp_apply,tour_p]; rw [show suit_Y s⁻¹ (wage_Q 0 _)=wage_Q 0 _ from (pose_U ..).symm,price_X,roseQ]; -- tune
 unfold bushV; split; next g=> simp_rw [hx,if_pos g]; exact haloI (fun j (_:j∈(univ:Finset Φg))=> star_P P _ (h' j) (wageZ C))
 next g=> simp_rw [hx,if_neg g]; exact hail (show ‖(0:ℂ)‖≤0 by rw [norm_zero]) -- tune
end YM.CF.Ione
