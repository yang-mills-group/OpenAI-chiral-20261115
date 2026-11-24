import SatinThinMonomial
import YM.CF.Ione.Mesh

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
open Ione
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

-- The FULL cost, not bushV on rank two. Adapt Ione/Rank.
abbrev bankY(s:Sweep n)(A:Finset (Dwell n)→ℝ):Finset (Dwell n)→ℝ:=fun i=>∑ j:Φg,‖(hail_Q s).val i j‖ * A j
lemma bank_p (A:Finset (Dwell n)→ℝ)(p:0≤A):0 ≤ bankY s A:= fun i=> sum_nonneg (fun j _ => mul_nonneg (norm_nonneg _) (p _))
lemma taxiQ (g:s∈cycleSweep n)(F:Φg→ℝ)(v:0≤F)(G H:Φg→ℝ)(T:∀ i j:Φg,HQ i j≠0→G i ≤H j)(Z:0 ≤ H): joinV G (bankY s F)≤joinV H F:=by
 unfold joinV bankY; simp_rw [mul_sum]; rw [sum_comm]; refine sum_le_sum fun i _=>?_ ; have hp:= sum_le_sum (g:=fun j:Φg=> ‖HQ j i‖ * (H i*F i)) (s:=univ) (f:=fun j:Φg=> G j*(‖HQ j i‖*F i)) fun j _=> by
    by_cases h:HQ j i=0; simp [h]; rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (T j i h) (v _)) (norm_nonneg _)
 refine hp.trans ?_; rw [←sum_mul]; exact mul_le_of_le_one_left (mul_nonneg (Z _) (v _)) (penny s g _)

variable {F:InkD n}(p:Scree.Hub n)(c':ℝ)(V:Pane n)
lemma consume_Q (hg:s∈cycleSweep n)(t:PressB P (moveHub s p) F h c')(x:0≤h): PressB P p (step_F s F) h (duty_Q P.order P.power*c'):=by
 let Y:= moveHub s p; let o:=Y.val.1; let e:=Y.val.2; have hp:boxA s o=p.val.1:=(boxA s).apply_symm_apply _; have hz: actY s⁻¹ Y.val.2=p.val.2:=by unfold Y; ext; simp [actY,moveHub, sitU]
 refine ⟨fun i j v=>?_ ,fun V=>hz ▸ rich_F s⁻¹ Y.val.2 _ (t.fitted (flashA s V)),((suit_Y s⁻¹).toLinearMap.continuous_of_finiteDimensional).measurable.comp (t.measureV.comp (revM s).measurable),fun V g=>?_ ,?_⟩
 · refine congrArg (suit_Y s⁻¹) (t.term _ _ ?_) -- tune
   apply flashD; rw [show (moveHub s p).val.2.map (boxA s).toEmbedding=p.val.2 from by ext; simp [moveHub]]; exact v
 · simp only [step_F,Function.comp_apply]; rw [revG,t.gaugeV]; exact gauge_E s g _
 obtain ⟨A,v,f,g⟩:=t.worth; let r:= P.order; let K(i):= composeCost P.order (A i) ((2:ℝ)^P.power); have hb(i):K i=duty_Q P.order P.power*A i:=by unfold K duty_Q composeCost; ring
 have hu:0 ≤ duty_Q P.order P.power:=by unfold duty_Q composeCost; positivity
 have hv:0 ≤ K:=fun i=>(hb i).symm ▸ (mul_nonneg hu (v i))
 refine ⟨bankY s⁻¹ K,bank_p s⁻¹ K hv,?_,?_⟩; swap
 · have ht:= taxiQ s⁻¹ ((cycleSweep n).inv_mem hg) K hv (Scree.tariff P p.val.1 h) (Scree.tariff P o h) (fun i j hx=>by rw [←hp]; exact (show (boxA s⁻¹).symm=boxA s from by rw [sitU]; rfl) ▸ (tune_L s⁻¹ i j o P hx h x)) (fun i=>by unfold Scree.tariff; exact mul_nonneg (pow_nonneg (by positivity) _) (pow_nonneg x _)) -- tune dependent notation
   refine ht.trans ?_; unfold joinV; simp_rw [hb, mul_left_comm _ (duty_Q _ _),←mul_sum]; exact mul_le_mul_of_nonneg_left g hu -- simp bomb
 intro V p' i; let Z:= door_b s V; let W:= flashA s V; let C:= s⁻¹; let R:= fun j:Φg=> fun x:tangD n=> crumb (F (increment W (Z x))).val j
 have hf := f W ((glowA ..).mpr p'); have h' (j:Φg): Signs P p.val.1 (R j) (K j):= hp ▸ port_l P s V (hf j)
 let T' (j:DN):= step_F s F (increment V j)
 change Signs P p.val.1 (fun j=>crumb (T' j).val i) (bankY _ _ _); have hx(x:DN): crumb (T' x).val i=∑ j:Φg,(hail_Q C).val i j * Spire.payZ C (R j x):=by
    unfold T' step_F; simp only [Function.comp_apply,tour_p]; rw [roseQ]
 unfold bankY; simp_rw [hx]; exact haloI (fun j (_:j∈(univ:Finset Φg))=> star_P P _ (h' j) (wageZ C))

section
variable {F:Copy n} (X D:Support (More n))
lemma medal_all (s:Sweep n)(hg:s∈cycleSweep n)(p:Vow.Medal P (actY s X) (actY s D) F h a)(hv:0 ≤ h): Vow.Medal P X D (turn_V s F) h (strive_E P.order*a):=by
 let K:=suit_Y s⁻¹; refine ⟨⟨fun i j h c=> ?_ , fun i=> tape_C s X ▸ rich_F s⁻¹ _ _ (p.lit (yellA s i)), (K.toLinearMap.continuous_of_finiteDimensional).measurable.comp (p.keeps.comp (((revM s).measurable.comp measurable_fst).prodMk ((tuft s).measurable.comp measurable_snd))),fun (V:Orbit n) g=>?_⟩, ?_⟩
 · obtain ⟨x,t⟩:= yellow s i j X h c; exact congrArg K (p.same _ _ x t)
 · let f:= (polarT s.charge ∘g) ∘ (castX s).anon n; have hV: yellA s (Lattice.gauge g V.1, threadG g V.2)=(Lattice.gauge f (flashA s V.1),threadG f (bun s V.2)):=by
      refine Prod.ext (revG ..) (funext fun i=> ?_); change bun s (threadG g V.2) i= threadG f (bun s V.2) i; simp only [bun,man,threadG, map_mul,map_inv]; rfl
   simp only [turn_V,Function.comp_apply,hV]; rw [show F _= _ from p.gaugeX (yellA s V) f]; exact gauge_E s g _ -- tune
 obtain ⟨C,v,j,w⟩:=p.pays; let o:= P.order; let B(z):= (o+1:ℝ)*composeCost o (o.factorial*C z) 1; have hb(k):B k=strive_E o*C k:=by unfold B strive_E composeCost; ring
 have he:0 ≤ strive_E o:=by unfold strive_E composeCost; positivity
 have hB:0 ≤ B:=fun i=>(hb i).symm ▸ (mul_nonneg he (v i))
 refine ⟨bankY s⁻¹ B,bank_p s⁻¹ B hB, ?_, ?_⟩; swap
 · have ht:= taxiQ s⁻¹ ((cycleSweep n).inv_mem hg) B hB (Wray.stake h) (Wray.stake h) (fun i j hx=>by unfold Wray.stake; rw [inkE s⁻¹ i j hx]) (fun i=>pow_nonneg hv _); refine ht.trans ?_; unfold joinV; simp_rw [hb,mul_left_comm _ (strive_E _),←mul_sum]; exact mul_le_mul_of_nonneg_left w he -- namespace stake
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
    unfold Yt turn_V; simp only [yellA,Function.comp_apply,parl_v]; rw [roseQ]
 let U:=fun j:Φg=> (hail_Q s⁻¹).val i j • Q j; rw [show (fun z=>crumb (Yt z).val i)=∑ j:Φg,U j from funext fun z=>Eq.trans (hY z) (by rw [Finset.sum_apply]; rfl)]
 exact Pence.money fun j _=> (hq j).σ _

end
variable {E:RegBudget n}
open Larch
lemma earth_Q (z:s∈cycleSweep n)(p:IncX (fun _ :Sweep n=>False) E P h a)(v:0≤h): IncX (fun _=>False) (base_Q s E) P h (duty_Q P.order P.power*a):=by
 obtain ⟨F,p,j⟩:=p.weight; let H:= duty_Q P.order P.power
 refine ⟨⟨fun i=> H*F (moveHub s i),fun i=>?_ ,fun i=>?_⟩,fun _ t=>t.elim⟩
 · exact consume_Q P s _ _ z (p _) v -- supply args
 apply le_trans _ (mul_le_mul_of_nonneg_left (j ((boxA s).symm i)) (by unfold duty_Q composeCost; positivity)); rw [mul_sum]; conv_rhs=>rw [←Equiv.sum_comp (scope_q s)] -- direction occurrence
 apply le_of_eq; apply sum_congr rfl; intro j _; change ite _ _ _=_; split_ifs with v p h
 · have hp:= mold_q P s j; unfold BudgetPoint.mass; rw [show coverNumber _ (scope_q s j).val.2= _ from glow_q s P.B j.val.2]; change (Trees.currency P.B P.supportExponent j.val.2)*(H*F _)=H*(Trees.currency _ _ _* F (moveHub s j)); ring
 · exact False.elim (p (congrArg (boxA s).symm v))
 · exact False.elim (v ((boxA s).symm.injective h))
 rw [mul_zero]
end YM.CF.QuadClock
