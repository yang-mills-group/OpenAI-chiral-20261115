import SatinThinShelter
import YM.SU5.Silk.Clock.Ion

/-!
# Step symmetry enlargement for the physical pseudoscalar

The old `cycleSweep` fixes the individual planes. Use the (generated)
plane-pair group, with **both** charge choices. Keep the same duty rsp.
strive multiplier (don't pay twice by composing lifts). Applications include
averaging Ice in the Ward and clover programs.

Extends SatinThin{Duty,Monomial,Tooth,Shelter}, ..Silk.Clock.Ion.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false
set_option quotPrecheck false

noncomputable section
namespace YM.CF.QuadClock
open Spire Ione Fock Lat Lattice Wilson Laurent Rush Drapes Fir Peaks Dial Paige Scroll Hive Cube Skye
open Matrix Thera Levier Urn Hake Pastry Scree Stilo
open Function Filter Finset
open scoped Classical Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Ione.Clock

def twoPlanes (n : Side) : Subgroup (Sweep n) where
  carrier := {s | s.s ∈ Loomed}
  one_mem' := Loomed.one_mem
  mul_mem' := fun _ _ => Loomed.mul_mem ‹_› ‹_›
  inv_mem' := fun {x} h => back_l x.s h

lemma mem_twoPlanes {n : Side} {s : Sweep n} : s ∈ twoPlanes n ↔ s.s ∈ Loomed := Iff.rfl

lemma reSweep_twoPlanes {n m : Side} (G : Ratio n m) {s : Sweep n} (a : s ∈ twoPlanes n) :
    reSweep G s ∈ twoPlanes m := a

-- true-charge argument also, directly (one spin-column test adapted from Ion).
theorem spinningWithCharge (p : Signed) (hp : p ∈ Loomed) (c : Bool)
    (U : UNI SpinIdx) (t : JetS p c (detX p) U) : Column U.val := by
  cases c; exact spinning p hp U t
  have hd (X : SpinIdx → ℂ) : windX true (diagonal X) = diagonal (star X) := by
    ext i j; by_cases k : i=j; subst j; simp [windX]; simp [windX,k]
  intro i j k a b
  apply phase_unique
  · have h := t.grade
    rw [singT, grad_eq, hd] at h
    cases v : detX p <;> rw [v] at h
    · exact equiv_column U _ _ h i j k a b
    rw [hush_true,diagonal_neg] at h; simpa using equiv_column U _ _ h i j k a b
  obtain ⟨u,h⟩ := group_product _ _ (color_l p hp 0 1 (by decide)) (p.perm.injective.ne (by decide: (0:Axis)≠1))
  have he : twist U (windX true (diagonal u)) = hush (p.flip 0) (gammaOp 0) * hush (p.flip 1) (gammaOp 1) := by
    rw [←h, win_m, map_mul]; exact congrArg₂ _ (t.cliff _) (t.cliff _)
  rw [hd u] at he
  cases q:p.flip 0 <;> cases g:p.flip 1 <;>
    simp only [q,g,hush_false,hush_true,neg_mul,mul_neg,neg_neg,inf_eq,diagonal_neg] at he <;>
    simpa only [Pi.neg_apply, neg_inj] using equiv_column U _ _ he i j k a b

theorem column_two {n : Side} (p : Sweep n) (hp : p ∈ twoPlanes n) :
    Column (hail_Q p).val :=
  distill_l (praise _) (spice_column (siteU ..)
    (prep_column _ _ _ _ (spinningWithCharge _ (mem_twoPlanes.mp hp) _ _ (spinZ ..))) _)

lemma fee_column_two {n:Side}(s:Sweep n)(hs:s∈twoPlanes n)(i:Finset (Dwell n)):
    (∑ j:Finset (Dwell n),‖(hail_Q s).val j i‖) ≤ 1:= by
 obtain ⟨f,h⟩:=nice_eq (hail_Q s) (column_two s hs)
 rw [sum_eq_single (f i)]; · exact (norm_entry ..).trans (CStarRing.norm_of_mem_unitary (hail_Q s).property).le
 · intro j _ p; rw [show (hail_Q s).val j i=0 from Classical.byContradiction fun w=>p (h _ _ w),norm_zero]
 simp

end YM.CF.QuadClock

-- Adapted: SatinThinDuty
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
lemma taxiTwo (g:s∈twoPlanes n)(F:Φg→ℝ)(v:0≤F)(G H:Φg→ℝ)(T:∀ i j:Φg,HQ i j≠0→G i ≤H j)(Z:0 ≤ H): joinV G (bankY s F)≤joinV H F:=by
 unfold joinV bankY; simp_rw [mul_sum]; rw [sum_comm]; refine sum_le_sum fun i _=>?_ ; have hp:= sum_le_sum (g:=fun j:Φg=> ‖HQ j i‖ * (H i*F i)) (s:=univ) (f:=fun j:Φg=> G j*(‖HQ j i‖*F i)) fun j _=> by
    by_cases h:HQ j i=0; simp [h]; rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (T j i h) (v _)) (norm_nonneg _)
 refine hp.trans ?_; rw [←sum_mul]; exact mul_le_of_le_one_left (mul_nonneg (Z _) (v _)) (fee_column_two s g _)

variable {F:InkD n}(p:Scree.Hub n)(c':ℝ)(V:Pane n)
lemma consumeTwo (hg:s∈twoPlanes n)(t:PressB P (moveHub s p) F h c')(x:0≤h): PressB P p (step_F s F) h (duty_Q P.order P.power*c'):=by
 let Y:= moveHub s p; let o:=Y.val.1; let e:=Y.val.2; have hp:boxA s o=p.val.1:=(boxA s).apply_symm_apply _; have hz: actY s⁻¹ Y.val.2=p.val.2:=by unfold Y; ext; simp [actY,moveHub, sitU]
 refine ⟨fun i j v=>?_ ,fun V=>hz ▸ rich_F s⁻¹ Y.val.2 _ (t.fitted (flashA s V)),((suit_Y s⁻¹).toLinearMap.continuous_of_finiteDimensional).measurable.comp (t.measureV.comp (revM s).measurable),fun V g=>?_ ,?_⟩
 · refine congrArg (suit_Y s⁻¹) (t.term _ _ ?_) -- tune
   apply flashD; rw [show (moveHub s p).val.2.map (boxA s).toEmbedding=p.val.2 from by ext; simp [moveHub]]; exact v
 · simp only [step_F,Function.comp_apply]; rw [revG,t.gaugeV]; exact gauge_E s g _
 obtain ⟨A,v,f,g⟩:=t.worth; let r:= P.order; let K(i):= composeCost P.order (A i) ((2:ℝ)^P.power); have hb(i):K i=duty_Q P.order P.power*A i:=by unfold K duty_Q composeCost; ring
 have hu:0 ≤ duty_Q P.order P.power:=by unfold duty_Q composeCost; positivity
 have hv:0 ≤ K:=fun i=>(hb i).symm ▸ (mul_nonneg hu (v i))
 refine ⟨bankY s⁻¹ K,bank_p s⁻¹ K hv,?_,?_⟩; swap
 · have ht:= taxiTwo s⁻¹ ((twoPlanes n).inv_mem hg) K hv (Scree.tariff P p.val.1 h) (Scree.tariff P o h) (fun i j hx=>by rw [←hp]; exact (show (boxA s⁻¹).symm=boxA s from by rw [sitU]; rfl) ▸ (tune_L s⁻¹ i j o P hx h x)) (fun i=>by unfold Scree.tariff; exact mul_nonneg (pow_nonneg (by positivity) _) (pow_nonneg x _)) -- tune dependent notation
   refine ht.trans ?_; unfold joinV; simp_rw [hb, mul_left_comm _ (duty_Q _ _),←mul_sum]; exact mul_le_mul_of_nonneg_left g hu -- simp bomb
 intro V p' i; let Z:= door_b s V; let W:= flashA s V; let C:= s⁻¹; let R:= fun j:Φg=> fun x:tangD n=> crumb (F (increment W (Z x))).val j
 have hf := f W ((glowA ..).mpr p'); have h' (j:Φg): Signs P p.val.1 (R j) (K j):= hp ▸ port_l P s V (hf j)
 let T' (j:DN):= step_F s F (increment V j)
 change Signs P p.val.1 (fun j=>crumb (T' j).val i) (bankY _ _ _); have hx(x:DN): crumb (T' x).val i=∑ j:Φg,(hail_Q C).val i j * Spire.payZ C (R j x):=by
    unfold T' step_F; simp only [Function.comp_apply,tour_p]; rw [roseQ]
 unfold bankY; simp_rw [hx]; exact haloI (fun j (_:j∈(univ:Finset Φg))=> star_P P _ (h' j) (wageZ C))

section
variable {F:Copy n} (X D:Support (More n))
lemma medalTwo (s:Sweep n)(hg:s∈twoPlanes n)(p:Vow.Medal P (actY s X) (actY s D) F h a)(hv:0 ≤ h): Vow.Medal P X D (turn_V s F) h (strive_E P.order*a):=by
 let K:=suit_Y s⁻¹; refine ⟨⟨fun i j h c=> ?_ , fun i=> tape_C s X ▸ rich_F s⁻¹ _ _ (p.lit (yellA s i)), (K.toLinearMap.continuous_of_finiteDimensional).measurable.comp (p.keeps.comp (((revM s).measurable.comp measurable_fst).prodMk ((tuft s).measurable.comp measurable_snd))),fun (V:Orbit n) g=>?_⟩, ?_⟩
 · obtain ⟨x,t⟩:= yellow s i j X h c; exact congrArg K (p.same _ _ x t)
 · let f:= (polarT s.charge ∘g) ∘ (castX s).anon n; have hV: yellA s (Lattice.gauge g V.1, threadG g V.2)=(Lattice.gauge f (flashA s V.1),threadG f (bun s V.2)):=by
      refine Prod.ext (revG ..) (funext fun i=> ?_); change bun s (threadG g V.2) i= threadG f (bun s V.2) i; simp only [bun,man,threadG, map_mul,map_inv]; rfl
   simp only [turn_V,Function.comp_apply,hV]; rw [show F _= _ from p.gaugeX (yellA s V) f]; exact gauge_E s g _ -- tune
 obtain ⟨C,v,j,w⟩:=p.pays; let o:= P.order; let B(z):= (o+1:ℝ)*composeCost o (o.factorial*C z) 1; have hb(k):B k=strive_E o*C k:=by unfold B strive_E composeCost; ring
 have he:0 ≤ strive_E o:=by unfold strive_E composeCost; positivity
 have hB:0 ≤ B:=fun i=>(hb i).symm ▸ (mul_nonneg he (v i))
 refine ⟨bankY s⁻¹ B,bank_p s⁻¹ B hB, ?_, ?_⟩; swap
 · have ht:= taxiTwo s⁻¹ ((twoPlanes n).inv_mem hg) B hB (Wray.stake h) (Wray.stake h) (fun i j hx=>by unfold Wray.stake; rw [inkE s⁻¹ i j hx]) (fun i=>pow_nonneg hv _); refine ht.trans ?_; unfold joinV; simp_rw [hb,mul_left_comm _ (strive_E _),←mul_sum]; exact mul_le_mul_of_nonneg_left w he -- namespace stake
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
lemma earthTwo (z:s∈twoPlanes n)(p:IncX (fun _ :Sweep n=>False) E P h a)(v:0≤h): IncX (fun _=>False) (base_Q s E) P h (duty_Q P.order P.power*a):=by
 obtain ⟨F,p,j⟩:=p.weight; let H:= duty_Q P.order P.power
 refine ⟨⟨fun i=> H*F (moveHub s i),fun i=>?_ ,fun i=>?_⟩,fun _ t=>t.elim⟩
 · exact consumeTwo P s _ _ z (p _) v -- supply args
 apply le_trans _ (mul_le_mul_of_nonneg_left (j ((boxA s).symm i)) (by unfold duty_Q composeCost; positivity)); rw [mul_sum]; conv_rhs=>rw [←Equiv.sum_comp (scope_q s)] -- direction occurrence
 apply le_of_eq; apply sum_congr rfl; intro j _; change ite _ _ _=_; split_ifs with v p h
 · have hp:= mold_q P s j; unfold BudgetPoint.mass; rw [show coverNumber _ (scope_q s j).val.2= _ from glow_q s P.B j.val.2]; change (Trees.currency P.B P.supportExponent j.val.2)*(H*F _)=H*(Trees.currency _ _ _* F (moveHub s j)); ring
 · exact False.elim (p (congrArg (boxA s).symm v))
 · exact False.elim (v ((boxA s).symm.injective h))
 rw [mul_zero]
end YM.CF.QuadClock

-- Adapted: SatinThinTooth
namespace YM.CF.QuadClock
open Ione Moto
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
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Next.Foundations StressFlux AnalyticBridge.VerifiedReset Push.Local
open Taxi
open Vow
local notation "G₅"=> SU.group

local notation "re" s:max=> PlaqAxes.transform s
private lemma tooth_step_two (s:Sweep n) (g:s∈twoPlanes n) (v:s.charge=false)(F:Scree.Hub n)(f:InkD n)(p:PressB P (moveHub s F) f h c)(hx:0≤h)(Z:4 ≤ (More n).val)(he:Nonwrapping (moveHub s F).val.2 (moveHub s F).val.1):
 tooth F.val.1 P (step_F s f) = costSkate s (tooth (moveHub s F).val.1 P f) :=by
 funext i j; obtain ⟨k,rfl⟩:=(re s.s).surjective i; obtain ⟨l,rfl⟩:=(re s.s).surjective j
 rw [cost_price]; let X:= moveHub s F; let G:= step_F s f; let i:=(re s.s) k; let j:=(re s.s) l; let t:=Thera.yet_one
 have hd(L:ℂ→L[ℝ]ℝ) : L (tooth F.val.1 P G i j)=(spinScar s.s k*spinScar s.s l)*L (phaseB s (tooth X.val.1 P f k l)):=by
    let A:=(assembly n).embed s.b; let M:= L.comp (phaseB s); let Vx:=M ∘ lifeH f; let W:=L ∘ lifeH G
    have heW: W= Vx ∘ pull s.s A:=by unfold W; rw [show G=step_F s f from rfl,life_step s f]; refine funext fun y=>?_ ; simp only [Function.comp_apply,revoke,v]; rfl
    rw [cym P G F (consumeTwo P s _ _ g p hx) hx L i j]; change _= _*M (tooth _ P f k l); rw [cym P f X p hx]
    have hu (a b:Flux SU.group): AnalyticBridge.VerifiedReset.quad (AnalyticBridge.VerifiedReset.coeff W F.val.1) a b=AnalyticBridge.VerifiedReset.quad (AnalyticBridge.VerifiedReset.coeff Vx X.val.1) (reframe a s.s) (reframe b s.s):=by
       let D:=(pintK P); have hc:= (show D.Regular X.val.2 Vx from (cashR _ X p hx M _ le_rfl).regular); have hy:= flux_hessian_pull s.s A X.val.1 t hc he Z a b
       rw [←heW,← (chart_p s F).1] at hy; rw [flux_formula _ t (show D.Regular F.val.2 W from (cashR _ F (consumeTwo P s _ _ g p hx) hx L _ le_rfl).regular),flux_formula _ t hc] at hy; exact hy
    have hy:= hu ((1:ℝ) • Averaging.ray i) ((1:ℝ) • Averaging.ray j); rw [rampPrice _ t,one_smul,one_smul,rampFlux k s.s,rampFlux l s.s,rampPrice _ t,one_mul,mul_one] at hy; change AnalyticBridge.VerifiedReset.coeff W F.val.1 i j*_=_; rw [hy]; ring
 refine Complex.ext ?_ ?_
 · change _=Complex.reCLM ((spinScar s.s k*spinScar s.s l) • _); rw [map_smul]; exact hd Complex.reCLM
 change _=Complex.imCLM ((spinScar s.s k*spinScar s.s l) • _); rw [map_smul]; exact hd Complex.imCLM

open Beau
lemma toothTwo (s:Sweep n)(g:s∈twoPlanes n)(F:Scree.Hub n)(f:InkD n)(p:PressB P (moveHub s F) f h c)(hx:0≤h)(Z:4 ≤ (More n).val)(he:Nonwrapping (moveHub s F).val.2 (moveHub s F).val.1):
 tooth F.val.1 P (step_F s f) = costSkate s (tooth (moveHub s F).val.1 P f) :=by
 let u:=τR s; let v:=τV s; have hg:u*v=s:=sash s; let X:=moveHub u F; have hp : X=moveHub s F:=((cupE s (moveHub u F)).symm.trans (step_k ..)).trans (congrArg (moveHub · F) hg)
 have hs: step_F s f=step_F u (step_F v f):=by funext i; simp only [step_F,Function.comp_apply,lights,hg,moon_Y]; rw [←mul_inv_rev,hg]
 let A:=consume_Q P v X c (cycleQ _|>.mpr quad_id) ((cupE s X).symm ▸ (show PressB P X f h c from (hp.symm ▸ p))) hx -- need rewrite cupE
 rw [hs,tooth_step_two u (show u∈twoPlanes n from g) rfl F _ A hx Z (hp.symm ▸ he)]
 funext i j; obtain ⟨i,rfl⟩:= (re u.s).surjective i; obtain ⟨j,rfl⟩:= (re u.s).surjective j
 rw [cost_price]; have hq:=p; rw [← hp] at hq; rw [tooth_echo s X f hq hx]; change _= costSkate s _ ((re s.s) _) ((re s.s) _); rw [cost_price]; apply congrArg (fun z:ℂ=> (spinScar s.s i*spinScar s.s j) • z); rw [show (phaseB v)=(cast_B (wageZ v⁻¹)) from rfl,castT,castT,castT]; change payZ u⁻¹ (payZ v⁻¹ (tooth X.val.1 P f i j)) = payZ s⁻¹ (tooth _ _ _ i j); rw [hp,←hg,mul_inv_rev,←warX]; -- oops payZ order, hp unfolded s in RHS, correct after commute
 unfold Spire.payZ; rw [sign_seq,sign_seq,Bool.xor_comm (wageZ u⁻¹)]
end YM.CF.QuadClock

-- Adapted: SatinThinShelter
namespace YM.CF.QuadClock
open Neon
open Py
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
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
variable {N n B: Side} {P:BudgetPoint}{h Q A B₀ C:ℝ}{L:ℕ}
local notation "mQ"=> mid N B
variable (s:Sweep (mid N B))(r:s∈twoPlanes (mid N B))(x y: Site (mid N B))(g:Earlier s x y)(hp:0≤h)
variable (v:HavenL (mid N B) P L)
open scoped YM.CF.Mew
include g r hp v
lemma wheelTwo {u:RegBudget (mid N B)}{X:ArcΦ}(p:Axon L y P u h Q X): Axon L x P (base_Q s u) h (duty_Q P.order P.power*Q) (turnD s X):=by
 have ht(i:Scree.Hub (mid N B))(t:i.val.1≠node x):base_Q s u i=0:=by unfold base_Q; rw [p.site _ (mt (root_is g i).mp t)]; exact funext (fun i=>map_zero _)
 refine ⟨earthTwo P s r p.vest hp,ht,fun i t=>?_⟩
 by_cases he:i.val.1=node x; swap; · rw [ht i he,if_neg (fun (p:i= Φrap (mid N B) x 10)=>he (p ▸ rfl)),Pill_0]; exact ⟨rfl,rfl⟩
 obtain ⟨a,W⟩:=p.flair _ ((chose_pull i).mpr t : chose L P (moveHub s i)); have hw:(moveHub s i).val.1=node y:= (root_is g i).2 he; let F:= u (moveHub s i)
 obtain ⟨w,q,z⟩:= p.vest.weight; have u':= v.rooms (moveHub s i) ((chose_pull i).mpr t); unfold base_Q; rw [life_step]; simp only [Function.comp_apply,Facet.glacial,a,map_zero,true_and]
 simp only [←move_bill g 10,show moveHub s i=moveHub s (Φrap (mid N B) x 10) ↔ i=Φrap (mid N B) x 10 from (scope_q s).injective.eq_iff] at W; -- tune
 rw [show pillar x (step_F s F) P=turnD s (pillar y F P) from Prod.ext (by change tooth (node x) _ _=costSkate _ (tooth (node y) _ _); rw [←he,←hw]; exact toothTwo s r i _ (q _) hp v.period u') (cost_Dome s i _ _ g he F (q _) u')]; rw [show F= u (moveHub s i) from rfl,W]; split; rfl; exact turn_Zero _

lemma restoreTwo {u:RegBudget (mid N B)}{V:Cusp (mid N B)}{z:ℂ}{F:Copy (mid N B)}{X:ArcΦ}(p:Ice L y P h A B₀ C F u V z X) : Ice L x P h (duty_Q P.order P.power*A) (strive_E P.order*B₀) C (turn_V s F) (base_Q s u) (force_V s V) (phaseB s z) (turnD s X):=by
 refine ⟨wheelTwo s r x y g hp v p.axle,le_trans ?_ p.phase,fun i h=>?_ ,?_,fun i w=>?_⟩
 · rw [phaseB,castT]; unfold cSignX; split; rw [norm_star]; rfl -- le_rfl syntax? `rw` closes.
 · unfold force_V; refine funext fun D=>funext fun v=>?_ ; unfold turn_V; simp only [Function.comp_apply]; rw [p.stout _ (mt (root_in g _).mpr h)]; exact map_zero _
 · obtain ⟨Z,qk,u,t⟩:=p.grant; let a:=strive_E P.order; have ha:0 ≤ a:=by unfold a strive_E composeCost; positivity
   refine ⟨a • zeal_F s Z,⟨fun i=>mul_nonneg ha (qk.1 _),fun i D p t=>?_⟩,fun i=>?_ ,fun i t'=>?_⟩
   · let X:=moldA s i; exact medalTwo P i.val D s r (qk.2 X (actY s D) (map_nonempty.mpr p) (Finset.map_subset_map.mpr t)) hp
   · rw [tall_s]; let A:=(boxA s).symm i; have he i:=call_Q (k:=P.B) (a:=P.supportExponent+1+1) s Z i; specialize he A; rw [show boxA s A=i from (boxA s).apply_symm_apply i] at he; rw [he]; exact mul_le_mul_of_nonneg_left (u _) ha
   · have ht:= t (moldA s i) (right_ne_zero_of_mul (show a*Z (moldA s i)≠0 from t')); exact ⟨glow_q s P.B i.val ▸ ht.1,(root_in g _).mpr ht.2⟩
 · unfold turn_V; simp only [Function.comp_apply]; rw [p.wear (yellA s i) (skew_V s i.1 _ w),map_add,map_add]; -- tune
   let u':=suit_Y s; have hl(x:Cipher mQ): suit_Y s⁻¹ (u' x)=x:=by unfold u'; rw [moon_Y,mul_inv_cancel,toon_Q]
   rw [ show exponentL _ _ (yellA s i).1= u' (exponentL P (base_Q s u) i.1) from (force_r P s u i).symm,← bean_H P s V i]; -- direction
   change _= _; rw [hl,hl]; suffices he:suit_Y s⁻¹ (z • 1)=(phaseB s z) • 1 by rw [he]
   rw [phaseB,castT,suit_scar,map_one]
end YM.CF.QuadClock
