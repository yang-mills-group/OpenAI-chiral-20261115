import GaugeFieldConstruction.Webb
import YM.CF.Bloom.Screen
import YM.CF.Vp929.Pre.Stock
import YM.CF.Chaff.Echo

-- Third purchase. Does NOT change the Muster constants. Refine plan_B
set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
-- certify.WAGES off all granted tasks
variable {u Hh pK qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
open Hope
namespace Riant
open Rate Rate.Pitching.Focus.Stockpile
variable {N:Side}
abbrev Tollup (U:ℝ)(p:BudgetPoint)(i:Scree.Hub N):ℝ:= Real.exp (U*coverNumber p.B i.val.2)
abbrev ΩBook(p:BudgetPoint)(d:ℝ)(C:Scree.Hub N → ℝ):= ∑ i,Tollup d p i*C i
structure ArenaC(p:BudgetPoint)(E:RegBudget N)(o:Seat N)(C:Scree.Hub N→ℝ)(d h B:ℝ):Prop where
 fits (i:Scree.Hub N) : PressB (KeyUp p) i (E i) h (C i)
 bill :ΩBook p d C ≤ B
 paid:∀ i,0≤ C i
 off(i:Scree.Hub N) : o≠i.val.1→ E i=0 ∧ C i=0
lemma ArenaC.earns {p E o C d h B}(v:ArenaC p E o C d h B)(i:Scree.Hub N)(pU: 0 ≤ d): C i≤ B:=by
 apply le_trans (b:=Tollup d p i*C i) (le_mul_of_one_le_left (v.paid i) (by unfold Tollup; exact Real.one_le_exp (by positivity)))
 exact ((single_le_sum (f:=fun i=>Tollup d p i*C i) (fun i _=>mul_nonneg (Real.exp_pos _).le (v.paid i)) (mem_univ _))).trans v.bill -- tune
lemma price3 {U:BudgetPoint}(o:ℕ)(p:U.B≤2*o)(i:Scree.Hub N)(w:ℕ)(k:ℝ)(h:∀ i:ℕ,(1+i:ℝ)^w ≤ k*Real.exp (a*i)) : ((1:ℝ)+Hope.reel U.B i.val.2)^w ≤ (10*(1+(o:ℝ)))^w*(k*Tollup a U i):=by
 let t:ℝ:=coverNumber U.B i.val.2; let K:ℝ:=10*(1+(o:ℝ)); have hx: (1:ℝ)+Hope.reel U.B i.val.2 ≤ K*(1+t):=by
    have he:(U.B:ℝ)≤ (2:ℝ)*o:=by exact_mod_cast p
    let A:ℝ:=U.B; let B:ℝ:=o; have hB:0 ≤ B:=Nat.cast_nonneg _; have ht:0 ≤ t:= Nat.cast_nonneg _; unfold Hope.reel; push_cast; change 1+(t*(4*A+2)+2*A)≤ 10*(1+B)*(1+t); change A≤2*B at he; nlinarith only [ht,hB,he,mul_le_mul_of_nonneg_left he ht]
 refine (pow_le_pow_left₀ (by positivity) hx w).trans ?_; rw [mul_pow]; unfold K; exact mul_le_mul_of_nonneg_left (h _) (pow_nonneg (by positivity) _)
lemma ΙShift(R:Patch): ∃ f:ℝ→ℝ, sizeK R.L 2 f ∧∀ᶠ x:ℝ in atTop,0≤ f x ∧∀ {N:Side}(p:BudgetPoint)(h:ℝ),0≤ h → p.power=2→ p.order=6→ p.supportExponent=1→ p.B≤2*radiusB x→∀ (F:RegBudget N), IncX primeU F p h (3*dleaf R.L x) →∀ i,PressB (KeyUp p) i (F i) h (f x):= by
 obtain ⟨c,h,H⟩:= Chaff.polyF 7 (show 0<(1:ℝ) by norm_num); let k(x:ℝ):ℝ:= 10*(1+(radiusB x:ℝ)); let f(x):= c*(k x)^7*(3*dleaf R.L x);
 have hh:sizeK R.L 0 k:= ((sizeK.mild _ _).accrue (sizeK.Bcash _)).scale 10
 refine ⟨f,(((hh.powC 7).scale c).tint ((dev_R R).1.scale 3)),?_⟩
 filter_upwards [(dev_R R).1.low (show 1≤2 by decide) |>.spine |>.eventually (ge_mem_nhds zero_lt_one), eventually_gt_atTop (0:ℝ),(Scales.year SU.group R.L).eventually_gt_atTop 0] with x _ v t
 have hx:0≤ dleaf R.L x :=mul_nonneg (Scales.gauge SU.group R.L t).le (Work.E09.temp_pos v).le; refine ⟨by unfold f k; positivity,fun {N} p w d t m e v Y q i =>?_⟩ -- includes extras natural
 obtain ⟨b,g,s⟩:=q.weight; apply hi_p (longer3 t (g i) d p.B)
 have hk(b':Scree.Hub N):0 ≤ b b':= (Taxi.eraF _ _ (g b') d _ (ping_f p _)).grade
 have ht: Tollup 1 p i*b i ≤ 3*dleaf R.L x:=by
    change _≤_; rw [show Tollup 1 p i*b i=p.mass i.val.2 (b i) from (by unfold Tollup BudgetPoint.mass; rw [e])]
    apply le_trans _ (s i.val.1); exact le_trans (Eq.le (show _= if i.val.1=i.val.1 then _ else 0 from (if_pos rfl).symm)) (single_le_sum (f:=fun j:Scree.Hub N=>if i.val.1=j.val.1 then p.mass j.val.2 (b j) else 0) (fun j _=> by split; exact mul_nonneg (Real.exp_pos _).le (hk _); exact le_rfl) (mem_univ _)) -- tune type HR
 rw [m]; exact le_trans (mul_le_mul_of_nonneg_right (price3 (radiusB x) v _ 7 _ H) (hk _)) (by change k x^7* (c* _)*_ ≤ _; unfold f; have he:0 ≤ k x:=by unfold k; positivity
                                                                                               linarith only [mul_le_mul_of_nonneg_left ht (show 0 ≤ c*k x^7 from mul_nonneg h (pow_nonneg he _))]) -- linarith nonlinear normalization atom
abbrev coin₂ (R:Patch)(x:ℝ):ℝ:=Scales.g SU.group R.L x^2
lemma coin_B {R:Patch} : Litt R 2 (coin₂ R):=Litt.gearX (BoreP.still 1) (Eventually.of_forall (fun i=> Eq.symm (one_mul ..)))
def poseX (p:BudgetPoint)(o:Seat N)(F G:RegBudget N): RegBudget N:= fun i=> if o=i.val.1 then Hope.ζMark (F i) (G i) (KeyUp p) i else 0
structure Icary(R:Patch)(x cost c η:ℝ):Prop where
 nn : 0≤ η
 bound:c*(cost*coin₂ R x) ≤ εLeaf R.L x
 marks {n:Side}(p:BudgetPoint)(E G:RegBudget n)(o:Seat n)(C:Scree.Hub n→ℝ)(h b:ℝ) : 1≤h → p.power=2→ p.order=6→ p.supportExponent=1→ p.B≤2*radiusB x→ ArenaC p E o C (5/4) h b → IncX primeU G p h (3*dleaf R.L x) → b≤cost*coin₂ R x → let F:=poseX p o G E; (∀ i, PressB (KeyUp p) i (F i) h (c*C i) ∧ PressB (KeyUp p) i (F i-E i) h (η*C i) ∧ ∀ U,pingS p.threshold i.val.2 U→ exp (F i U)-1= E i U*exp (G i U)) ∧ IncX primeU F p h (εLeaf R.L x) ∧ IncX primeU F (KeyUp p) h (εLeaf R.L x)
lemma issuer :∃ c:ℝ,1≤ c ∧∀ (R:Patch)(t:ℝ),0≤ t →∃ f:ℝ→ℝ,sizeK R.L 2 f ∧∀ᶠ x:ℝ in atTop,Icary R x t c (f x):=by
 let n:ℝ:=(6:ℕ).factorial; let c:=2*n*(7*2); let D₀:=n*7*(7*(n*Real.exp 1*7)); let H:= 2*n*(7*2)^2; have hn:1≤n:=by unfold n; exact_mod_cast Nat.factorial_pos 6
 have hw:1≤c:=by unfold c; linarith
 refine ⟨c,hw,fun R K hK=> ?_⟩; obtain ⟨v,hv,ht⟩:=ΙShift R; let Z(x):=D₀*v x; let t(x):=K*coin₂ R x; let u(x:ℝ):ℝ:= H*t x; have hZ:=hv.scale D₀; have ht':Litt R 2 t:= Litt.scale_l coin_B _; have hu:=ht'.height_r;
 refine ⟨fun x=>u x+ Z x,(hu.scale H).accrue hZ,?_⟩
 filter_upwards [ht, tenor_Q 16 _ (ht'.scale_l c) (by positivity), ((hu.scale (7*2)).low (by decide:1≤2)).spine.eventually (ge_mem_nhds (show (0:ℝ)<1/4 by norm_num)), ((hv.scale 7).low (by decide:1≤2)).spine.eventually (ge_mem_nhds zero_lt_one), (hZ.low (by decide:1≤2)).spine.eventually (ge_mem_nhds zero_lt_one)] with x ht hw' hy hp hm
 have hg:0≤ t x:=mul_nonneg hK (sq_nonneg _)
 refine ⟨(by unfold u H Z D₀; have hl:=ht.1; positivity),hw',fun {N} p E G o C h b g v₁ v₂ v₃ v₄ hE hG hB=>?_⟩
 intro F; have h0:= zero_le_one.trans g; let A(i):= ht.2 p h h0 v₁ v₂ v₃ v₄ G hG i; let p':=KeyUp p; have hω:p'.order=6:=v₂; have hnn:=ht.1
 have hw(i:Scree.Hub N):C i≤ t x:= (hE.earns i (by norm_num)).trans hB
 have h(i:Scree.Hub N):PressB p' i (F i) h (c*C i) ∧ PressB p' i (F i-E i) h ((u x+ Z x)*C i) ∧ ∀ U,pingS p.threshold i.val.2 U→ NormedSpace.exp (F i U)-1= E i U*NormedSpace.exp (G i U):=by
    let d:=C i; have hd:0 ≤ d:=hE.paid i; by_cases e:o=i.val.1
    · rw [show F i=_ from (if_pos e: F i =ζMark (G i) (E i) p' i)]; have hp':n*Real.exp (7*v x)*(7*v x) ≤ n*Real.exp 1*(7*v x):=by gcongr
      have hx: turnsP p' d (Hope.snack p' (v x))≤Z x*d := by
        unfold turnsP Hope.snack; rw [hω]; change n*((↑(6:ℕ)+1)*d*((↑(6:ℕ)+1)*(n*_)))≤ _; rw [show (↑(6:ℕ):ℝ)+1=7 from (by norm_num)]; unfold Z D₀; linarith only [mul_le_mul_of_nonneg_left hp' (show 0 ≤ n*7*7*d from (by positivity))] -- tune
      obtain ⟨W,s,q⟩:=ζlemma (A i) (hE.fits i) g hω (Z x*d) (2*d) hx (by linarith only [mul_le_mul_of_nonneg_right (show Z x ≤1 from hm) hd]) (by linarith only [hy,show d ≤ t x from hw i])
      refine ⟨hi_p W ?_,hi_p s ?_,q⟩; · change skewCost p' (2*d) ≤ c*d; unfold skewCost c; rw [hω]; unfold n; apply le_of_eq; push_cast; ring -- tune
      rw [hω]; unfold u H; change 2*n*(7*(2*d))^2+ _ ≤ _*d; exact (by nlinarith only [mul_le_mul_of_nonneg_left (show d ≤ t x from hw i) (show 0 ≤ n*d from (by positivity))] )
    obtain ⟨y,z⟩:=hE.off i e
    rw [show F i=0 from if_neg e,y,z]; simp only [sub_self,mul_zero]; refine ⟨rinse _ _ _,rinse _ _ _,fun V _=>?_⟩; simp
 let v(i):=c*C i; have hc(Y:Seat N): (∑ i:Scree.Hub N,if Y=i.val.1 then p.mass i.val.2 (v i) else 0) ≤ εLeaf R.L x:=by
    refine le_trans (b:=c*ΩBook p (5/4) C) ?_ ((mul_le_mul_of_nonneg_left (hE.bill.trans hB) (show 0 ≤ c from by unfold c; positivity)).trans hw'); unfold ΩBook; rw [mul_sum]; refine sum_le_sum fun i _ => ?_; have ht:= hE.paid i; have hcp:0 ≤ c:=(by unfold c; positivity); split
    next t=> unfold v; have hh:Real.exp (p.supportExponent*coverNumber p.B i.val.2)≤ Tollup (5/4) p i:=by rw [v₃]; exact Real.exp_monotone (mul_le_mul_of_nonneg_right (by norm_num) (Nat.cast_nonneg _))
             exact (mul_le_mul_of_nonneg_right hh (mul_nonneg hcp ht)).trans_eq (by ring)
    exact mul_nonneg hcp (mul_nonneg (Real.exp_pos _).le ht)
 exact ⟨h,⟨⟨v,fun i=> smallerP v₁ (h i).1 h0,hc⟩,fun _ t=> t.elim⟩,⟨⟨v,fun i=> (h i).1,hc⟩,fun _ t=> t.elim⟩⟩
end Riant
end YM.CF.Py
end
