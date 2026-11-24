import GaugeFieldConstruction.Harpy
/-! Sole cost χ. -/
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
open Lenten
open Stationary Vault Font
open Bank Laurent Bloch Tap Hove Spire
open Haro Peaks Rush Fir Next.Free Thorn
open Planned.PrimaryIntegral295 Carrier
namespace Boom
variable {f c:Side}{G: Ratio c f}{o:Skye.Seat f}{U:Op (Single c)}{T: Script Male}{V: DiamP→ℂ}{M M':Male}{h a d:ℝ}{σ Y B:Bool→ℝ}{m k:ℕ}
private abbrev VasC (Q:DiamP→ Views →L[ℝ] ℝ)(F: DiamP→ℂ)(p:Views):ℂ:= ∑' i,PayS (Q i) p* F i
section
variable (e:Odd G.count.val)(t:FlightFlux.chime ThetaX V a)(p:∀ x y:Single c,U x y=remTag G (AnchorN o) V x y)
include t
lemma Smart(i j:Kt)(o:Skye.Seat f): let V':=RawInfinity G o V h
 ∀ x:Views,V' x i j=VasC (pairF G o) (gated i j h V) x:=fun _=>rfl
omit t
variable (F H:DiamP→ℂ)(hF:Summable fun i:DiamP=> deltaM i^2*‖F i‖)(hH:Summable fun i:DiamP=>deltaM i^2*‖H i‖)
include hF
lemma coexist_P (x: Views)(Q:DiamP→ Views→L[ℝ]ℝ): Summable (fun i:DiamP=>PayS (Q i) x *F i):=Summable.of_norm_bounded hF fun i=> by rw [norm_mul,pay_money,one_mul]; exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (δMP _))
include hH
lemma coincide_P (Q:DiamP→ Views→L[ℝ]ℝ): VasC Q (F+H)=VasC Q F+VasC Q H:=by funext x; unfold VasC; simp only [Pi.add_apply,mul_add]; exact (coexist_P F hF ..).tsum_add (coexist_P H hH ..)
omit hF hH
include e t p
set_option maxHeartbeats 100000 in
lemma MulArc (i j:Kt)(h:ℝ): ∃ Z:Ole Views ℂ, AptK (fun x=> streamF (downT G o) U h x i j-RawInfinity G o V h x i j) Z∧ CostOle Z≤ 2*Pier h c a:= by
 classical
 let F:=gated i j h V; let W:=fun k=> neo G o k*F k
 let Q:= closePay G o; let P:=pairF G o
 have hp(z):‖P z‖ ≤ deltaM z:= (celebrate e z).1; have hQ(z):‖Q z‖≤deltaM z:=(celebrate e z).2
 let A:= {x:DiamP|TimelyPair c x}; let f:=VasC Q W; let g:=VasC P F; have ht : (fun x=> streamF (downT G o) U h x i j - RawInfinity G o V h x i j)= fun x=> f x-g x:=funext fun x=> by rw [Fshore o t.2.1 i j x h U p]; rfl -- tune
 have hy(q:DiamP→ℂ)(H:∀ i,‖q i‖ ≤ h^2*‖V i‖)(B:Set DiamP):∀ i,‖Set.indicator B q i‖ ≤ h^2*‖V i‖:= by
    intro i; by_cases p:i∈B; · rw [Set.indicator_of_mem p]; exact H i
    rw [Set.indicator_of_notMem p,norm_zero]; positivity
 let E:= A.indicator W; let Y:= A.indicator F; let H₀:= (Aᶜ : Set DiamP).indicator W; let H₁:=(Aᶜ:Set DiamP).indicator F
 have h₁(x):‖F x‖≤ h^2*‖V x‖:= γG i j _; have h₂(x):‖W x‖≤ h^2*‖V x‖:=by unfold W; rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) (neo_bound _)).trans (h₁ _)
 have he: SumBudget (fun i=>deltaM i^2*‖H₀ i‖) (Pier h c a):=Γfar h t _ (hy W h₂ _) c (fun i p=>Set.indicator_of_notMem (show i ∉ Aᶜ from Set.notMem_compl_iff.mpr p) _)
 have hz: SumBudget (fun i=>deltaM i^2*‖H₁ i‖) (Pier h c a):=Γfar h t _ (hy F h₁ _) c (fun i p=> Set.indicator_of_notMem (show i∉ Aᶜ from Set.notMem_compl_iff.mpr p) _)
 have hh: f-g=VasC Q H₀-VasC P H₁:=by
    have hF:F=Y+H₁:=by ext i; by_cases h:i∈A <;> simp [h,Y,H₁]
    have hg: W=E+H₀:=by ext i; by_cases h:i∈A <;> simp [h,E,H₀]
    have hp:VasC P Y=VasC Q E:=by
       funext x; refine tsum_congr fun i=>?_ ; by_cases h:i∈A
       · have hl:= Well G e o i (show TimelyPair c i from h).1 (show TimelyPair c i from h).2; change Q i=P i ∧ _ at hl; rw [hl.1,show Y i=F i from Set.indicator_of_mem h F,show E i=W i from Set.indicator_of_mem h W,show W i=F i from (by unfold W; rw [show neo G o i=1 from hl.2,one_mul])]
       rw [show Y i=0 from Set.indicator_of_notMem h _,show E i=0 from Set.indicator_of_notMem h _,mul_zero, mul_zero]
    unfold f g; rw [hg,hF,coincide_P E H₀ (Γjoint t E (hy W h₂ _)).2.1 he.2.1,coincide_P Y H₁ (Γjoint t Y (hy F h₁ _)).2.1 hz.2.1,hp]; abel
 obtain ⟨D,d,H⟩:= boundS _ he.2.1 _ hQ; obtain ⟨B,v,Vb⟩:= boundS _ hz.2.1 _ hp; refine ⟨D-B, ?_,?_⟩; · exact (d.minus v).equal (Filter.EventuallyEq.of_eq (hh.symm.trans ht.symm))
 exact (show CostOle (D-B) ≤ _ from (show ∀ {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F] (D B:Ole E F), CostOle (D-B) ≤ CostOle D+CostOle B from fun {_ _} _ _ _ _ D B=>norm_sub_le D B) D B).trans ((add_le_add (H.trans he.2.2) (Vb.trans hz.2.2)).trans_eq (by ring))
end
private lemma berth_money {I J E L:Type}[Fintype I][Fintype J][NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup L][NormedSpace ℝ L](f:I→ J→ ℂ→L[ℝ]L)(K:I→J→ Ole E ℂ) (C:ℝ)(p:∀ i j,CostOle (K i j)≤C) : CostOle (clanJ K f) ≤ clanK f C:=by
 let Z:= fun i j=> postF (K i j) (f i j); change ‖∑ i:I,∑ j:J,Z i j‖≤ ∑ i:I,∑ j:J, ‖f i j‖*C; apply le_trans (norm_sum_le univ (fun i:I=> ∑ j:J,Z i j)); apply sum_le_sum; intro i _; apply (norm_sum_le univ (fun j:J=>Z i j)).trans; apply sum_le_sum; intro j _; exact (post_pay _ _).trans (mul_le_mul_of_nonneg_left (p i j) (norm_nonneg _))
noncomputable abbrev coinV(C:ℝ):ℝ:= clanK flare_one C
lemma coin_pos (p:0≤d):0 ≤ coinV d:= c_nn _ _ p -- tune
lemma coin_d (p q:ℝ):coinV (p*q)= coinV p * q:=by unfold coinV; apply (show ∀ {I J E:Type}[Fintype I][Fintype J][NormedAddCommGroup E][NormedSpace ℝ E](Q:I→J→ℂ→L[ℝ] E),clanK Q (p*q)=clanK Q p* q from fun {_ _ _} _ _ _ _ f=> by unfold clanK; simp_rw [sum_mul]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; rw [mul_assoc])
lemma coin_init (p:ℝ):coinV p= coinV 1*p:= by nth_rw 1 [←one_mul p]; rw [coin_d]
lemma Flight_Q (v:Odd G.count.val)(t:FlightFlux.chime ThetaX V a)(p:∀ x y:Single c,U x y=remTag G (AnchorN o) V x y) (h:ℝ): ∃ Z:PalOne, AptK (RawInfinity G o V h) Z∧ CostOle (markJet (downT G o) U h-Z)≤ coinV (2*Pier h c a):=by
 choose Z hv hK using MulArc v t p (h:=h) -- binder last explicit h tune
 let f:= RawInfinity G o V h; let g:=streamF (downT G o) U h; let H:= markJet (downT G o) U h; let a':=2*Pier h c a; let W:=clanJ Z flare_one
 have he:AptK (g-f) W:= by
    let F:=g-f; let V(i j:Hove.Kt)(x:Views):= flare_one i j (F x i j); let K:=∑ i:Hove.Kt,∑ j:Hove.Kt,V i j
    have he:AptK K W:= AptK.sumV univ _ _ (fun i _=> AptK.sumV univ (fun j=>V i j) _ (fun j _=> (hv i j).geomF _))
    have ht(i): F i=K i:=by unfold K; simp_rw [Finset.sum_apply]; exact flare_draw _
    exact he.equal (Filter.EventuallyEq.of_eq (funext fun i=>(ht i).symm)) -- Plane input mismatch berth fixed Plane. adapt
 refine ⟨H-W, ((show AptK g H from K_pays ..).minus he).equal (Filter.EventuallyEq.of_eq (by abel)),?_⟩; change CostOle (H-(H-W)) ≤ _; rw [show H-(H-W)=W from sub_sub_self H W]; exact berth_money flare_one _ _ hK
noncomputable def δwinBody (M:Male)(V: PalOne) := palCart (bladeL false) (palCart (wheelP M false) (palCart V (palCart (wheelP M true) (bladeL true))))
def δInfty (F:Views→ Pal)(M:Male)(p: Views): Pal:= (baseF false)*(fellP M false p*(F p*(fellP M true p *baseF true)))
lemma BaseNon (F:Views→ Pal)(V:PalOne)(e:AptK F V):AptK (δInfty F M) (δwinBody M V) :=cart_K (AptK.const _) (cart_K (plankK M false) (cart_K e (cart_K (plankK M true) (AptK.const _))))
abbrev labelB:=coinV 1*2*(1000*(96:ℝ)^2)
abbrev inkPay(c:Side)(h a:ℝ):ℝ:=labelB*h^2*a/c.val
lemma cost_V (M:Male)(V:PalOne){c:ℝ}(p:CostOle V ≤ c): CostOle (δwinBody M V)≤ mintPay c :=by
 let X:=wheelP M false; let Y:=wheelP M true; let v:=V; let z:=palCart Y (bladeL true); let w:=palCart v z; let H:=palCart X w
 have hc:0≤ c:= (Ole_non v).trans p
 have he : CostOle z ≤ 4*BasePrice true*CostOle (bladeL true):=by apply (pal_cost ..).trans; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (wheel_C M true) (by norm_num)) (Ole_non _)
 have hz : CostOle w ≤ 4*c*(4*BasePrice true*CostOle (bladeL true)):=by apply (pal_cost ..).trans; exact mul_le_mul (mul_le_mul_of_nonneg_left p (by positivity)) he (Ole_non z) (by positivity)
 have hx : CostOle H ≤ 4*BasePrice false*(4*c*(4*BasePrice true*CostOle (bladeL true))):=by apply (pal_cost ..).trans; exact mul_le_mul (mul_le_mul_of_nonneg_left (wheel_C M false) (by norm_num)) hz (Ole_non w) (mul_nonneg (by positivity) (BP_u _))
 exact (pal_cost (bladeL false) H).trans (mul_le_mul_of_nonneg_left hx (mul_nonneg (by positivity) (Ole_non _)))
lemma CullY (w:Odd G.count.val)(v:FlightFlux.chime ThetaX V a)(p:∀ x y:Single c,U x y= remTag G (AnchorN o) V x y) (h:ℝ)(M:Male): ∃ B:PalOne,AptK (δInfty (RawInfinity G o V h) M) B ∧ CostOle (winJ (downT G o) M h U-B)≤ mintPay (inkPay c h a):=by
 obtain ⟨Z,g,t⟩:=Flight_Q w v p h; let f:= RawInfinity G o V h; let X:=markJet (downT G o) U h; let V:= winJ (downT G o) M h U
 let A:=streamF (downT G o) U h; let K:=δwinBody M Z; refine ⟨K,BaseNon f _ g,?_⟩
 have hz: V-K= δwinBody M (X-Z):=by
    apply ((show AptK (δInfty A M-δInfty f M) (V-K) from (BaseNon A X (K_pays ..)).minus (BaseNon f Z g)).unique); have hv:δInfty A M-δInfty f M=δInfty (A-f) M:=by funext i; simp only [δInfty,Pi.sub_apply,sub_mul,mul_sub]; -- tune Pal def
    rw [hv]; exact BaseNon _ _ ((K_pays ..).minus g)
 change CostOle (V-K) ≤ _; rw [hz]; let E:=X-Z
 refine cost_V M (X-Z) ((t).trans_eq ?_)
 rw [coin_init]; unfold Pier inkPay labelB; ring
end Boom
end YM.CF.TableF
end
