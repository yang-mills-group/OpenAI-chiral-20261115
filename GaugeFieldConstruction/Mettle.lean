import GaugeFieldConstruction.Baffle
import YM.CF.Roots.Seat
import SatinThinPiers
import YM.CF.Mica.Sleet
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 30000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
local notation "GS"=> SU.group
variable {n:Side}{p: BudgetPoint}{Q: InkD n}{o:Skye.Seat n}{X:Scree.Hub n}{h c:ℝ}
namespace Lenten
open Bank Laurent Bloch Tap Hove Spire
open Haro Hove Moto Tap
namespace Layout
open scoped YM.CF.Mew
open HushP ModuleB Pastry Flot
namespace Fren
open Skye Levier Scroll Spire Ione
open Lattice
open ProjectorNext.Equivariance (bonds pull_increment roll pulledDirection)
-- Point root always moves by pull. x at old.
variable (s:Sweep n)(R:Signed)
open Rush
-- anchor costs on this chart.
open QuadClock Vault
variable {T:InkD n}{b:ℝ}
local notation "ΓH" s X=> moveHub s X
structure Turns (Q T: InkD n) : Prop where
 turns (A:Pane n) : T (flashA s A)= suit_Y s (Q A)
lemma HoldS (U: Cipher n): Pastry.pane (suit_Y s U) =cast_B (wageZ s) (Pastry.pane U):= Beau.pot_Z ..
lemma dusk_C (A:Pane n)(v:PressB p X Q h c)(u:Nonwrapping X.val.2 X.val.1) : LitF (orbitPH (Q A)) X.val.1:=by
 intro x y t; have hx:∃ i j:Hove.Kt, matPH (orbitPH (Q A)) x y i j ≠0:=Classical.byContradiction (fun l=> t (by push Not at l; exact funext₂ fun i j=>l i j))
 obtain ⟨i,j,g⟩:=hx; let S:=camp X.val.2; let b:=hailV x i; let a:=hailV y j; let Z:=Haro.tray b a; have he: Z ⊆ S:=by
    apply Finset.mem_powerset.mp; apply And.left (Finset.mem_filter.mp (?_:Z ∈ Pastry.Wheat S)); by_contra t; have ht : Pastry.crumb (Q A).val Z=0:= (v.fitted A).door t; apply g; change Prism.portB (Q A).val (true,b) (false,a)=0; rw [Prism.port_eq]; split; rfl; change _*Pastry.crumb (Q A).val Z=0; rw [ht,mul_zero]
 exact ⟨u _ (mem_filter.mp (he (show (true,b)∈Z by simp [Z,Haro.tray]))).2,u _ (mem_filter.mp (he (show (false,a)∈Z by simp [Z,Haro.tray]))).2⟩
lemma ploy_respect (U U':tangD n)(T T':tangD n)(v:PressB p X Q h c)(hp:0≤h)(e: Agrees X.val.2 U U')(x:Agrees X.val.2 T T'): ploy Q U T=ploy Q U' T':=by
 have he(L:ℂ→L[ℝ]ℝ): L (ploy Q U T)= L (ploy Q U' T'):=by rw [ploy_value v hp,ploy_value v hp]; exact hessian_agrees Thera.yet_one (cashR _ _ v hp L _ le_rfl).regular e x
 exact Complex.ext (he Complex.reCLM) (he Complex.imCLM)
lemma lift_pane (X:Support (More n))(t:ℝ)(u v:tangD n)(e:Agrees X u v): Agrees X (increment 1 (t • u)) (increment 1 (t • v)):=by
 intro i p q; unfold RG.increment; simp only [Pi.smul_apply,e i p q]
lemma branch_m (u:Turns s Q T): orbitPH (T 1)=loom_P s (orbitPH (Q 1)):=by
 have hp : T 1=suit_Y s (Q 1):= by have he:=u.turns (1:Pane n); rw [Facet.glacial] at he; exact he
 rw [hp,suit_Y,paral]
lemma planeDot (v:PressB p X Q h c) (w:PressB p (moveHub s X) T h b)(H:Turns s Q T)(u:0≤h)(i j:tangD n): let L:= door_b s 1; ploy T (L i) (L j)=payZ s (ploy Q i j):=by
 intro L; let Z:= cast_B (wageZ s); let K:= term T; have ht(x:tangD n): K (L x)= Z (term Q x):=by
    change lifeH T (RG.increment 1 (door_b s 1 x))=_; have he:=(tour_p s 1 x).symm; rw [Facet.glacial] at he; rw [he]
    change Pastry.pane (T (flashA s _))= _; rw [H.turns]; apply HoldS
 have hg(f:InkD n)(V:Scree.Hub n)(a:ℝ)(v:PressB p V f h a) : ContDiffAt ℝ ((↑(2:ℕ)): WithTop ℕ∞) (term f) 0:= (eraF _ _ v u 1 (ping_f p _)).paid.of_le (Nat.cast_le.mpr ((by decide:2≤6).trans p.order_ge))
 let V:Fin 2→tangD n:=![i,j]; rw [ploy_iter,ploy_iter, show ![L i, L j] = L ∘ V from (by ext1 i; fin_cases i <;> rfl)]; let Y:= iteratedFDeriv ℝ 2 K 0 (L ∘ V); let F:= K ∘ L;
 have hY: iteratedFDeriv ℝ 2 F 0= ContinuousMultilinearMap.compContinuousLinearMap (iteratedFDeriv ℝ 2 K 0) (fun _=> L):= Next.Foundations.jets_linear L (hg _ _ _ w)
 unfold F at hY; change Y=payZ s (iteratedFDeriv ℝ 2 (term Q) 0 V); rw [show Y= iteratedFDeriv ℝ 2 (K ∘ L) 0 V from congrArg (fun M=> (M: ContinuousMultilinearMap ℝ (fun _: Fin 2=> tangD n) ℂ) V) hY.symm, show K ∘ L= Z ∘ term Q from funext ht, Z.iteratedFDeriv_comp_left (f:=term Q) (hg _ _ _ v) le_rfl]; exact castT .. -- tune
lemma PayCon (R:Signed)(b:Bool)(x:ℂ):cast_B (b.xor (detX R)) x=cSignX (b.xor (detX R)) x:=castT ..
abbrev Dye (R:Signed)(b:Bool)(x:ℂ):= cast_B (b.xor (detX R)) x
-- deterministic moved labels parallel lit checks.
structure Thoughts (R:Signed)(u:Bool)(A B:Waves):Prop where
 life(x y: Gem): (bF4 B).val (gird R x) (gird R y)= Dye R u ((bF4 A).val x y)
 bond(x:Gem)(y:Sut): bF5 B (gird R x) (girdS R y)= Dye R u (bF5 A x y)
 part: chartF B = postF (pre (chartF A) (moveP R u)) (ℳPAL R u)
 limb(x:Gem)(v:SU.group.Color): (bm5 B).val (hem (gird R x) (dyeX u v))=ΔPal R u ((bm5 A).val (hem x v))
variable (M: Male)
set_option maxHeartbeats 70000 in
lemma lives (f:PressB p X Q h c)(g:PressB p (moveHub s X) T h b)(H:Turns s Q T)(u:0≤h) (Y W:Waves)(e:MetaB X.val.1 M Y Q p h) (v:MetaB (moveHub s X).val.1 M W T p h)(r:100<n.val)(t:Nonwrapping X.val.2 X.val.1): Thoughts s.s s.charge Y W:=by
 let R:=s.s; let U:=s.charge; let S:=moveHub s X; let a:= (spike SU.group); let D:=dyeX U; let Z:=D a; let k:=X.val.1; let v':=S.val.1; have hx:‖a‖=1:= spike_norm Thera.yet_one; have ht:‖Z‖=1:= (D.norm_map a).trans hx; have hA(a:SU.group.Color)(s:‖a‖=1): (↑(inner ℝ a a):ℂ)=1:=by rw [real_inner_self_eq_norm_sq,s,one_pow,Complex.ofReal_one]
 let L:=door_b s 1; let K:=p.threshold
 have hz:10≤(More n).val:=by change 10≤ n.val*2; omega
 let l₀(x:Gem):= gateC k K (hem x a); let l₁(y:Gem):=gateC v' K (hem (gird R y) Z)
 let bp(y:Sut):= gateT k K (loomH y a); let bP(y:Sut):=gateT v' K (loomH (girdS R y) Z)
 constructor
 · intro x y; have hp:ploy T (L (l₀ x)) (L (l₀ y))= ploy T (l₁ x) (l₁ y):= ploy_respect _ _ _ _ g u (sunCap s x a t hz K) (sunCap s y a t hz K);
   have hb: ploy T (l₁ x) (l₁ y)= (bF4 W).val (gird R x) (gird R y):=(formC_Ps (o:=v') g u (gird R x) (gird R y) Z Z).trans (by rw [hA Z ht,mul_one]; exact (congrArg (fun X' : leadF Gem Gem=> X' _ _) v.post).symm) -- name v.post
   refine hb.symm.trans (hp.symm.trans ((planeDot s f g H u (l₀ x) (l₀ y)).trans ?_)); rw [e.post]; exact (castT ..).symm -- tune
 · intro x y; have hp:ploy T (L (l₀ x)) (L (bp y))=ploy T (l₁ x) (bP y):= ploy_respect _ _ _ _ g u (sunCap s x a t hz K) (moonCap s y a t hz K)
   have hb:ploy T (l₁ x) (bP y)= bF5 W (gird R x) (girdS R y):= (formT_Ps (o:=v') g u (gird R x) (girdS R y) Z Z).trans (by rw [hA Z ht,mul_one]; exact (congrArg (fun X':Gκ=>X' _ _) v.mast).symm)
   refine hb.symm.trans (hp.symm.trans ((planeDot s f g H u (l₀ x) (bp y)).trans ?_)); rw [e.mast]; exact (castT ..).symm
 · rw [e.port,v.port, branch_m s H]; exact moveJ0 s M (dusk_C 1 f t) r
 intro x z; let X':=hem x z; let P:=gateC k K X'; let W':=hem (gird R x) (D z); let P':=gateC v' K W';
 let Y₀(y:ℝ):=orbitPH (Q (increment 1 (y • P))); let Y₁(y:ℝ):=orbitPH (T (increment 1 (y • P'))); let S₀(y):= sectorJ (Y₀ y) M k h; let S₁(y):= sectorJ (Y₁ y) M v' h; let T':= ℳPAL s.s s.charge; have hp: S₁= T' ∘ S₀:=by
    funext y; have he: Y₁ y= loom_P s (Y₀ y):=by
       unfold Y₁; rw [show T (increment 1 (y • P'))= T (increment 1 (y • L P)) from Eq.symm (g.term _ _ (lift_pane S.val.2 y (L P) P' (sunCap s x z t hz K))), ← map_smul];
       change orbitPH (T (increment 1 (door_b s 1 _)))= _; have hx:=tour_p s 1 (y • P); rw [Facet.glacial] at hx; rw [←hx,H.turns,suit_Y, paral]
    unfold S₁; rw [he]; exact congrArg Prod.fst (moveJ0 s M (o:=k) (h:=h) (f:=Y₀ y) (dusk_C _ f t) r) -- tune
 rw [v.mixed,e.mixed]; apply (landR M (o:=v') g W').unique; apply HasDerivAt.congr_of_eventuallyEq (T'.hasFDerivAt.comp_hasDerivAt 0 (landR M (o:=k) f X')); exact EventuallyEq.of_eq hp -- tune
-- thoughts uniqueness absolute.
lemma ThoughtU (f:Bool)(X Y Z:Waves)(u:Thoughts R f X Y)(h:Thoughts R f X Z):Y=Z:=by
 have hv:chartF Y=chartF Z:= u.part.trans h.part.symm; have he(a:Gem):gird R (gird R⁻¹ a)=a:= by simpa only [inv_inv] using gird_flip R⁻¹ a
 have ht(a:Sut):girdS R (girdS R⁻¹ a)=a:=by simpa only [inv_inv] using girdS_rev R⁻¹ a
 have hp:bF4 Y=bF4 Z:=by apply Subtype.ext; apply ContinuousLinearMap.ext; intro i; apply ContinuousLinearMap.ext; intro j; have hp:= (u.life (gird R⁻¹ i) (gird R⁻¹ j)).trans (h.life _ _).symm; rw [he,he] at hp; exact hp -- repeat i=j variable not same
 have hg:bF5 Y=bF5 Z:=by apply ContinuousLinearMap.ext; intro i; apply ContinuousLinearMap.ext; intro j; have hp:=(u.bond (gird R⁻¹ i) (girdS R⁻¹ j)).trans (h.bond _ _).symm; rw [he,ht] at hp; exact hp
 have hs:bm5 Y=bm5 Z:=by
    have hm(i:Gem)(j:SU.group.Color): (bm5 Y).val (hem i j)= (bm5 Z).val (hem i j):=by
       have hx:=(u.limb (gird R⁻¹ i) (dyeX f j)).trans (h.limb _ _).symm; rw [he, dyeF ..] at hx; exact hx
    apply Subtype.ext; apply ContinuousLinearMap.ext; intro k
    rw [trade_Z k, map_sum,map_sum]; exact sum_congr rfl fun k p=> hm _ _
 exact Prod.ext (Subtype.ext (congrArg Prod.fst hv)) (Prod.ext (Prod.ext hp (Subtype.ext (congrArg (fun i:PalOne=>i.2.1) hv))) (Prod.ext hg (Prod.ext (Subtype.ext (congrArg (fun i:PalOne=>i.2.2.val) hv)) hs)))
end Fren
end Layout
end Lenten
end YM.CF.TableF
end
