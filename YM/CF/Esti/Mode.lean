import YM.CF.Esti.Stole
import YM.CF.Vol.Celt
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Baton
import YM.CF.Palot.End
import YM.CF.Appel.Sat
import YM.Next.FLUCTUATIONS.Grants
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Wind
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Esti
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
variable {K': Teller G}{A B:Stores S}{T:Tube G S}{V:Config G c}{U:Config G f}{k:S.Choices}{q:Chi}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E]{x':E}
open AnalyticBridge.Annulus1AD Push.SectorMeasure.Oriented Pressure.Tube
variable {O:Stores S}{F: Forest S.ratio}{Y:LinkArray G (Frozen A x F)}{z:LogArray G (Active A x F)}{β Q γ D L M s:ℝ}{J:ChartRatio G}{P:Patch}
lemma espy_m (P:Patch)(g x:ℝ)(p m:ℕ): espy P g x p ^ m=espy P ((m:ℝ)*g) x p:=by unfold espy; rw [←Real.exp_nat_mul]; congr 1; ring
lemma beamT(P:Patch)(g:ℝ)(n j:ℕ)(p:0<g)(C K M u width:ℝ): ∀ᶠ x in atTop,∀ {c f:Side}(S:StepData c f), S.patch=P →∀ A O:Stores S, ∀ F: Forest S.ratio, 0<O.shares→ |grip n u (width*fiery G x P.L) K C M (locals A O x F ((j+104)*radiusB x)).card| ≤ espy P (3*g) x O.shares:=by
 let T (x:ℝ):= width*fiery G x P.L; let tBill(v:ℝ)(x:ℝ):= still n (v*T x) M C; let Z(x):=zest n*tBill 1 x; have ht(v:ℝ): Lento (tBill v):=by
    let H:= Lento.ledge P.L (v*width); refine Lento.piece (Lento.times (Lento.sco ?_) (Lento.sun ((2:ℝ)^n*C*C))) _ _; apply Lento.mono H; filter_upwards with x; unfold T; rw [←mul_assoc]
 let J:= fun x=>zest n*plume n u (T x) K C M; have hp:Lento J:= (Lento.sun _).times ((((Lento.sun _).times (ht 2)).times (Lento.sun _)).piece _ _)
 filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop 1,cardS P Z j g ((Lento.sun _).times (ht 1)) p, cardS P J j g hp p, cardS P _ j g (Lento.sun (zest n)) p] with x h ht hp hF c f S hS A O F hu
 have hb:=(tune (F:=F) (A:=A) (O:=O) j h).2.2.2; let e:=espy P g x O.shares
 let X:= locals A O x F ((j+104)*radiusB x); have he: |zest n| ≤e:= (pow_one _).symm.le.trans (hF S hS O _ (pin_p hu)); have hz:0<e:=Real.exp_pos _
 have hu': |Z x|^X.card ≤ e:= ht S hS O _ hb
 unfold grip; rw [abs_mul,abs_mul (zest n),abs_pow,abs_pow]; refine le_trans (b:=e*e*e) (mul_le_mul (mul_le_mul he (hp S hS O _ hb) (pow_nonneg (abs_nonneg _) _) hz.le) ?_ (by positivity) (by positivity : 0 ≤ e*e)) ?_
 · simpa only [X,Z,tBill,Esti.still,T,one_mul] using hu' -- f local rename
 change e*e*e≤_; rw [show e*e*e=e^3 from by ring, show e^3= _ from espy_m P g x O.shares 3]; norm_num
lemma cardinalE(P:Patch)(n j:ℕ)(Q M:ℝ)(p:0 ≤ Q)(hp:0 ≤ M)(k:ℝ)(h:0<k):∀ᶠ x in atTop,∀ {c f:Side}(S:StepData c f), S.patch=P →∀ O:Stores S,0 < O.shares → ∀ β ∈Set.Icc (y G P.L x/2) (2*y G P.L x), let r:ℝ:= latticeFieldEstimates O j x; |1+frieze (n:=n) (C:=Q) (D:=M) β r|^n ≤ espy P (k+k) x O.shares:=by
 let V:= carV n M; have hx:0 ≤ V:=by unfold V carV; dsimp only; have :=Rows.slip_pos; positivity
 let a(x:ℝ):= dusk j P*plow x^4; let Φ(x:ℝ):= (1+2*y G P.L x*(a x*(Q+4*V)))^n; have hΦ:Lento Φ:= ((Lento.sun _).plus (((Lento.sun _).times (Lento.yearB P.L)).times (((Lento.sun _).times (plow_l.power 4)).times (Lento.sun _)))).power _
 filter_upwards [cardS P Φ j k hΦ h,(year G P.L).eventually (eventually_gt_atTop 0), (Scales.peak G P.L).eventually (eventually_ge_atTop (1+(n:ℝ)/k))] with x hx' hv hh c f S hS O hp' β hb r
 let C:= O.shares; have he:1 ≤ (C:ℝ):=Nat.one_le_cast.mpr hp'; have hg : r=a x*(C:ℝ):=by unfold r a; rw [dust,hS]; ring -- tune C unfold
 let L (x):= 2*y G P.L x*(a x*(Q+4*V)); have hP': 0 ≤ V:=hx; have ha:0 ≤ L x:=by unfold L a; have ht:=dusk_pos P j; have hg:= size x; positivity
 have hB:0 ≤ β:= ((half_pos hv).trans_le hb.1).le; unfold frieze; rw [abs_of_nonneg hB,abs_of_nonneg ?z]; swap
 · have h:0≤r:=by unfold r; positivity
   change 0≤1+β*(r*Q+2*r*V+2*r*V); positivity
 change (1+β*(r*Q+2*r*V+2*r*V))^n ≤ _; have hS':0 ≤ r:=by unfold r; positivity
 apply le_trans (pow_le_pow_left₀ (by positivity) (b:=(1+L x)*(C:ℝ)) ?_ n) -- tune
 · rw [mul_pow]; let t:=Scales.p G P.L x
   change Φ x * (C:ℝ)^n ≤ _; refine (mul_le_mul ((le_abs_self _).trans ((pow_one _).symm.le.trans (hx' S hS O 1 (pin_p hp')))) ?_ (by positivity) (show 0 ≤ espy P k x O.shares from (Real.exp_pos _).le)).trans_eq (show espy P k x O.shares * espy P k x O.shares= _ from ?_)
   · change 1+(n:ℝ)/k ≤ t at hh; have hg:n/(k:ℝ) ≤ t := (le_add_of_nonneg_left zero_le_one).trans hh
     have hz: 1 ≤ t:=by 
        have hh':0≤(n:ℝ)/k:=by positivity
        linarith only [hh',hh]
     unfold espy; refine (pow_le_pow_left₀ (by positivity : 0≤(C:ℝ)) (show (C:ℝ) ≤ Real.exp (C:ℝ) from by linarith [Real.add_one_le_exp (C:ℝ)]) n).trans ?_
     rw [← Real.exp_nat_mul]; apply Real.exp_monotone; exact mul_le_mul_of_nonneg_right (by have hx:= (div_le_iff₀ h).mp hg; change _ ≤ k*t^2; nlinarith) (by positivity)
   unfold espy; rw [←Real.exp_add]; congr 1; ring
 rw [← show r*(Q+4*V)= r*Q+2*r*V+2*r*V from ?_]; swap; · ring
 apply le_trans (add_le_add_right (mul_le_mul_of_nonneg_right hb.2 (by positivity : (0:ℝ) ≤ r*(Q+4*V))) 1)
 unfold L; rw [hg,add_mul,one_mul]; exact add_le_add he (le_of_eq (by ring)) -- tune
end YM.CF.Esti
