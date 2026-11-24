import GaugeFieldConstruction.Ply
import GaugeFieldConstruction.Heliac
/- Gauge average phase extensions. -/
set_option autoImplicit false
set_option maxRecDepth 5500
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
variable {p:BudgetPoint} (o:Skye.Seat n)
open TableF.Lenten.Loden Haro Tap Hove Moto
attribute [local instance] opCStarAlgebra
variable {h v:ℝ}
open Dial Nacre Ember Fir Fock
open Work.F03 Taxi TableF Bank HushP ModuleB Flot RG Hake
variable {o} (M: Male)(P: Waves)
abbrev Silex (W:Pane n→ℂ): Paper n:= isolate none W
lemma sill_V (W: Pane n→ℂ)(U: Pane n): AlphaY (Silex W) U = hollow (W U):=by
 unfold AlphaY; rw [sum_eq_single none]
 · simp [Silex,isolate]; rfl
 · intro j _ p; simp [Silex,isolate,p]
 simp -- tune
lemma sill_G (W: Pane n→ℂ)(p:GaugeInvariant W):portable (Silex W):=by
 intro X g; funext i; unfold αLines; rw [stripeQ,Fintype.sum_option]; have hz(k:Pairs n):Silex W (some k)=0:= (by simp [Silex,isolate]); simp_rw [hz]; cases i <;> simp [boostX,Silex,isolate,cSignX,p g X]
lemma sill_P (W:Pane n→ℂ)(u:Haw p o (Pax o) W v):TrackD p (Pach o) h (Silex W) v:= (show _ from track_p (R:=Pach o) (moorage none trivial W (haw_s o W u)) (one_mul v).le) -- X implicit diff
-- GE signatures
variable {A:InkD n}{F:Paper n}
def D15 (x:Axis)(f:PlaqAxes)(V:Waves): Prop:= ∀ (i: Gem)(j: Sut), bF5 V i j= Complex.ofReal (i.val f.val.1 f.val.2 *divWhite x j)
structure E15(x:Axis)(f:PlaqAxes)(V:Waves):Prop where
 gauge4:bF4 V=0
 phot:chartF V=(0,0,0)
 mixed:bm5 V=0
 gauge:D15 x f V
lemma gauge_Shift (x: ℝ)(q:Clip)(f:PlaqAxes)(l:Axis)(u:MetaB o M P (AlphaY (Silex (Gval o f p q x l))) p h)(e:x≠0)(D:10<(More n).val): E15 l f P ∧ lifeH (AlphaY (Silex (Gval o f p q x l))) 1=0:=by
 let L:=Gval o f p q x l; let X:= Silex L; let T:=AlphaY X; let K:=AnalyticBridge.VerifiedReset.spike SU.group; have hK:‖K‖=1:=AnalyticBridge.VerifiedReset.spike_norm Thera.yet_one; have hf: lifeH T=L:=funext fun i=> by change Pastry.pane (AlphaY (Silex L) i)=_; rw [sill_V,hullB]
 refine ⟨?_, show lifeH T 1=0 from congrFun hf 1|>.trans (prints_zero ..)⟩; have he: TableF.term T=L ∘ increment 1:= congrArg (· ∘ increment (1:Pane n)) hf; have ht(i:Pane n): orbitPH (T i)=0:=by rw [show T i= _ from sill_V L i]; exact hol_l _ -- tune namespace
 constructor
 · apply Subtype.ext; rw [u.post]; apply ContinuousLinearMap.ext; intro i; apply ContinuousLinearMap.ext; intro j; change ploy T (gateC o p.threshold (hem i K)) (gateC o p.threshold (hem j K))=0; rw [ploy_iter,he]; exact prints_wave_a o q l f p x D i j K e
 · rw [u.port, ht]; have hp: TabX o M h (0:Op (Single n))=0:=by funext i; unfold TabX; simp [streamF,hill_Z]
   exact ((tab M _).equal (Eventually.of_forall fun i=>congrFun hp i)).unique (AptK.const _)
 · apply Subtype.ext; rw [u.mixed]; apply ContinuousLinearMap.ext; intro i; let H:=gateC o p.threshold i; have hz: Paint T H=0:=by ext a b; unfold Paint; rw [Matrix.of_apply, show ModuleB.portE T a b=fun _=>0 from funext (fun _=>by unfold ModuleB.portE; rw [ht]; rfl)]; simp
   change sectorJ (Paint T H) _ _ _=0; rw [hz,seat_b]; simp [streamF,hill_Z]
 intro i j; rw [u.mast]; change ploy T (gateC o p.threshold (hem i K)) (gateT o p.threshold (loomH j K))=_; rw [ploy_iter,he]; exact prints_wave_b o q l f p x D i j K hK e
lemma econUni (A B:Waves)(g:bF4 A=bF4 B)(v:bF5 A=bF5 B)(x: bm5 A=bm5 B)(u:chartF A=chartF B): A=B:=Prod.ext (Subtype.ext (congrArg Prod.fst u)) (Prod.ext (Prod.ext g (Subtype.ext (congrArg (fun z:PalOne=>z.2.1) u))) (Prod.ext v (Prod.ext (Subtype.ext (congrArg (fun z:PalOne=>z.2.2.val) u)) x)))
lemma vital {x:Axis}{f:PlaqAxes}{A B:Waves} (p:E15 x f A)(q:E15 x f B): A=B:=econUni _ _ (p.gauge4.trans q.gauge4.symm) (ContinuousLinearMap.ext fun i=>ContinuousLinearMap.ext fun j=> (p.gauge i j).trans (q.gauge i j).symm) (p.mixed.trans q.mixed.symm) (p.phot.trans q.phot.symm)
structure PH15(b:Bool)(V:Waves)(Y:PalOne): Prop where
 gauge4:bF4 V=0
 gauge5:bF5 V=0
 mixed:bm5 V=0
 landing(i:Views): match b with
 | true=> let C:= -(uroS i.1); (chartF V).1=0∧ (chartF V).2.1 i=C*Y.1∧ (chartF V).2.2.val i i=C*Y.2.1 i+C*Y.2.1 i
 | false=>let C:=uroS i.2; (chartF V).1=0∧ (chartF V).2.1 i=Y.1*C ∧ (chartF V).2.2.val i i=Y.2.1 i*C+Y.2.1 i*C
lemma plainΦ (b:Bool)(L:PalOne)(i:Oneκ b L)(t:0<h)(u:20<n.val)(w:p.power ≤3)(e:p.order ≤6)(Q:Waves)(T:MetaB o M Q (AlphaY (Pyl b o (excels o L) h)) p h): PH15 b Q L:=by
 let K:=Pyl b o (excels o L) h; let F:=AlphaY K
 obtain ⟨q0,q1,h0,h1,H,V,S,hC⟩:=shinePH o b L i t u w e M
 let X:=orbitPH (F 1); have hp(v z:tangD n): ploy F v z=0:=by rw [ploy_iter,show TableF.term F=fun _=>0 from (congrArg (· ∘ increment (1:Pane n)) V),iteratedFDeriv_const_of_ne (by norm_num:(2:ℕ)≠0)]; rfl
 refine ⟨Subtype.ext (T.post.trans (ContinuousLinearMap.ext fun i=>ContinuousLinearMap.ext fun j=>hp _ _)), T.mast.trans (ContinuousLinearMap.ext fun i=>ContinuousLinearMap.ext fun j=>hp _ _),Subtype.ext (T.mixed.trans S), fun j=>?_⟩
 revert j; cases b
 · intro j; have hx:=linerR (h:=h) M o (H 1) j; simp only [h0,h1] at hx; change (chartF Q).1=0∧ _; simpa only [T.port] using hx -- wrong rw hx goal simp
 intro j; have hx:=linerL (h:=h) M o (H 1) j; simp only [h0,h1] at hx; change (chartF Q).1=0∧ _; simpa only [T.port] using hx
lemma skis(b:Bool)(L:PalOne)(A B:Waves)(u:PH15 b A L)(v:PH15 b B L): A=B:=by
 have hx(i):=u.landing i; have hp(i):= v.landing i; apply econUni _ _ (u.gauge4.trans v.gauge4.symm) (u.gauge5.trans v.gauge5.symm) (u.mixed.trans v.mixed.symm); cases b <;> exact Prod.ext ((hx 0).1.trans (hp 0).1.symm) (Prod.ext (ContinuousLinearMap.ext fun i=>(hx i).2.1.trans (hp i).2.1.symm) (dual_uni _ _ fun i=> (hx i).2.2.trans (hp i).2.2.symm)) -- wish
lemma silo_e {E:Sut} (A B:InkD n):A=A:=rfl
-- physical left catalogue of all slots
abbrev busC {n:Side}(o:Seat n)(M:Male)(h:ℝ)(p:BudgetPoint)(W:Waves):= Silex (CoverP o (bF4 W).val (bF5 W) p)
abbrev busF{o:Seat n}(W: Waves):= Pyl true o (αPureX o M p W) h
abbrev busG(o:Seat n)(M:Male)(p:BudgetPoint)(h:ℝ)(W:Waves):Paper n:=∑ i:GateI, plac (beamer o neutralK (mallet o (αGuide o M p W h) p i) h) true
abbrev totP:ℝ:= |tentRate| *(Fintype.card lotV:ℝ)
def busγ:ℝ:=abs (∑ i:GateI,tentRate*dietP i)
abbrev bushRate:= totP*abs QuiltB + suitCostH+busγ* |κzone|
lemma banksP (W:Waves)(u:20<n.val)(t:0<h)(x:p.power≤3)(l:p.order ≤6):∃ A:Paper n, TrackD p (Pach o) h A (bushRate * ‖W‖) ∧portable A∧ AlphaY A=αPress o M p W h:=by
 let C':=busC o M h p W; let L:= αPureX o M p W; let F:= busF (h:=h) (p:=p) (o:=o) M W
 let Y:= αGuide o M p W h; let G:=busG o M p h W; let D(i):=mallet o Y p i; let Q(i):=plac (beamer o neutralK (D i) h) true; let S(i):=plac (beamer o i (fun _=> L i) h) true; --
 let T:=bloomT (bF4 W).val (bF5 W); let X:=CoverP o (bF4 W).val (bF5 W) p; let d:= ‖W‖
 have h0:=bean_G W _ le_rfl; have hp:=glyphs.choose_spec.2 n o (bF4 W).val (bF5 W) p x l; have he:=ψTax p T o -- tune from Equerry ψTax
 have hk(i): SheetQ (L i):=field_u M o (chartF W) (chart_j W) i
 have hg:=tagged_P o M t W x l u
 have hu(i):portable (S i):= kinViewP (h:=h) o (fun _=>L i) i (Knot_c o _ (hk i)).motion true
 have hx(i):portable (Q i):=kinViewP (h:=h) o (D i) neutralK (mask_k o Y hg i p).motion true
 have hC:TrackD p (Pach o) h C' (suitCostH*d):=by
    apply track_p (sill_P (o:=o) X hp); have hr:=glyphs.choose_spec.1
    exact (mul_le_mul_of_nonneg_left (add_le_add h0.2.1 h0.2.2.1) (zero_le_one.trans hr)).trans_eq (by unfold suitCostH; rw [←two_mul, ←mul_assoc]) -- tune
 let D':= fena L; have hl:TrackD p (Pach o) h F ((totP*abs QuiltB)*d):=by
    have hp(i): TrackD p (Pach o) h (S i) (tentRate*D'):=marked_w o true _ i (hotB (L i) _ (brew_e L i)) t.ne' u x l -- tune
    apply track_p (track_sum univ S (fun i=>tentRate*D') (fun i _=>hp i)); rw [sum_const,card_univ,nsmul_eq_mul]
    have hc:fena L ≤ |QuiltB| * ‖W‖:= (Cushion (M:=M) o (chartF W) u).trans (mul_le_mul (le_abs_self _) h0.1 (Ole_non _) (abs_nonneg _)); refine (mul_le_mul_of_nonneg_left (mul_le_mul (le_abs_self _) hc (norm_nonneg L) (abs_nonneg _)) (Nat.cast_nonneg (α:=ℝ) (Fintype.card lotV))).trans_eq ?_ ; unfold totP d; ring
 have hs:TrackD p (Pach o) h G (busγ *|κzone| *d):=by
    have hp(i):TrackD p (Pach o) h (Q i) (tentRate*dietP i*tautF Y):=by
       rw [mul_assoc,mul_comm (dietP i)]; exact marked_w o true _ _ (mallet_p o Y i x l) t.ne' u x l
    apply track_p (track_sum univ Q _ fun i _=> hp i); rw [←sum_mul]; apply (mul_le_mul (le_abs_self _) ((entrust_M o M t W x l u).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))) (taut_nonneg Y) (abs_nonneg _)).trans_eq (mul_assoc ..|>.symm) -- tune
 refine ⟨C'+(F+G), track_p (track_a hC (track_a hl hs)) (?_: _),port_add (sill_G _ he) (port_add (port_sum univ S (fun i _=>hu i)) (port_sum univ Q (fun i _=> hx i))),?_⟩
 · apply le_of_eq; unfold bushRate d; ring
 rw [Alpha_add,Alpha_add]; unfold αPress; rw [show AlphaY C'=αGauge o p W from funext fun i=>sill_V ..,show AlphaY G=_ from (show AlphaY G =∑ i:GateI,AlphaY (Q i) from map_sum AlphaL Q univ),show AlphaY F=_ from (show AlphaY F=∑ i:lotV, AlphaY (S i) from map_sum AlphaL S univ)]; rw [show (∑ i:lotV, AlphaY (S i))=αPure o M p W h from sum_congr rfl fun i _=>funext fun u=> plac_ℓ .., show (∑ i:GateI, AlphaY (Q i))= αMixed o M p W h from sum_congr rfl fun i _=>funext fun u=>plac_ℓ ..] -- tune
end MastTin
end YM.CF.XGarden
end
