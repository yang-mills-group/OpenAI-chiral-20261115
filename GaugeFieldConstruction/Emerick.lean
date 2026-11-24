import GaugeFieldConstruction.Liberate
import GaugeFieldConstruction.Monition
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
namespace ArtCart
open Buffered Lifted Girt Skye Window Vale
variable {x:Cover}{d:ℕ}{k:Side}
open TableF TableF.Lenten Layout Flot Moto Tap Bank ModuleB Haro Hove Fren Work.F03 Taxi Ember Fir HushP
variable {F H:Paper n}{p:BudgetPoint}{c v h:ℝ}(M: Male){o:Seat n}
def Bush(o:Seat n)(M:Male)(p:BudgetPoint)(h:ℝ)(W:Waves):Paper n:= busC o M h p W+(busF (h:=h) (p:=p) (o:=o) M W+busG o M p h W)
lemma bush_S (W:Waves)(u:20<n.val)(t:0<h)(x:p.power≤3)(l:p.order ≤6):let A:=Bush o M p h W; TrackD p (Pach o) h A (bushRate * ‖W‖) ∧portable A∧ AlphaY A=αPress o M p W h:=by
 intro A
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
 refine ⟨track_p (track_a hC (track_a hl hs)) (?_: _),port_add (sill_G _ he) (port_add (port_sum univ S (fun i _=>hu i)) (port_sum univ Q (fun i _=> hx i))),?_⟩
 · apply le_of_eq; unfold bushRate d; ring
 change AlphaY (C'+(F+G))=_; rw [Alpha_add,Alpha_add]; unfold αPress; rw [show AlphaY C'=αGauge o p W from funext fun i=>sill_V ..,show AlphaY G=_ from (show AlphaY G =∑ i:GateI,AlphaY (Q i) from map_sum AlphaL Q univ),show AlphaY F=_ from (show AlphaY F=∑ i:lotV, AlphaY (S i) from map_sum AlphaL S univ)]; rw [show (∑ i:lotV, AlphaY (S i))=αPure o M p W h from sum_congr rfl fun i _=>funext fun u=> plac_ℓ .., show (∑ i:GateI, AlphaY (Q i))= αMixed o M p W h from sum_congr rfl fun i _=>funext fun u=>plac_ℓ ..] -- tune
lemma bush_T (W:Waves)(u:20<n.val)(t:0<h)(x:p.power≤3)(l:p.order ≤6): Tuned (Bush o M p h W):=by
 let L:= αPureX o M p W; let H:=αGuide o M p W h
 refine tuning_a (tune_s _) (tuning_a (tuning_sum _ _ (fun i _=>?_)) (tuning_sum _ _ (fun i _=>?_))) -- tune
 · exact tunedΘ o i _ (Knot_c o _ (field_u M o (chartF W) (chart_j W) i)) u
 exact tunedΘ o neutralK _ (mask_k o H (tagged_P o M t W x l u) i p) u -- tune implicit i
abbrev sigVal (F:Paper n):Prop:= ∀ i j: Single n, F (some (false,i,j))=0
lemma sigUni (A B:Paper n)(h:sigVal A)(p:sigVal B)(x:AlphaY A=AlphaY B):A=B:=by
 funext i v; have hf(i): thrust A i=thrust B i:=by rw [←(bpu_T ..).1,←(bpu_T ..).1,x];
 rcases i with _|⟨b,i,j⟩; · rw [←(bpu_T A v).2, ←(bpu_T B v).2,x]
 cases b; · rw [h,p]
 have ht:A (some (true,i,j)) v+-A (some (false,j,i)) v=B (some (true,i,j)) v+-B (some (false,j,i)) v:= Matrix.ext_iff.mpr (hf v) i j; simpa [h,p] using ht
lemma bush_V (W: Waves)(o:Seat n)(p:BudgetPoint)(h:ℝ):sigVal (Bush o M p h W):=by
 intro i j; simp [Bush,busG,busF,busC,Silex,Pyl,plac,isolate]
lemma bush_a (V W:Waves)(u:20<n.val)(t:0<h)(x:p.power≤3)(l:p.order ≤6):Bush o M p h (V+W)=Bush o M p h V+Bush o M p h W:=by
 let F:= Bush o M p h; let G:= hatchP o M t x l u; have ht(U:Waves): AlphaY (F U)= G U:=(bush_S M U u t x l).2.2
 exact sigUni _ _ (bush_V M _ o p h) (fun i j=>by rw [Pi.add_apply,bush_V M _ o p h i j,bush_V M _ o p h i j,add_zero]) (by change AlphaY (F (V+W))= _; rw [ht,map_add,Alpha_add]; change _=AlphaY (F V)+AlphaY (F W); rw [ht,ht])
lemma bush_m (V:Waves)(c:ℂ)(u:20<n.val)(t:0<h)(x:p.power≤3)(l:p.order ≤6): Bush o M p h (c • V)= c • Bush o M p h V:=by
 let F:= Bush o M p h; let G:= hatchP o M t x l u; have ht(U:Waves): AlphaY (F U)= G U:=(bush_S M U u t x l).2.2
 exact sigUni _ _ (bush_V M _ o p h) (fun i j=>by rw [Pi.smul_apply,bush_V M _ o p h i j,smul_zero]) (by change AlphaY (F (c • V))=_; rw [ht,map_smul,Alpha_s]; change c • G V=_; rw [←ht V])
-- alpha radial kernels.
abbrev CurveS(o:Seat n)(p:BudgetPoint)(h:ℝ)(W:Waves)(r:Sweep n):Paper n:=Barber r (Bush (sh r⁻¹ o) M p h (Mason r⁻¹ W))
abbrev Ť (n:Side):ℂ:= (Fintype.card (Sweep n):ℂ)⁻¹
def bushMoon (o:Seat n)(p:BudgetPoint)(h:ℝ)(W:Waves):Paper n:= Ť n • ∑ r:Sweep n,CurveS M o p h W r
lemma ray_V (W:Waves)(u:20<n.val)(t:0<h)(x:p.power≤3)(l:p.order ≤6): Tuned (bushMoon M o p h W):= tuning_h (tuning_sum _ _ (fun i _=> Tune_s i (bush_T M (Mason i⁻¹ W) u t x l))) _ -- placeholders
variable (p)
lemma curve_send (s r:Sweep n)(o:Seat n)(h:ℝ)(W:Waves):Barber r (CurveS M o p h W s)= CurveS M (sh r o) p h (Mason r W) (s*r):=by
 have he: sh (s*r)⁻¹ (sh r o)=sh s⁻¹ o:=by rw [azimuth,mul_inv_rev,← mul_assoc,mul_inv_cancel,one_mul]
 unfold CurveS; rw [barber_L,he,sh_Pi]
lemma birth_ψ{I:Type*} (S:Finset I)(F:I→Paper n)(r:Sweep n): Barber r (∑ i∈S,F i)=∑ i∈ S, Barber r (F i):=by induction S using Finset.induction_on with|empty=>rw [sum_empty,sum_empty,bornØ]|@insert i S p ih=>rw [sum_insert p,sum_insert p,born_Z,ih]
lemma ray_send (r:Sweep n)(o:Seat n)(h:ℝ)(W:Waves): Barber r (bushMoon M o p h W)= bushMoon M (sh r o) p h (Mason r W):=by
 unfold bushMoon; rw [born_P,birth_ψ,show payZ r (Ť n)=Ť n from ?_]; swap
 · unfold payZ cSignX; split; · simp [Ť]
   rfl
 apply congrArg (Ť n • ·); exact Fintype.sum_equiv (Equiv.mulRight r) _ _ fun i=> curve_send ..
variable {p}
lemma ray_K (W:Waves)(u:20<n.val)(t:0<h)(x:p.power≤3)(l:p.order ≤6)(r:Sweep n):AlphaY (CurveS M o p h W r)= facetW r p M h o W:=by
 let U:= sh r⁻¹ o; let F:= Bush U M p h (Mason r⁻¹ W); let V:= AlphaY F
 have he: V= αPress U M p (Mason r⁻¹ W) h:=(bush_S M _ u t x l).2.2; unfold facetW buoyB; rw [← he]; exact T_uni r (axis_V F r) -- tune
lemma ray_M (W:Waves)(u:20<n.val)(t:0<h)(x:p.power≤3)(l:p.order ≤6): AlphaY (bushMoon M o p h W)= shoulder o p M h W:=by
 unfold bushMoon; rw [Alpha_s]; apply congrArg (Ť n • ·); rw [show AlphaY _= _ from (show AlphaY (∑ r:Sweep n,CurveS M o p h W r)=∑ i:Sweep n, AlphaY (CurveS M o p h W i) from map_sum AlphaL _ _)]; exact sum_congr rfl fun i _=>ray_K M W u t x l i -- tune
-- roof finances.Calendar.
def morgue:= (CaseL:ℝ)*|bushRate| * tilos
lemma MR_0:0≤ morgue:=by unfold morgue tilos; positivity
lemma ray_B (W:Waves)(u:300<n.val)(t:0<h)(x:p.power≤3)(l:p.order ≤6)(v:ℝ) : TrackD p (Pach o) h (bushMoon M o p h W) (morgue* ‖W‖) ∧portable (bushMoon M o p h W)∧ Portage (bushMoon M o p h W,0) o p h v W M (morgue* ‖W‖) 0:=by
 let H:= morgue* ‖W‖; let V(r:Sweep n):=Mason r⁻¹ W; let P(r:Sweep n):= CurveS M o p h W r
 have he(r:Sweep n):= (bush_S (o:=sh r⁻¹ o) M (V r) (lt_trans (by omega) u) t x l)
 have hp(r:Sweep n): TrackD p (Pach o) h (P r) H:=by
    apply track_p (u:= (?_:TrackD p (Pach o) h (P r) ((CaseL:ℝ)*(bushRate* ‖V r‖))))
    · unfold H morgue; rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul (le_abs_self _) (sheen_norm ..) (norm_nonneg _) (abs_nonneg _)) (Nat.cast_nonneg _)
    · have ht:= tiltY r (sh r⁻¹ o); rw [azBack] at ht; rw [←ht]; exact tiltFee r (he r).1 -- tune matcher
 have hx: TrackD p (Pach o) h (bushMoon M o p h W) H:=by
    apply track_p (track_h (track_sum univ P (fun _=>H) fun i _=>hp i) _); unfold Ť; simp only [norm_inv, Complex.norm_natCast,sum_const,card_univ,nsmul_eq_mul]; rw [←mul_assoc,inv_mul_cancel₀ mag_h.ne',one_mul] -- tune
 have hg:portable (bushMoon M o p h W):=port_m (port_sum _ _ (fun i _=> barber_tru _ 1 _ (he i).2.1)) _ -- tune
 obtain ⟨hM,hL,H⟩:= stronghold (o:=o) M u t x l W;
 rw [← ray_M M W (by omega) t x l] at hL hM;
 exact ⟨hx,hg, ⟨hx,trace_Z⟩,⟨hg,fun i=>port_Z⟩,hM,hL⟩
end ArtCart
end MastTin
end YM.CF.XGarden
end
