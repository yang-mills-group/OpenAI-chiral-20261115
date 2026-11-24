import GaugeFieldConstruction.Idlings
import YM.CF.Moto.Road
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
open HushP ModuleB Pastry
-- entries in PH houses: both endpoints. not represented yet as Mark physical.
open Housing
variable (o:Skye.Seat n)
-- A1 frame: g star transport from root at x. B_F paid using transported O.
-- algebra of insertion indices (complex linear in G). prove on paid subspace.
open Flot
set_option maxRecDepth 2800
variable (M:Tulip.Male)
abbrev blurred (f: yardLot)(h:ℝ): InkD n:= ∑ i:lotV,viewW o i (fun _=> f i) h
lemma press_P (f:yardLot)(F:coD f)(u:20<n.val)(p₀:p.power≤3)(t:p.order ≤6)(r:h≠0): PressB p (Zhub o) (blurred o f h) h ((Fintype.card lotV:ℝ)*(CargoMax*palCost)* fena f):=by
 have hv(i:lotV): PressB p (Zhub o) (viewW o i (fun _=> f i) h) h (CargoMax*palCost*fena f):=vistaP o i u p₀ t _ (Knot_c o _ (F i)) (hotB _ _ (brew_e f i)) r
 apply lift_PV (Larch.prop_sum (univ:Finset lotV) _ _ p h (Zhub o) (fun i _=> hv i)); simp only [sum_const,card_univ,nsmul_eq_mul,mul_assoc]; try rfl
lemma snap_blur (f: yardLot): orbitPH (blurred o f h 1)= notesK o f h:=by rw [blurred,Finset.sum_apply,plains]; unfold notesK; apply sum_congr rfl; intro i _; rw [ph_caps,beam_flat]; try rfl
lemma light_blur(f:yardLot):lifeH (blurred o f h)=0:=by rw [blurred,lifeSum]; exact sum_eq_zero fun _ _=> ph_nest ..
abbrev hotSpot:= ‖baseF false‖ * (2*edgeRate) * ‖baseF true‖
private lemma edge_p : 0≤edgeRate:= mul_nonneg (zero_le_one.trans (Kin_1 1 12).choose_spec.1) (by norm_num)
lemma hotFee:0 ≤ hotSpot:=mul_nonneg (mul_nonneg (norm_nonneg _) (mul_nonneg (by norm_num) edge_p)) (norm_nonneg _)
lemma earnings_1(A:Pal)(P:SheetQ A)(k:lotV)(e:20<n.val)(w:p.order≤6)(p₀:p.power≤3)(r:h≠0): tautF (landA M o (viewW o k (fun _=> A) h) p h) ≤ (1/50:ℝ)⁻¹ * (hotSpot*p.threshold*‖A‖):=by
 let X:=viewW o k (fun _=>A) h; let S:=landA M o X p h; let K:=hotSpot*p.threshold*‖A‖;
 have hK:0≤K:= mul_nonneg (mul_nonneg hotFee p.threshold_pos.le) (norm_nonneg _); refine Flot.price_desk S (by norm_num) hK (fun i f=>?_)
 let H:= vistaP o k e p₀ w (fun _=>A) (Knot_c o A P) (hotB _ ‖A‖ le_rfl) r; unfold S X; rw [land_1 M k _ i H 0 r (hasDerivAt_const _ _)] -- order maybe
 let y:= gateC o p.threshold i; let L:=edgeRate*p.threshold; have Sx: p.dirBound o y:= formC_life i o p f
 let F:=pulseI k A 0 A o y; have he : ‖F‖≤2*L* ‖A‖:=by
    let B:=star (DLinx (shoreX k) o y); let C:=DLinx (shoreY k) o y; have hh: ‖B‖ ≤ L:=by unfold B; rw [norm_star]; exact hat_Ω _ (knot_rad k).1 y Sx p₀
    have hp: ‖C‖≤ L:= hat_Ω _ (knot_rad k).2 _ Sx p₀; have hk:‖B*A+A*C‖≤ L*‖A‖+‖A‖*L:= (norm_add_le ..).trans (add_le_add ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_right hh (norm_nonneg _))) ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_left hp (norm_nonneg _))))
    rw [show F=B*A+A*C from (by unfold F pulseI; rw [add_zero])]; exact hk.trans_eq (by ring)
 change ‖baseF false* F* baseF true‖ ≤ _; apply (norm_mul_le ..).trans; apply (mul_le_mul_of_nonneg_right ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_left he (norm_nonneg _))) (norm_nonneg _)).trans_eq; unfold hotSpot L; ring
abbrev mulZone:ℝ:= (Fintype.card lotV:ℝ)*(1/50:ℝ)⁻¹ * hotSpot
private lemma PalA_sum {J:Type}(T:Finset J)(F:J→ ComG→L[ℝ]Pal): tautF (∑ i∈T,F i)≤ ∑ i∈T,tautF (F i):=by -- TC
 exact (show ∀{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](F:J → ComG→L[ℝ]E), tautF (∑ i∈T,F i)≤∑ i∈T,tautF (F i) from fun {_} _ _ f=> norm_sum_le ..) F
lemma earnB_1(f:yardLot)(F:coD f)(e:20<n.val)(w:p.order ≤6)(p₀:p.power≤3)(r:h≠0): tautF (landA M o (blurred o f h) p h)≤ mulZone*p.threshold*fena f:=by
 let V(k:lotV):= viewW o k (fun _=> f k) h; let c:= (CargoMax*palCost)*fena f
 have hp(k): PressB p (Zhub o) (V k) h c:= vistaP o k e p₀ w _ (Knot_c o _ (F k)) (hotB _ _ (brew_e f k)) r
 unfold blurred; rw [landS (o:=o) M (F:=V) _ _ (fun i _=>hp i)] -- tune argument placements
 apply (PalA_sum ..).trans; apply (sum_le_sum (g:=fun k:lotV=> (1/50:ℝ)⁻¹ * (hotSpot*p.threshold*fena f)) _).trans_eq
 · simp only [sum_const,card_univ,nsmul_eq_mul]; unfold mulZone; ring
 intro i _; apply (earnings_1 o M (f i) (F i) i e w p₀ r).trans -- tune order
 exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (brew_e f i) (mul_nonneg hotFee p.threshold_pos.le)) (by norm_num)
-- Mixed section; target adjoint intertwiner. using ζedge first coordinate.
variable (A:ComG→L[ℝ]Pal)
def mallet (p:BudgetPoint) (i:GateI) (V:Pane n) := A (hem (ζedge i).1 (πon o i p V))
abbrev capT(p:BudgetPoint)(h:ℝ): InkD n:= ∑ i:GateI, viewW o neutralK (mallet o A p i) h
lemma mask_k(Z:ViewsM A)(i:GateI)(p:BudgetPoint): KnotK o (mallet o A p i):=by
 constructor; · intro V g; let a:= (ζedge i).1; unfold mallet; rw [πGauge]; let k:=g o; let v:= πon o i p V; change A (coneC a (SU.group.adjoint k v))= KinX k * A (coneC a v)* star (KinX k); rw [← Z.main k a v]; rw [mul_assoc,Kin_S,mul_one] -- tune complement
 intro V; exact Z.binned _
omit M
abbrev handV(a:Gem): SU.group.Color→L[ℝ] ComG:= (coneC a).toContinuousLinearMap
abbrev dietP(i:GateI) := tautF (handV (ζedge i).1) * F_grade.choose
lemma mallet_p (i:GateI)(p₀:p.power≤3)(t:p.order ≤6): Housing.Haw p o (Pax o) (mallet o A p i) (tautF A*dietP i):= svelte (svelte (F_grade.choose_spec.2 n o i p p₀ t) (handV (ζedge i).1)) A
abbrev hat_Pe(k:GateI):ℝ:= CargoMax*palCost*dietP k
abbrev valorP:=∑ i:GateI,hat_Pe i
lemma press_m (Z:ViewsM A)(u:20<n.val)(p₀:p.power≤3)(t:p.order ≤6)(r:h≠0): ∀ i: GateI,PressB p (Zhub o) (viewW o neutralK (mallet o A p i) h) h (hat_Pe i*tautF A):=by
 intro i; apply lift_PV (vistaP o neutralK u p₀ t _ (mask_k o A Z i p) (mallet_p o A i p₀ t) r); unfold hat_Pe; apply le_of_eq; ring
lemma tipB (Z:ViewsM A)(u:20<n.val)(p₀:p.power≤3)(t:p.order≤6)(r:h≠0): PressB p (Zhub o) (capT o A p h) h (valorP*tautF A):=by
 apply lift_PV (Larch.prop_sum (univ:Finset GateI) _ _ p h (Zhub o) (fun i _=>press_m o A Z u p₀ t r i)); rw [← sum_mul]
lemma tide_p(i:GateI): mallet o A p i 1=0:=by unfold mallet; rw [π_flat,show hem (ζedge i).1 0=0 from map_zero (handV _),map_zero]
lemma tide_g:orbitPH (capT o A p h 1)=0:=by
 rw [capT, Finset.sum_apply,plains]; apply sum_eq_zero; intro i _; rw [ph_caps,beam_flat,tide_p]; unfold modelK seed_k; ext a b; simp
lemma tide_scalar: lifeH (capT o A p h)=0:=by rw [capT,lifeSum]; exact sum_eq_zero fun _ _=> ph_nest ..
include M
lemma tide_Z (Z:ViewsM A)(u:20<n.val)(p₀:p.power≤3)(t:p.order≤6)(r:h≠0): landA M o (capT o A p h) p h=A:=by
 let F(i:GateI):= viewW o neutralK (mallet o A p i) h; let L(i:GateI):= landA M o (F i) p h; rw [capT,landS (o:=o) M (F:=F) _ (fun i=>hat_Pe i*tautF A) (fun i _=>press_m o A Z u p₀ t r i)]; apply ContinuousLinearMap.ext; intro x
 have ht(a:Gem)(z:SU.group.Color)(i:GateI) : L i (hem a z)=A (handV (ζedge i).1 (acCue a i • z)):=by
    let H:= handV (ζedge i).1; let d:= acCue a i • z; let W:= mallet o A p i; let y:=hem a z; let w:= gateC o p.threshold y; have he: 10 < (More n).val:=by change _<n.val*2; omega
    have hp: HasDerivAt (fun x:ℝ=> W (increment 1 (x • w))) (A (H d)) 0:= (A.comp H).hasFDerivAt.comp_hasDerivAt 0 (π_sun (o:=o) he a z p i)
    unfold L F; rw [land_1 M neutralK _ _ (press_m o A Z u p₀ t r i) _ r hp,tide_p]; unfold pulseI; rw [mul_zero,zero_mul, add_zero,zero_add]; exact Z.binned _
 have he (a:Gem)(z:SU.group.Color): (∑ i:GateI,L i) (hem a z)= A (hem a z):=by
    have hv:∑ i:GateI,(acCue a i) • (ζedge i).1=a:=by
       simp_rw [← ac_pack]; exact congrArg Prod.fst (merc (a,0))|> fun e=> (Prod.fst_sum ..|>.symm.trans e) -- tune
    have hz(i:GateI): handV (ζedge i).1 (acCue a i • z)= grayC z (acCue a i • (ζedge i).1):= Eq.trans (map_smul ..) (map_smul (grayC z) (acCue a i) (ζedge i).1|>.symm) -- tune TC
    rw [_root_.sum_apply]; simp_rw [ht,hz,← map_sum,hv]; try rfl
 let P:=(∑ i:GateI,L i);
 change P x=A x; rw [trade_Z x,map_sum,map_sum]; exact sum_congr rfl fun i _=> he _ _
end Layout
end Lenten
end YM.CF.TableF
end
