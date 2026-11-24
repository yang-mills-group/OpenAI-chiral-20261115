import Risa.Cultural
import Compass.Prime
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Channels
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.flexible false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 305000
noncomputable section
namespace YM.Gleam.Luster
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ v' ν θ ω':ℝ}{U:Config G n}{A:Support c}{m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
variable {X Y:fieldDir G n 1}{D:Finset (Cell n)}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)(D':LocalRatio J)
namespace Risa
open Regis ProbabilityTheory
open _root_.YM.Regis.Head AnalyticBridge.VerifiedReset StressFlux Lattice.PlaqAxes Virgo _root_.YM.CF.Scree
namespace Ridgetop
abbrev Raw:=fieldDir G n 1
-- operation on tiler. first on raw
abbrev salt(o:Site n)(i:PlaqAxes)(x:@Raw n G):G.Color:= floret G i (fun h:Stitch=> faceCurl (slotFace (ringT G h) o) x)
variable (o:Site n)
lemma hiker_d (i:PlaqAxes)(x:fieldDir G n 1): HasDerivAt (fun t:ℝ=> petals (represent (t • x)) o i) (salt o i x) 0:=by
 have hd (t:ℝ): petals (represent (t • x)) o i = floret G i (fun h:Stitch=>(ringT G h).atSite (represent (t • x)) o):=by
   unfold floret petals clover stencil; simp_rw [←dial_s]; rfl
 simp_rw [hd]; unfold salt floret
 have hu (h:Stitch):= (slot_deriv (ringT G h) o x).const_smul (lipT G h)
 exact (( (hu (i,false,false)).sub (hu (i,false,true))).sub ((hu (i,true,false)).sub (hu (i,true,true)))).const_smul ((4:ℝ)⁻¹)
-- rotate lambda
lemma swivelV (i:PlaqAxes)(x:fieldDir G n 1)(s:Signed)(b:Site n): salt o i (bank s b x)=reframe (fun j=>salt (affine s b o) j x) s i:=by
 have h:= hiker_d o i (bank s b x); simp_rw [bank_at,petals_moves] at h
 apply h.unique; unfold reframe; apply HasDerivAt.const_smul (c:= StressFlux.sign s i.val.1 * StressFlux.sign s i.val.2); refine (HasDerivAt.sub ?_ ?_)
 all_goals simp only [orderedDir]; split_ifs <;> first| exact hiker_d ..|exact hasDerivAt_const ..
#print axioms swivelV
abbrev heeled(o:Site n)(i:PlaqAxes)(x:Altar G n): G.Color:= floret G i (fun h:Stitch=> Etch.river q (slotFace (ringT G h) o) x)
variable (Xh:Hike)
local notation "Υ"=>posess G Xh
local notation "χ"=>Xh.cost
-- at identity orientation, lose the skew.S
lemma canon(y:ℝ)(x:fieldDir G n 1): (Υ).chalk q y 1 o (tiler B P x)=(Υ).sketch q y o (tiler B P x):=by
 rw [Etch.chalk_now]; unfold Etch.sketch; simp_rw [Etch.river_now q B P]
 apply congrArg (Υ).f; funext i; apply congrArg _;

 have hp:=slot_deriv ((Υ).slot i) 0 (bank 1 o x); simp_rw [bank_at,Slot.atSite,expandAt_pull,pull_id,affine,Signed.act_zero,zero_add] at hp; exact hp.unique (slot_deriv _ _ _)
-- separate
lemma sketch_is(y:ℝ)(x:Altar G n):(Υ).sketch q y o x=(∑ i:PlaqAxes,(CF.Compass.decor i:ℝ)*Virgo.clipQ χ (y • @heeled n G q o i x))/2:=by
 unfold Etch.sketch posess viaduct; dsimp only
 congr 1; refine sum_congr rfl fun i _=>?_
 let v:=fun i:Stitch=>Etch.river q (slotFace (ringT G i) o) x; change _*Virgo.clipQ χ (floret G i (y • v))=_; rw [floret_smul]
lemma heeled_tiler(i:PlaqAxes)(x:fieldDir G n 1): @heeled n G q o i (tiler B P x)=salt o i x:=by unfold heeled salt; simp_rw [Etch.river_now q B P]
open CF.Compass
-- neg by X side01. need cast
lemma unrule (s:Signed)(v:Anchored s)(h:tariffX s=true)(F:PlaqAxes→ℝ): (∑ i:PlaqAxes,(decor i:ℝ)*F (PlaqAxes.transform s i))= -(∑ i:PlaqAxes,(decor i:ℝ)*F i):=by
 let g(i:PlaqAxes):=(decor i:ℝ)*F i; change _= -(∑ i,g i)
 rw [← Equiv.sum_comp (PlaqAxes.transform s) g,←Finset.sum_neg_distrib]
 refine sum_congr rfl fun i _=>?_
 have he: (((decor (PlaqAxes.transform s i)):ℤ):ℝ)= -(decor i:ℝ):=by
    exact_mod_cast (show decor (PlaqAxes.rotate s i) = -(decor i:ℤ) from by rw [sail_decide s v,h]; change (-1 : ℤ)* _=_; exact neg_one_mul _)
 dsimp only [g]; rw [he]; ring
include B P L
lemma slice_zero (O:Bid.Sworn H n G)(y:ℝ): clouds B P ((Υ).sketch q y o)=0:=by
 let s:Signed:= CF.Pec.X side01
 let u:Site n:=o-s.act o
 let f:=(Υ).sketch q y o
 have h:=cover_calms s u B P L O f (fun x=> -f x) (Etch.sketch_smooth ..|>.continuous) (fun V=>?_)
 swap
 · unfold f; rw [sketch_is,sketch_is]; simp_rw [heeled_tiler B P _, swivelV _ _ _ _ _, show affine s u o=o from (by unfold affine u; abel)]
   unfold Virgo.clipQ Virgo.coil
   simp_rw [norm_smul y,reframe_norm] -- syntax
   let f(i:PlaqAxes):=χ^2*(‖y‖*‖salt o i V‖)^2/(χ^2+(‖y‖*‖salt o i V‖)^2); change (∑ x:PlaqAxes, (decor x:ℝ) * f (transform s x))/2= -((∑ x:PlaqAxes, (decor x:ℝ) * f x)/2)
   rw [unrule _ quad_anchor (tax_s _ _ (by decide:(0:Axis)≠1)) f]; ring
 unfold clouds at h; rw [integral_neg] at h; change (∫ x : stamen B P n,f x.val ∂_) = _; linarith only [h]
lemma meal_m (O:Bid.Sworn H n G)(y:ℝ)(o:Bool→Site n)(s:Bool→Signed): meal B P Xh y false o s=0:=by
 change clouds B P _ =_
 have he:=Etch.paid_chalk Υ q y (s true) (o true) B P L O
 exact he.trans (slice_zero B P L (0:Site n) Xh O y)
#print axioms meal_m
end Ridgetop
end Risa
end YM.Gleam.Luster
