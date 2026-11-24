import YM.SU5.FiniteGaugeData.LapisQ.Jubilat
import YM.SU5.FiniteGaugeData.LapisQ.Aube
import YM.SU5.FiniteGaugeData.Lapis.Lease
set_option autoImplicit false
set_option maxHeartbeats 620000
set_option synthInstance.maxSize 23000
noncomputable section
namespace YM.SU5.FiniteGaugeData.LapisQ
open Function Finset Filter MeasureTheory ProbabilityTheory Matrix Lattice Wilson RG Precision Tree Next.Fluctuations Work.F03
open Pressure Exterior Laurent Bloch Drachma Galope Avenue Galope.Press Wrist Poeme Haute Lapis Punch Affiche Work.F06
open scoped Topology InnerProductSpace Matrix MatrixOrder RealInnerProductSpace ContDiff BigOperators NNReal ENNReal Kronecker Classical
set_option quotPrecheck false
namespace Nectar
open Nosh Apoth Real Vulcan Willow Lumi
variable (G:Gauge) {n:Side} {z:Cover} (p q:PlaqAxes)(x:Cover)
noncomputable def sprinkle (x:Cover) (p:PlaqAxes): Slot:= ⟨Lattice.route 0 x 1, p⟩
lemma wet : (sprinkle x p).offset=x:=route_end ..
lemma wet0(x:Cover) (y:Site n): slotFace (sprinkle x p) y=(wrap n x+y,p) :=by rw [slotFace,wet]; rfl
lemma mentor_C {E:Type*}[NormedAddCommGroup E] [InnerProductSpace ℝ E] : ContDiff ℝ 1 (fun x:E=>mentor x):=by
 unfold mentor; exact (contDiff_norm_sq (𝕜:=ℝ) (E:=E)).neg.div_const 2 |>.exp
lemma mentor_z {E:Type*}[NormedAddCommGroup E][InnerProductSpace ℝ E](x y:E) : ‖mentor x-mentor y‖ ≤ ‖x-y‖:=by
 let f(t:ℝ):=Real.exp (-t^2/2); have ht(t:ℝ):HasDerivAt f (-t*f t) t:=by
    have he:= ((hasDerivAt_id' t).pow 2).neg.div_const 2 |>.exp; convert! he using 1; unfold f; dsimp; ring
 have hp(t:ℝ)(v:t∈Set.Ici (0:ℝ)): ‖-t*f t‖≤1:=by
    have hv:0≤t:=v; have he:0< f t:=Real.exp_pos _; rw [norm_mul,norm_neg,Real.norm_of_nonneg hv,Real.norm_of_nonneg he.le]; unfold f; rw [neg_div, Real.exp_neg,←div_eq_mul_inv]; apply (div_le_one (Real.exp_pos _)).2; nlinarith only [Real.add_one_le_exp (t^2/2), sq_nonneg (t-1)] -- neg_div wrong direction
 change ‖f _-f _‖ ≤_; apply le_trans (b:=1* ‖‖x‖-‖y‖‖) ; · exact (convex_Ici _).norm_image_sub_le_of_norm_hasDerivWithin_le (fun t _=> (ht t).hasDerivWithinAt) hp (norm_nonneg _) (norm_nonneg _)
 rw [one_mul]; exact abs_norm_sub_norm_le ..
#check Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
private lemma mult_price {E:Type*}[NormedAddCommGroup E][InnerProductSpace ℝ E](x y:Bool→E): |mentor (x false)*mentor (x true)-mentor (y false)*mentor (y true)|≤2 *‖x-y‖:=by
 have h(a b:Bool)(r:ℝ)(e:|r|≤1): |r * (mentor (x a)-mentor (y a))| ≤ ‖x-y‖:= by rw [abs_mul]; refine le_trans (mul_le_of_le_one_left (abs_nonneg _) e) (le_trans (mentor_z ..) (norm_le_pi_norm (x-y) a))
 have he(x:E): |mentor x|≤1:=by rw [abs_of_nonneg (pollen_a x).1]; exact (pollen_a x).2
 let r(x:Bool→E)(a:Bool):= mentor (x a)
 change |r x false*r x true-r y false*r y true|≤_
 rw [show r x false*r x true-r y false*r y true = r y false*(r x true-r y true)+r x true*(r x false-r y false) from (by ring)]; apply (abs_add_le ..).trans; rw [two_mul]; exact add_le_add (h true true _ (he _)) (h false false _ (he _))
noncomputable def zenY(p: Slot) : Duct G Unit where
 beam _:= p
 seen u:= mentor (u ())
 registered:= mentor_C.comp (show ContDiff ℝ 1 (fun x:Unit→ G.Color=> x ()) from (by fun_prop))
 c:=1
 h:=1
 grant:=zero_le_one
 charge:=zero_le_one
 enough x:= by rw [Real.norm_of_nonneg (pollen_a _).1]; exact (pollen_a _).2
 cheer x y:=by simp only [one_mul]; exact (mentor_z (x ()) (y ())).trans (norm_le_pi_norm (x-y) ())
 orbs:= fun u x=> by simp [mentor]
noncomputable def dualY (p q:Slot): Duct G Bool where
 beam b:= if b then q else p
 seen x:= mentor (x false)*mentor (x true)
 registered:= (mentor_C.comp (show ContDiff ℝ 1 (fun x:Bool→ G.Color=> x false) from (by fun_prop))).mul (mentor_C.comp (show ContDiff ℝ 1 (fun x:Bool→ G.Color=> x true) from (by fun_prop)))
 c:=2
 h:=1
 grant:=zero_le_two
 charge:=zero_le_one
 enough x:=by
    rw [norm_mul]; apply (mul_le_mul (b:=1) (d:=1) ?_ ?_ (norm_nonneg _) zero_le_one).trans_eq (one_mul _); all_goals rw [Real.norm_of_nonneg (pollen_a _).1]; all_goals exact (pollen_a _).2
 cheer:= mult_price
 orbs:= fun u x=> by simp [mentor]
-- physical live uses NORMAL orientation at site root. On Cover Mark labels with optional rephase.Lens charges true.
variable {G p q}(s:Clip)(r:ℝ)(U:Config G n)(V:Site n)
noncomputable def wardF(s:Clip)(r:ℝ)(U:Config G n)(p:Cell n):ℝ:= mentor ((r*Real.sqrt s.direct) • (G.curvature (faceValue U p)))
private lemma plainZ (i:Slot): Lumi.probe (zenY G i) 1 V U ()= i.atSite U V:=by
 unfold Lumi.probe; rw [Slot.atSite,expandAt_pull]; simp only [affine,Signed.act_one, zero_add,pull_id]; rfl
lemma zenZ (i:Slot): Lumi.live (zenY G i) s r 1 V U= wardF s r U (slotFace i V):=by
 unfold Lumi.live wardF; change mentor ((r*Real.sqrt s.direct) • (Lumi.probe (zenY G i) 1 V U ()))=_; rw [plainZ,atSite_path,←map_smul]; simp [mentor,norm_smul]
lemma dualZ(i j:Slot): Lumi.live (dualY G i j) s r 1 V U= Lumi.live (zenY G i) s r 1 V U* Lumi.live (zenY G j) s r 1 V U:=rfl -- if reduce bool classical irr
--- polarized simply right pay.Any alt
lemma orientZ(i:Slot)(o:Signed): Lumi.live (zenY G i) s r o V U= Lumi.live (zenY G (pick (G:=G) o i).1) s r 1 V U:=by
 unfold Lumi.live; let w:= pick (G:=G) o i; let z:=r*Real.sqrt s.direct; change mentor (z • Lumi.probe (zenY G i) o V U ())=mentor (z • Lumi.probe (zenY G w.1) 1 V U ()); rw [looks,plainZ]; change mentor (z • (w.2 • w.1.atSite U V))= _; rcases (marker (G:=G) o i).1 with he|he; · rw [show w.2=1 from he,one_smul]
 rw [show w.2=-1 from he,neg_one_smul, smul_neg]; simp [mentor]
end Nectar
end YM.SU5.FiniteGaugeData.LapisQ
#print axioms YM.SU5.FiniteGaugeData.LapisQ.Nectar.zenZ
#print axioms YM.SU5.FiniteGaugeData.LapisQ.Nectar.orientZ
