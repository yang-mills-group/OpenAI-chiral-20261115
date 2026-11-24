import WakeRoad.Mirror
import YM.Next.MAXWELL.Pole
/-! # Vote on actual growing mixed test. -/
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark SatinVerification Vacancy Tapestry
open CF.Pannier.Chancel
open Preparation.Yoke EmberWind Jewel
open Lamour.Bridge.Celeste Morn
open Ballad
open SpinReceipt Shuttle
open Papal (Weaver household)
open WakeInvestment
namespace Spine
variable (P:Spine) {S:Finset Cover} {F:Family P.calibration} (j:Axis)
-- credit without ever asserting continuity at the Mark boundary
lemma shift_cover3 (p:InTest P.calibration true S false F)(k:ℕ):
    let u : P.Test:= P.art F (aux_test p)
    (P.halfShift j k u)∈ bay P.calibration (onFlight P.par.block S j k) true:=by
  intro u; apply (Tapestry.locates ..).2; change InTest _ _ _ _ (mirror _ _ (Heat.gaugeShift P.par.block k) (mirror _ _ 0 F)); let h:= axial _ j (Heat.gaugeShift P.par.block k) (axial P.calibration j 0 p); rw [Tower.support_translation,sub_zero] at h; exact h
lemma creditShelf (p:InTest P.calibration true S false F)(s k:ℕ)(e:Tower.region j 0 P.calibration.ℓ (onFlight P.par.block S j k)):
    let u:P.Test:=P.art F (aux_test p); let v:=P.halfShift j k u; (∫ x, ‖P.singleState j s x u‖^2 ∂ (P.pillars j)) ≤ ‖P.E s (mirror P.calibration j 0 v.val * v.val)‖:=by
 intro u v; let y:=P.positiveVox j s _ v (P.shift_cover3 j p k) e
 have h(x:P.Spectrum0 j):P.singleState j s x u=P.singleState j s x v:=by unfold v; rw [P.single_state,P.single_state,P.halfReads]
 simp_rw [h,P.single_state,P.pillar_]; rw [at_label]; change ‖P.compressed j s (P.voxTest j s y) (P.groundZero j)‖^2 ≤ ‖P.E s (mirror _ _ _ y.val*y.val)‖
 rw [←P.seed_pairing, inner_self_eq_norm_sq_to_K,norm_pow,RCLike.norm_ofReal,abs_of_nonneg (norm_nonneg _),P.seed]; exact pow_le_pow_left₀ (norm_nonneg _) (Submodule.norm_orthogonalProjectionOnto_apply_le ..) 2
end Spine
namespace GramSignal
open CF.Hiro CF.Onyx Regis.Head.Brecht Ballad
open Stationary (Gaia)
lemma decay_pair {x:ℕ→ Gaia}(h:Tendsto (fun i=> ‖x i‖) atTop atTop)(A B:PlaqAxes):
    Tendsto (fun i=> shotR 0 0 (X:=x i)*speckleV A B SU.group (x i)) atTop (𝓝 0) := by
 obtain ⟨C,hp,t⟩:= (Maxwell.Free.bare_pole A.val.1 A.val.2 B.val.1 B.val.2).bounds
 have ht:Tendsto (fun i=> ‖x i‖⁻¹) atTop (𝓝 0):=tendsto_inv_atTop_zero.comp h
 let Q:= Maxwell.bareCurl A.val.1 A.val.2 B.val.1 B.val.2
 have hv:Tendsto (fun i=> Q (x i)) atTop (𝓝 0):= tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) ((h.eventually_gt_atTop 0).mono (fun i x=> t _ (norm_pos_iff.mp x))) (show Tendsto (fun i=> C* ‖x i‖⁻¹^4) atTop (𝓝 0) by simpa only [zero_pow (by decide:(4:ℕ)≠0),mul_zero] using ((ht.pow 4).const_mul C)))
 have hx:Tendsto (fun n=>speckleV A B SU.group (x n)) atTop (𝓝 0):=by
    change Tendsto (fun n=> (Fintype.card SU.group.ColorIndex:ℂ)*(Q (x n):ℂ)) _ _; simpa using (Complex.continuous_ofReal.continuousAt.tendsto.comp hv).const_mul (Fintype.card SU.group.ColorIndex:ℂ)
 have hy{v:ℕ→ Gaia}(t:Tendsto (fun i=> ‖v i‖) atTop atTop): Tendsto (fun n=>shotL (v n) 0 0) atTop (𝓝 0):= kP_further v t
 have hz:Tendsto (fun i=> ‖-x i‖) atTop atTop:=by simp [h]
 simpa only [mul_zero,shotR] using (((hy h).const_mul (-60:ℂ)).mul (hy hz)).mul hx
open Pressure
variable (P:Spine)(β:ℕ→ℝ)
abbrev tee (s:ℕ)(u:Cover)(D:PlaqAxes):= choiceWeave P β (localStaff u 0 D) 4 s
lemma mover (s:ℕ)(D:PlaqAxes)(h:D.val.1≠3)(p:D.val.2≠3)(k:ℕ)(u:Cover): takeoff P.par.block (tee P β s u D) 3 k= tee P β s (Shuttle.march u k P.par.block) D:=by
 funext N; change reflMark _ _ (reflMark _ _ _) = _; unfold tee choiceWeave; rw [local3 _ D h p,local3 _ D h p]; exact congrArg (fun i=> tee P β s i D N) (commute_f u k P.par.block)
lemma opposedT (s:ℕ)(D:PlaqAxes)(h:D.val.1≠3)(p:D.val.2≠3)(u:Cover): fluent 3 0 (tee P β s u D)=tee P β s (Shuttle.flip u) D:=funext fun _=>local3 _ D h p ..
private lemma staff_cert(D:PlaqAxes)(s:ℕ)(u:Cover)(r:ℕ): InTest P.calibration true (skyDeck (nodeC u) 12) false (staffWeight r • household P.calibration (tee P β s u D)):= .smul _ ((localStaff u 0 D).letterBudget (κFix β s) _ (temp (hat P.par.R.L P.par.x s)) (ready_local ..))
def ballotT (D:PlaqAxes)(s:ℕ)(u:Cover)(r:ℕ): P.Test:=P.art _ (aux_test (staff_cert P β D s u r))
local notation "W"=> P.calibration
lemma far_credit (D:PlaqAxes)(h:D.val.1≠3)(p:D.val.2≠3)(k:ℕ)(u:Cover)(r s:ℕ)(e:Tower.region 3 0 (W).ℓ (onFlight P.par.block (skyDeck (nodeC u) 12) 3 k)):
    let v:= Shuttle.march u k P.par.block
    (∫ x, ‖P.singleState 3 s x (ballotT P β D s u r)‖^2 ∂ (P.pillars 3)) ≤ ‖staffWeight r^2 * P.E s (household W (tee P β s (Shuttle.flip v) D * tee P β s v D))‖:=by
 intro v; let w:=staffWeight r; let f:=tee P β s v D; let l:=tee P β s u D; let t:= tee P β s (Shuttle.flip v) D; let T:=ballotT P β D s u r
 have hf(a: Weaver):household W (fluent 3 (0:ℤ) a)=mirror W 3 0 (household W a):=rfl
 have hp: (P.halfShift 3 k T).val = w • household W f := by
    rw [←show takeoff P.par.block l 3 k=f from mover P β s D h p k u]
    change mirror W _ _ (mirror W _ _ (w • household W l))=_; simp_rw [mirror_scale,star_star]; rfl
 refine le_trans (P.creditShelf 3 (staff_cert P β D s u r) s k e) ?_
 change ‖P.E s (mirror W _ _ ((P.halfShift 3 k T).val)* ((P.halfShift 3 k T).val))‖ ≤ _
 have he : star w=w:=by simp [w,staffWeight,star_mul,star_pow]; ring
 let I(s':ℕ)(u':Cover):= paidStaff P β s' 4 0 (localStaff u' 0 D) (ready_local ..)
 rw [hp,mirror_scale,he,Algebra.mul_smul_comm,Algebra.smul_mul_assoc,smul_smul,← pow_two,←hf,opposedT P β s D h p v,E_scale P.run P.large P.law _ ((I s (Shuttle.flip v)).mul (I s v))]
 rfl
variable {β P} {f:ℕ→ℕ}{u:ℕ→ Cover}{y:Gaia} {I:ℝ}
local notation "rr"=> zoomR P.par I
private lemma lift_shelter (B:Side)(k:ℕ)(c:ℕ)(x:Cover)(h:((c+12:ℕ):ℤ) ≤ nodeC (Shuttle.march x k B) 3): region 3 0 c (onFlight B (skyDeck (nodeC x) 12) 3 k):=by
 intro y hy
 let E:Cover:= (2* Heat.gaugeShift B k) • step 3
 change y∈(skyDeck (nodeC x) 12).image (fun i=>i+E) at hy
 obtain ⟨w,v,rfl⟩:=mem_image.mp hy
 have hi:=((pav_v (nodeC x) w 12).mp v 3).1
 rw [alignL] at h
 let Q:=(nodeC x) 3
 change ((c+12:ℕ):ℤ) ≤ Q + E 3 at h
 change (0:ℤ)+ ↑c≤w 3 + E 3; change Q-12 ≤ w 3 at hi
 push_cast at h
 -- use add_le_add instead omega
 calc _ = Q-12 + (((c:ℤ)+12) - Q) := by abel
      _ ≤ w 3 + E 3:=add_le_add hi (sub_le_iff_le_add'.mpr h)

lemma cover_shelter (p:0<I)(h:Appoint P.par I u y)(n:ℕ)(t:0< gait P.par y n 3):
    ∀ᶠ s:ℕ in atTop, region 3 0 (P.calibration).ℓ (onFlight P.par.block (skyDeck (nodeC (u s)) 12) 3 (kroll P.par I n s)):= by
 let v(s:ℕ):= Shuttle.march (u s) (kroll P.par I n s) P.par.block
 have he: Appoint P.par I v (gait P.par y n):= xplus_a p h n
 let c:= P.calibration.ℓ
 exact (xfront p he t (c+12)).mono fun s u=> lift_shelter P.par.block _ _ _ u
lemma staffPoll (pI:0<I)(D:PlaqAxes)(h:D.val.1≠3)(p:D.val.2≠3)(h₀:Appoint P.par I u y)
    (g:Pooling P.run (P.period ∘ P.projection.rows) (P.cutoff ∘ P.projection.columns) f β)(Q:P.PhysicalWakeGram):
    Spine.WakePoll P (fun s=> ballotT P β D s (u s) (rr s)) 0:=by
 let v(n s):= xplus P.par I (u s) n s; let a(n:ℕ): Gaia:=opposite (gait P.par y n) - gait P.par y n
 have hp:Tendsto (fun i=> ‖a i‖) atTop atTop:=(foreign P.par y y).congr (fun i=> dist_eq_norm ..)
 constructor; intro ε hz; let w(n:ℕ):= shotR 0 0 (X:=a n)* speckleV D D SU.group (a n)
 have hc:Tendsto (fun i=> ‖w i‖) atTop (𝓝 0):=by simpa only [w,norm_zero] using (decay_pair hp D D).norm
 obtain ⟨n,hn,v',u'⟩:= ((hc.eventually (gt_mem_nhds hz)).and (((gait_up P.par y).eventually_gt_atTop 0).and (hp.eventually_gt_atTop 0))).exists
 let W1(s):= Shuttle.flip (v n s)
 have hn':Tendsto (fun s=> riseX (rr s) (W1 s-v n s)) atTop (𝓝 (a n)):=by
    suffices he:∀ (t q:Cover)(s:ℕ), riseX (rr s) t - riseX (rr s) q=riseX (rr s) (t-q) by
       let t:=xplus_a pI h₀ n; exact (((appoint_as P.par pI _ _).mp (xflip_a t)).sub ((appoint_as P.par pI _ _).mp t)).congr (fun i=> he _ _ _)
    intro t q s; ext i; simp [riseX,moor,sub_div]
 have he:= norm_pos_iff.mp u'
 let F(s:ℕ):= twoStaff P β 4 rr (fun i=>localStaff (W1 i) 0 D) (fun i=>localStaff (v n i) 0 D) s
 have hx:Tendsto F atTop (𝓝 (w n)):= by
    obtain ⟨a',b,c⟩:= local_value I pI W1 (v n) hn' he 0 0 D D g Q
    have hx:= a'.add (b.mul c); rw [mul_zero,add_zero] at hx; exact hx.congr (fun s=>sub_add_cancel _ _)
 filter_upwards [cover_shelter pI h₀ n v',hx.norm.eventually (gt_mem_nhds hn)] with s K H
 simp only [sub_zero]; exact (far_credit P β D h p (kroll P.par I n s) (u s) (rr s) s K).trans_lt H

#check @Spine.creditShelf
#check @staffPoll
#print axioms staffPoll
end GramSignal
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
