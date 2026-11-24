import YM.SU5.SatinWard.Resolution.RadianMesh
import YM.SU5.SatinWard.Resolution.IslandU
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.MeshClock
open Function Set Filter Metric Finset
open scoped Topology NNReal
namespace Carousel
variable (M: Mesh) {α y C:ℝ} {X I:Type*} [NormedAddCommGroup X][NormedSpace ℝ X][Fintype I][DecidableEq I][CompleteSpace X]
variable (p:0<α)(e:α<1) {f:(I→ℝ)→X} (K: Spark M (realLn M) C f α) (hc:Continuous f)
local notation "σ" v:max=> (mill M v:ℝ)
local notation "Λ"=> (M.L:ℝ)
local notation "σρ" i:max v:max=> realLn M i v
local notation "δ" i:max t:max=> axisLn i t
variable (x:I→ℝ)(i:I)
lemma axis_cont (x:I→ℝ)(i:I): Continuous (fun t:ℝ=> x+axisLn i t):=by
 refine continuous_pi (fun a=>?_); by_cases e:a=i <;> simp [axisLn,e,continuous_const_add,continuous_const]
lemma axis_plus (u v:ℝ): δ i (u+v)=axisLn i u+axisLn i v:=Pi.single_add i _ _
local notation "D" i:max => gradPrice (f:=f) M (realLn M) i
noncomputable abbrev slopeJump (i:I)(v:ℕ)(x:I→ℝ):= boltDiff M (realLn M) i v f x
lemma memo_cont(v:ℕ)(h:Continuous f):Continuous (boltDiff M (realLn M) i v f):= (Continuous.sub (h.comp (continuous_id.add continuous_const)) h).const_smul _
include hc p K
lemma lights_up :TendstoUniformly (fun v:ℕ=> boltDiff M (realLn M) i v f) (D i) atTop := by
 refine Metric.tendstoUniformly_iff.mpr fun r u=>?_
 have he:Tendsto (fun v:ℕ=> (σ v)^α) atTop (𝓝 0):=by convert! (gears M).rpow (tendsto_const_nhds (x:=α)) (Or.inr p); rw [Real.zero_rpow p.ne']
 have hp:Tendsto (fun v:ℕ=> C*roseMax M α* (σ v)^α) atTop (𝓝 0):=by simpa using he.const_mul (C*roseMax M α)
 filter_upwards [hp.eventually (gt_mem_nhds u)] with v h x; rw [dist_eq_norm]; exact (quorum M (realLn M) C p (realpaid M) K i x v).2.trans_lt h
lemma grad_cont : Continuous (gradPrice (f:=f) M (realLn M) i):=(lights_up M p K hc i).continuous ((Eventually.of_forall (fun n=> memo_cont M i n hc)).frequently) -- syntax tune
include e
noncomputable abbrev gateLand (M:Mesh)(α:ℝ):ℝ:=2*(expense M α)*((mill M 0:ℝ)^α)⁻¹+roseMax M α*κK M α
omit hc K in
lemma land_nonneg:0≤gateLand M α:=by unfold gateLand; have h:=expense_pos M p; have hp:= rosePos M p; have hq:=gear_pos M 0; have hv:= κK_pos M p e; positivity
local notation "fee"=> C*gateLand M α
lemma grad_scale (x:I→ℝ)(j:I)(y:ℝ): ‖(D i) (x+ axisLn j y)-(D i) x‖ ≤ (fee) * |y|^α:=by
 let f:=gradPrice (f:=f) M (realLn M) i; let d:= fun t:ℝ=> f (x+axisLn j t); have h0:0≤ C:=K.pos; let V:= C*κK M α; have hv : 0 ≤ V:=mul_nonneg h0 (κK_pos M p e).le
 have ht (v:ℕ)(t:ℝ): ‖d (t+(mill M v:ℝ))-d t‖ ≤ V*(σ v)^α:=by
    unfold d f; rw [axis_plus,←add_assoc]; exact at_spiral M _ _ p e (realpaid M) K i j _ v
 have e:=polar_arc M p ((grad_cont M p K hc i).comp (axis_cont x j)) hv (fun x n=> ht n x) (fun v=>(overhead M (realLn M) C p (realpaid M) K i (x+axisLn j v) 0).1) y 0 -- binder hc f conflict. 
 have hx:d 0=f x:=by simp [d,axisLn]
 change ‖d y-f x‖≤ _; change ‖d (0+y)-d 0‖≤ _ at e; rw [hx,zero_add] at e; refine e.trans_eq ?_; unfold V gateLand; ring
lemma gather (x y:I→ℝ):‖(D i) x-(D i) y‖≤ Fintype.card I*(fee)*‖x-y‖^α:=by
 let w:= x-y; let s (j):=axisLn j (w j)
 have hx:x=y+∑ i:I,s i:=by
    ext j; unfold s; rw [Pi.add_apply,Finset.sum_apply,sum_eq_single j] ; · unfold axisLn; rw [Pi.single_eq_same]; unfold w; simp
    · intro i _ a; exact Pi.single_eq_of_ne (Ne.symm a) _
    simp
 nth_rw 1 [hx]; refine (accumulation _ _ s univ (C:= (fee)*‖w‖^α) (fun i' _ x=>?_)).trans_eq (by unfold w; rw [←mul_assoc]; rfl)
 refine (grad_scale M p e K hc i x i' (w i')).trans ?_; exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) ((Real.norm_eq_abs (w i')).symm.trans_le (norm_le_pi_norm w _)) p.le) (mul_nonneg K.pos (land_nonneg M p e))
lemma cruise (x:I→ℝ)(n:ℕ)(p':0 ≤ y): ‖f (x+ axisLn i (arcTick M n y))-f x- (arcTick M n y) • (gradPrice (f:=f) M (realLn M) i x)‖ ≤ y*(C*roseMax M α*(mill M n:ℝ)^α+(fee) * y^α):=by
 let s:=σ n; let T:= C* roseMax M α * s^α ; let U:= C*gateLand M α; let v:=(D i) x; let w(m:ℕ): ℝ:= m*s; let Z:=T+U*y^α; have hZ:0≤Z:=add_nonneg (by have hx:=K.pos; have ht:=rosePos M p; have hp:0 < s:= gear_pos ..; unfold T; positivity) (mul_nonneg (mul_nonneg K.pos (land_nonneg M p e)) (Real.rpow_nonneg p' _))
 let A:=arcStage M n y; have ht:w A ≤ y:=(arc_price M p' n).1; let u:=σρ i n; have hs0:0<s:=gear_pos M n; let F(m:ℕ):= x+m • u
 have hz(m): x+ axisLn i (w m) =F m:=by unfold F w; rw [show (m:ℝ)*s=m • s from (nsmul_eq_mul m s).symm]; unfold axisLn; rw [Pi.single_smul']; rfl
 have h(m:ℕ)(d:m ≤ A): ‖f (F m)-f x-(w m) • v‖≤ w m * Z:=by
    induction m with
    | zero => simp [F,w]
    | succ m ih=>
       let θ:=(D i) (F m); let y':= F (m+1); let T':= boltDiff M (realLn M) i n f (F m)
       let hx:‖T'-v‖ ≤ Z:=by
         refine (norm_sub_le_norm_sub_add_norm_sub _ θ _).trans (add_le_add ?_ ?_); rw [norm_sub_rev]; exact (quorum M (realLn M) C p (realpaid M) K i _ _).2 -- q binder e lean grouping rw at both goals? tactic block
         have hw:‖θ-v‖ ≤ (fee) * |(w m)|^α:= by unfold θ; rw [←hz]; exact grad_scale M p e K hc i x i (w m)
         apply le_trans hw (?_); apply mul_le_mul_of_nonneg_left ?_ (mul_nonneg K.pos (land_nonneg M p e)); have h':0 ≤ w m:=by unfold w; positivity
         apply Real.rpow_le_rpow (abs_nonneg _) _ p.le; rw [abs_of_nonneg h']; exact le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.le_trans (Nat.le_succ _) d)) hs0.le) ht
       let e':= F m; have hv:f y'-f (F m)=s • T':=by unfold T' boltDiff; rw [Pi.smul_apply, smul_inv_smul₀ (gear_pos M n).ne']; unfold y' stroll F; rw [succ_nsmul,←add_assoc]
       have hp:w (m+1)=w m+s:=by unfold w; push_cast; ring
       have ht:f y'- f x-w (m+1) • v= s • (T'-v)+(f (F m)- f x-w m • v):=by rw [hp,smul_sub, ←hv]; module
       change ‖f y'-_ - _‖ ≤ _; rw [ht,hp]; refine (norm_add_le ..).trans ?_; rw [norm_smul,Real.norm_of_nonneg hs0.le]; exact (add_le_add (mul_le_mul_of_nonneg_left hx hs0.le) (ih (Nat.le_trans (Nat.le_succ _) d))).trans_eq (by ring)
 rw [show arcTick M n y=w A from rfl,hz]; exact (h A (le_refl A)).trans (mul_le_mul_of_nonneg_right ht hZ)
lemma slum (x:I→ℝ)(p': 0 ≤ y): ‖f (x+ axisLn i y)-f x- y • (D i) x‖ ≤ (fee)*y*y^α:=by
 let T:= C*(roseMax M α); let A:= C*gateLand M α; let h:=arc_pass M p'; have hu:Tendsto (fun n:ℕ=> (mill M n:ℝ)^α) atTop (𝓝 0):=by convert! (gears M).rpow (tendsto_const_nhds (x:=α)) (Or.inr p); rw [Real.zero_rpow p.ne']
 let F(t:ℝ):= ‖f (x+ axisLn i t)-f x-t • (D i) x‖; let W(n:ℕ):=y*(T*(σ n)^α+A*y^α); have hv:Tendsto W atTop (𝓝 (A*y*y^α)):=by
    rw [show A*y*y^α=y*(T*0+A*y^α) from (by ring)]; exact ((hu.const_mul T).add_const (A*y^α)).const_mul y
 change F y≤_; exact le_of_tendsto_of_tendsto ((show Continuous F from (by unfold F; exact (((hc.comp (axis_cont x i)).sub continuous_const).sub (continuous_id.smul continuous_const)).norm)).continuousAt.tendsto |>.comp h) hv (Eventually.of_forall fun n=> cruise M p e K hc i x n p') -- arguments tune
lemma cadence(x:I→ℝ)(y:ℝ): ‖f (x+axisLn i y)-f x-y • (D i) x‖ ≤ (2*C*gateLand M α) * |y|  * |y|^α:=by
 by_cases h:0≤y; · rw [abs_of_nonneg h]; apply le_trans (slum M p e K hc i x h); linarith only [mul_nonneg (mul_nonneg (mul_nonneg K.pos (land_nonneg M p e)) h) (Real.rpow_nonneg h α)]
 let z:= x+axisLn i y; let w:= -y; have hv:y≤0:=le_of_not_ge h; have hx:z+axisLn i w=x:=by unfold z w; rw [add_assoc,← axis_plus]; simp [axisLn]; --
 have hp:‖f x - f z- w • (D i) z‖≤ (fee)*w*w^α:= hx ▸ slum M p e K hc i z (by linarith only [hv] : (0:ℝ) ≤ -y)
 have hq:‖(D i) z-(D i) x‖≤ (fee)*w^α:= (grad_scale M p e K hc i x i y).trans_eq (by rw [abs_of_nonpos hv]); rw [abs_of_nonpos hv]; let d:=D i; change ‖f z-f x-y • d x‖ ≤ 2*C*_*w*w^α
 rw [show f z-f x-y • d x= -(f x-f z-w • d z)-w • (d z-d x) from (by unfold w; module)] -- sign check: -(fx-fz -w dz)-w(dz-dx)= fz-fx+w dx. ok.
 refine (norm_sub_le ..).trans ?_; rw [norm_neg,norm_smul,Real.norm_of_nonneg (show 0≤ w from neg_nonneg.mpr hv)]; nlinarith only [hp,mul_le_mul_of_nonneg_left hq (neg_nonneg.mpr hv)]
#print axioms gather
#print axioms cadence
end Carousel
end YM.CF.Buffered.Afterglow.Tower.MeshClock
