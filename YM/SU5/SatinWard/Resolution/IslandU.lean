import YM.SU5.SatinWard.Resolution.CanvasAr
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.MeshClock
open Function Set Filter Metric
open scoped Topology NNReal
namespace Carousel
variable (M: Mesh) {α:ℝ} {X G I:Type*} [NormedAddCommGroup X][NormedSpace ℝ X][AddCommGroup G][Fintype I][DecidableEq I]
local notation "Ξ"=> I → marks M
local notation "Θ"=> I → ℝ
local notation "Γj"=> (marks M)
noncomputable def liftP (I:Type*) (x:I→ marks M): I→ ℝ:= fun i=> (x i).val
local notation "P" => liftP M I
lemma mark_z(n:ℕ):bell M n 1= (mill M n:ℝ):=by simp [bell]
lemma scale_notch(n:ℕ)(z:ℤ) : notch M n z= z • notch M n 1:=by apply Subtype.ext; rw [AddSubgroup.coe_zsmul]; change bell M n z=z • bell M n 1; rw [mark_z,zsmul_eq_mul]; rfl
noncomputable def propLn(i:I)(n:ℕ): (I→ marks M):=Pi.single i (notch M n 1)
noncomputable abbrev axisLn(i:I)(x:ℝ): I→ℝ:= Pi.single i x
noncomputable def realLn(i:I)(n:ℕ): I→ℝ:= axisLn i (mill M n)
lemma liftp_add(x y: I→ marks M) : P (x+y)=P x + P y:=rfl
lemma liftp_sub(x y: I→ marks M) : P (x-y)=P x-P y:=rfl
lemma liftp_ln(v:ℕ)(i:I): liftP M I (propLn M i v)=realLn M i v :=by ext j; change ((propLn M i v j):ℝ)=_; unfold propLn realLn; by_cases h:j=i<;> simp [axisLn,h]; exact mark_z ..
lemma liftp_iso : Isometry (liftP M I):=by
 intro x y; simp only [edist_pi_def]; rfl
lemma liftp_dense : DenseRange (liftP M I):=by
 intro x
 choose f hf using fun i:I=> (mem_closure_iff_seq_limit.mp ((daylight M) (x i))) -- f:ℕ→ G or ℝ mem combos
 let Y:ℕ→ (I→ marks M):= fun n i=>⟨f i n,(hf i).1 n⟩
 have p:Tendsto (fun n=>P (Y n)) atTop (𝓝 x):=tendsto_pi_nhds.mpr (fun i=>(hf i).2)
 exact mem_closure_of_tendsto p (Eventually.of_forall fun i=>Set.mem_range_self _)
lemma liftp_visible : IsDenseInducing (liftP M I):= (liftp_iso (I:=I) M).isUniformInducing.isDenseInducing (liftp_dense M)
local notation "σ" h:max=> (mill M h:ℝ)
lemma realpaid : PaidR M (realLn (I:=I) M):=by
 intro i v; unfold realLn axisLn; rw [← Pi.single_smul', nsmul_eq_mul,←speedup] -- check
lemma markpaid : PaidR M (propLn (I:=I) M):=by
 let V: (I→ marks M) →+ (I→ℝ):=⟨⟨liftP M I,rfl⟩,liftp_add M⟩ -- structure syntax
 intro i h; apply (liftp_iso M).injective; change V (M.L • propLn M i (h+1))= V _; rw [map_nsmul, show V (propLn M i (h+1))=_ from liftp_ln M _ i, show V (propLn M i h)=_ from liftp_ln M _ i]; exact realpaid ..
variable {f:(I→marks M)→X}[CompleteSpace X] (C:ℝ)(p:0<α)(K:Spark M (propLn (I:=I) M) C f α)
lemma step_ticket {C:ℝ}{f:G→X}(u:G)(n:ℤ)(h:∀x,‖f (x+u)-f x‖≤C)(x:G): ‖f (x+n • u)-f x‖≤ |(n:ℝ)| *C:=by
 by_cases p:0≤ n; · obtain ⟨b,rfl⟩:= Int.eq_ofNat_of_zero_le p; simpa using creep C f x u h b
 have u':0≤ -n:= by omega
 obtain ⟨b,hb⟩:=Int.eq_ofNat_of_zero_le u'; rw [show n=-(b:ℤ) from ?_, norm_sub_rev]; swap; · exact neg_eq_iff_eq_neg.mp hb
 let z:= x+ (-(b:ℤ)) • u; have hx:z+b • u=x:=by unfold z; simp
 change ‖f x-f z‖≤ _; have h:=creep C f z u h b; rw [hx] at h; simpa using h
lemma accumulation {C:ℝ}{X I G:Type*}[NormedAddCommGroup X][AddCommGroup G](x:G)(f:G→X)(u:I→G)(A:Finset I)(h:∀ i∈A,∀ x,‖f (x+u i)-f x‖≤ C) : ‖f (x+(∑ i∈A,u i))-f x‖≤ A.card*C:=by
 classical
 induction A using Finset.induction_on with
 | empty=>simp
 | insert i A t ih=> rw [Finset.card_insert_of_notMem t,Finset.sum_insert t,add_comm (u i),←add_assoc]; exact (norm_sub_le_norm_sub_add_norm_sub _ (f (x+∑ i∈A,u i)) _).trans ((add_le_add (h _ (Finset.mem_insert_self ..) _) (ih fun i v=> h i (Finset.mem_insert_of_mem v))).trans_eq (by push_cast; ring))
local notation "fmax" => expense M α
include K p
lemma slip(i:I)(t:ℕ)(x: I→ marks M)(g:ℤ) : ‖f (x+g • propLn M i t)-f x‖ ≤ |bell M t g| *(C*expense M α):=by
 have hx:0<σ t:= gear_pos ..
 have he(x): ‖f (x+propLn M i t)-f x‖ ≤ σ t*(C*fmax):=by
    rw [show f (x+propLn M i t)-f x=(σ t) • boltDiff M (propLn M) i t f x from (smul_inv_smul₀ hx.ne' _).symm,norm_smul,Real.norm_eq_abs,abs_of_pos hx]; exact mul_le_mul_of_nonneg_left (overhead M (propLn M) C p (markpaid M) K i x t).2 hx.le
 refine (step_ticket (propLn M i t) g he x).trans_eq ?_; rw [show bell M t g=(g:ℝ)*(mill M t:ℝ) from rfl,abs_mul,abs_of_pos hx,mul_assoc]
abbrev berth (I:Type*)[Fintype I](α C:ℝ):ℝ:= Fintype.card I*(C*expense M α)
local notation "K✧"=> berth M I α C
lemma island_lip (x y:I→marks M): ‖f x-f y‖≤ berth M I α C*‖x-y‖:=by
 let S:=(marks M)
 choose x' r g using fun i:I=> notch_exists M (x i-y i); let B:=fun i:I=> (r i) • propLn M i (x' i) -- shadow!! tune
 let T:=‖x-y‖ * (C*expense M α); have ht: x=y+∑ i:I,B i:=by
    funext i
    rw [Pi.add_apply,Finset.sum_apply,Finset.sum_eq_single i]; swap; · intro j _ h; simp [B,propLn,Ne.symm h]
    swap; · simp
    unfold B propLn; rw [Pi.smul_apply,Pi.single_eq_same, ← scale_notch M (x' i) (r i),g i]; abel
 have hx (i:I)(z):‖f (z+B i)-f z‖≤ T:=by
    refine (slip M C p K i _ z _).trans ?_; apply mul_le_mul_of_nonneg_right ?_ (mul_nonneg K.pos (expense_pos M p).le); rw [show |bell M (x' i) (r i)|= ‖notch M (x' i) (r i)‖ from (Real.norm_eq_abs _).symm, g i]; exact norm_le_pi_norm (x-y) i -- hp
 refine le_trans (?_ : ‖f x-f y‖ ≤ (Fintype.card I:ℝ)*T) (le_of_eq (by unfold T berth; ring)); nth_rw 1 [ht]; exact accumulation _ _ _ Finset.univ (fun i _=> hx i)
-- produce extension all space. with quantitative continuity inherited for all l≥ money as functions (before and after compression).
lemma wallP : UniformContinuous f:= by
 have h : LipschitzWith (Real.toNNReal (berth M I α C)) f:= LipschitzWith.of_dist_le_mul (by intro x y; rw [dist_eq_norm,dist_eq_norm,Real.coe_toNNReal _ (show 0≤berth M I α C from mul_nonneg (by positivity) (mul_nonneg K.pos (expense_pos M p).le))]; exact island_lip M C p K x y)
 exact h.uniformContinuous
noncomputable abbrev sphereEm (f:(I→marks M)→X): (I→ℝ)→X:= IsDenseInducing.extend (liftp_visible M) f
lemma extendSphere : UniformContinuous (sphereEm M f)∧(∀x:I→marks M,sphereEm M f (P x)=f x):=⟨uniformContinuous_uniformly_extend (liftp_iso M).isUniformInducing (liftp_dense M) (wallP M C p K),fun _=> (liftp_visible M).extend_eq (wallP M C p K).continuous _⟩
lemma lightSphere : Spark M (realLn (I:=I) M) C (sphereEm M f) α:=by
 let V:= sphereEm M f; obtain ⟨h,v⟩:= extendSphere M C p K; have hx:Continuous V:=h.continuous; let p':= liftp_dense (I:=I) M
 refine ⟨K.pos,fun x=>?_,fun x i w=>?_⟩
 · refine p'.induction_on x ?_ (fun y=> (by change ‖V (P y)‖≤_; rw [show V (P y)=_ from v y]; exact K.norms y)); exact isClosed_le hx.norm continuous_const
 refine p'.induction_on x (isClosed_le (((hx.comp (continuous_id.add continuous_const)).add (hx.comp (continuous_id.sub continuous_const))).sub (hx.const_smul _)).norm continuous_const) (fun y=>?_)
 rw [←liftp_ln, ←liftp_add, ←liftp_sub,v,v,v]; exact K.laps ..
#print axioms lightSphere
end Carousel
end YM.CF.Buffered.Afterglow.Tower.MeshClock
