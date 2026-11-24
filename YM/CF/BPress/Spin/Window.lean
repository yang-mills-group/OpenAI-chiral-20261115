import YM.CF.BPress.Spin.Pledge
import YM.CF.Lattice.Tenant
/-! Spatial localization (in eq:B-Cpass and lem:Lspeed). Common power estimate variant
 using **output row** partitions. Instead of C/w commutator proof, use its costs via concrete
 finite-range truncation including field reads, and lift margin via counting enlarged boxes.
 Works at arbitrarily small targets with arbitrarily small relative/margin loss. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Spin
open Function Filter Finset Fock Branch NormedSpace Lattice Tenant Pledge
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators
attribute [local instance] opCStarAlgebra
namespace Eye
variable {N:Side} {w k :ℕ}
lemma volume (x: Site N)(h:2*w<N.val): (bay (terr N) x w).card=(w+w+1)^4:=by
 apply le_antisymm
 · rw [tract]; exact (Corona.halo_size ..).trans (by simp)
 let f := fun y:Cover=> x+wrap N y; have hr : (box w).image f ⊆ bay (terr N) x w:=by
    intro y h; obtain ⟨z,g,rfl⟩:= mem_image.mp h; unfold f; rw [bay_mem]; change separation _ _ ≤ _; rw [separation_comm,separation,add_sub_cancel_left]; apply Finset.sup_le; intro j _; exact (Corona.lap ..).trans (by have hp:= (box_test.mp g).1 j; have ht:=(box_test.mp g).2 j; omega)
 have he {x: Cover}(p:x∈box w) (i:Axis): -(N.val:ℤ)< 2*x i ∧ 2*x i≤N.val:=by have hp:= (box_test.mp p).1 i; have ht:=(box_test.mp p).2 i; omega
 rw [← Corona.box_size,← card_image_of_injOn (f:=f) (s:=box w) (fun _ p _ q H=>wrap_injOn N (he p) (he q) (add_left_cancel H))]; exact card_le_card hr

variable {I D : Type*}[Fintype I][DecidableEq I]
def look (u:I→ Site N)(X:Support N): Op I:= cutM (univ.filter fun i=>u i∈X)
lemma look_left (u:I→Site N)(X:Support N)(A:Op I)(i j:I): (look u X*A) i j=if u i∈X then A i j else 0:=by rw [look,cutM,Matrix.diagonal_mul]; by_cases h:u i∈X <;> simp [h]
lemma look_right (u:I→Site N)(X:Support N)(A:Op I)(i j:I): (A*look u X) i j=if u j∈X then A i j else 0:=by rw [look,cutM,Matrix.mul_diagonal]; by_cases h:u j∈X <;> simp [h]
lemma look_one (u:I→Site N)(X:Support N):‖look u X‖≤1:= IsStarProjection.norm_le _ (cutM_idp _)
def ν(w:ℕ):ℝ:=2*w+1 -- coercion of w
lemma vol_pos : 0<ν w:=by unfold ν; positivity
variable {b : Stage (Site N) I D Empty} {u:I → Site N}{A: Op I}
def eye (u:I→ Site N)(x:Site N)(w:ℕ): Op I:= look u (bay (terr N) x w)
lemma esteem (v:Ket I)(u:I→ Site N)(h:2*w<N.val) : ∑ x:Site N, ‖acts (eye u x w) v‖^2=ν w^4*‖v‖^2:=by
 have he i : #{x:Site N | u i∈ bay (terr N) x w}=(w+w+1)^4:= Eq.trans (congrArg Finset.card (show (univ.filter fun x=> u i∈bay (terr N) x w)=bay (terr N) (u i) w from by ext x; simp [bay,(terr N).sym (u i)])) (volume (u i) h)
 simp_rw [EuclideanSpace.norm_sq_eq,eye,look,cut_apply]; rw [sum_comm,mul_sum]; refine sum_congr rfl (fun i _=>?_); simp only [mem_filter,mem_univ,true_and,apply_ite,norm_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,ite_pow,one_pow]; rw [←sum_filter,sum_const,he,nsmul_eq_mul]; unfold ν; push_cast; ring
lemma house (e:b.F= terr N)(p: FiniteOp b k A)(X:Site N): eye b.home X w*A*eye b.home X (w+k)=eye b.home X w*A:=by
 ext i j; unfold eye; rw [look_right, look_left]; by_cases h:b.home i∈ bay (terr N) X w -- metavariable
 · by_cases t:b.home j∈bay (terr N) X (w+k); simpa [t]; have hx:k< b.F.span (b.home i) (b.home j):=by rw [e]; exact lt_of_not_ge fun z=>t (bay_mem _ |>.mpr (((terr N).tri X (b.home i) (b.home j)).trans (Nat.add_le_add ((bay_mem _).mp h) z)))
   rw [p i j hx]; simp
 simp [h]
lemma norm_act (A:Op I)(v:Ket I): ‖acts A v‖≤‖A‖*‖v‖:=by rw [← Matrix.l2_opNorm_toEuclideanCLM]; exact ContinuousLinearMap.le_opNorm ..
variable {a r δ :ℝ}
-- margin lift via sqrt operation-free estimate.
lemma boundA (h:FiniteOp b k A)(e:b.F=terr _)(s: 2*(w+k)< N.val)(p:0≤a)(q:0≤r)(kA: a*ν (w+k)^2 ≤ r*ν w^2)(uA:∀ x, ‖eye b.home x w*A‖≤a) : ‖A‖≤r:=by
 rw [← Matrix.l2_opNorm_toEuclideanCLM]; apply ContinuousLinearMap.opNorm_le_bound _ q; intro v
 let χ:=eye b.home
 apply (sq_le_sq₀ (norm_nonneg (acts A v)) (by positivity)).1
 have he (x:Site N): ‖acts (χ x w) (acts A v)‖ ≤ a*‖acts (χ x (w+k)) v‖:=by
    rw [←act_mul]; nth_rw 1 [←house e h x]; rw [act_mul]; exact (norm_act ..).trans (mul_le_mul_of_nonneg_right (uA _) (norm_nonneg _)) -- tune nthrw
 have ht: ν w^4*‖acts A v‖^2 ≤ ν w^4*(r*‖v‖)^2:=calc
    _ ≤ ∑ x:Site N,(a*‖acts (χ x (w+k)) v‖)^2 := by rw [←esteem _ b.home (by omega)]; exact sum_le_sum (fun i _=> pow_le_pow_left₀ (norm_nonneg _) (he i) _)
    _ = (a*ν (w+k)^2)^2*‖v‖^2:= by unfold χ; simp_rw [mul_pow a,←mul_sum, esteem v b.home s]; ring -- tune
    _ ≤ _:= (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) kA 2) (sq_nonneg _)).trans_eq (by ring)
 exact le_of_mul_le_mul_left ht (pow_pos vol_pos _)

-- numeric growth budget
lemma priceν (p:0≤a)(h:a<r)(k:ℕ): ∀ᶠ w:ℕ in atTop,a*ν (w+k)^2≤r*ν w^2:=by
 have hx:Tendsto (fun w:ℕ=> (ν w)⁻¹) atTop (𝓝 0):= tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 ((tendsto_natCast_atTop_atTop (R:=ℝ)).const_mul_atTop (by norm_num : (0:ℝ)<2)))
 let f(w:ℕ):= 1+(2*(k:ℝ))*(ν w)⁻¹; have ht: Tendsto f atTop (𝓝 1):=by have he:= (hx.const_mul (2*(k:ℝ))).const_add 1; simpa only [mul_zero,add_zero] using he -- comp ν def
 have he:Tendsto (fun w:ℕ=> a*f w^2) atTop (𝓝 a):=by simpa using ((ht.pow 2).const_mul a)
 filter_upwards [he.eventually (ge_mem_nhds h)] with w v; have ho:0<ν w:=vol_pos; have hp:ν (w+k) = f w*ν w:=by unfold f; rw [add_mul,one_mul,mul_assoc _ ((ν w)⁻¹),inv_mul_cancel₀ ho.ne',mul_one]; unfold ν; push_cast; ring
 rw [hp,mul_pow,←mul_assoc]; exact mul_le_mul_of_nonneg_right v (sq_nonneg _)
variable {P:Pledge}
lemma tailBuys (P:Pledge)(h:0<δ): ∀ᶠ k:ℕ in atTop, Real.exp (-P.rate/2*k)*P.price≤δ:=by
 have he:Tendsto (fun k:ℕ=> (-P.rate/2)*(k:ℝ)) atTop atBot:= (tendsto_natCast_atTop_atTop (R:=ℝ)).const_mul_atTop_of_neg (div_neg_of_neg_of_pos (neg_lt_zero.mpr P.pos) (by norm_num)) -- check
 have hx:= (Real.tendsto_exp_atBot.comp he).mul_const P.price; rw [zero_mul] at hx; exact hx.eventually (ge_mem_nhds h)

/-- Sufficient volume increases; margin `r-a` independent. Includes budget at arbitrarily large windows in this lemma. -/
lemma pledge_lift (P:Pledge)(p:0≤a)(q:a<r): ∀ᶠ w:ℕ in atTop, ∃ m:ℕ,∀N:Side,m≤N.val→∀{I D:Type}[TopologicalSpace D][Fintype I][DecidableEq I]{b:Stage (Site N) I D Empty}, b.F=terr N →∀ f:Raw D I,P.Costs b f→ ∀ x:D, (∀ z:Site N,‖eye b.home z w*f x‖≤a) → ‖f x‖≤r:=by
 let δ := (r-a)/4; have hd:0<δ:=div_pos (sub_pos.mpr q) (by norm_num); obtain ⟨k,h⟩:= (tailBuys P hd).exists
 have he:a+δ< r-δ:=by unfold δ; linarith
 filter_upwards [priceν (add_nonneg p hd.le) he k] with w t
 refine ⟨2*(w+k)+1,?_⟩; intro N L I D _ _ _ b e f C x X
 obtain ⟨F,K,pF,uF,gF⟩:= C
 let A:=lop F k x; let B:= f x-A; have hp: ‖B‖≤δ:= ((lip_tail F K pF uF gF P.pos.le).boundOp (half_pos P.pos).le x).trans h
 have hx : ‖A‖ ≤ r-δ:=by
    refine boundA (lop_rad F K pF x) e L (add_nonneg p hd.le) ((add_nonneg p hd.le).trans he.le) t ?_; intro z
    let G:= eye b.home z w; rw [show A=f x-B from (sub_sub_cancel ..).symm,mul_sub]; apply (norm_sub_le ..).trans; exact add_le_add (X _) ((norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg B) (look_one b.home _)).trans hp)) -- tune
 have hv: f x=A+B:= by unfold B; abel
 nth_rw 1 [hv]; exact (norm_add_le ..).trans ((add_le_add hx hp).trans_eq (sub_add_cancel ..))
end Eye
end YM.CF.BPress.Spin
