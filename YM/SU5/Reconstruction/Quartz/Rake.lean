import YM.SU5.Reconstruction.Quartz.Shimmer
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.Quartz
open Function Set Filter MeasureTheory Spectral Analysis Metric
open scoped Topology NNReal ENNReal Complex ComplexOrder InnerProductSpace
open Multiplier CrossedFrame Clasp Complex HadamardThreeLines
variable {K H D:Hilbert}(C:Clasp K H D)(n:ℕ)
local notation "S"=> spectrum ℂ C.angle
local notation "Q"=> glacier C n
local notation "R"=> Quartz.rise C n
local notation "L" i:max=> C.Left.symm.conjStarAlgEquiv i
local notation "B" i:max=> C.Right.symm.conjStarAlgEquiv i
variable (X:H.Op)(Y:D.Op)(k:K.Op)
local notation "T"=>twinkle C n (L X)
lemma blink (z:ℂ)(p:|z.re|≤1): ‖rise C n z‖≤ Real.exp n:= by
 refine (rising C n z).fare (Real.exp_pos _).le (fun x=>?_)
 simp only[rise_tag,norm_exp,mul_re,div_ofNat_re,ofReal_re,ofReal_im,mul_zero,sub_zero]; apply Real.exp_le_exp.mpr
 have ht:z.re * height C n x ≤ (n:ℝ):= (le_abs_self _).trans (Eq.trans_le (abs_mul _ _) ((mul_le_mul p (height_edge C n x) (by positivity) (by positivity)).trans_eq (by rw[one_mul])))
 linarith
lemma flammable (s:K.Op) (e:Pays s):‖s‖≤1:= ContinuousLinearMap.opNorm_le_bound s zero_le_one (fun x=> (show ‖s x‖=1*‖x‖ by rw [one_mul,@norm_eq_sqrt_re_inner ℂ,@norm_eq_sqrt_re_inner ℂ,e.ordinary]).le)
lemma confined (z:ℂ):DifferentiableAt ℂ (twinkle C n k) z:= by unfold twinkle; exact ((((rise_analytic C n _).mul_const Q).mul_const k).mul_const Q).mul ((rise_analytic C n _).comp z (differentiableAt_id.neg))
lemma neither (k u s:K.Op)(v:‖u‖≤1)(e:‖s‖≤1): ‖u*(s*k*star s)*u‖≤ ‖k‖:=calc
 _≤ (‖u‖*((‖s‖*‖k‖)*‖star s‖))*‖u‖:=by apply (norm_mul_le ..).trans; gcongr <;> refine (norm_mul_le ..).trans ?_ <;> gcongr <;> refine (norm_mul_le ..).trans ?_ <;> gcongr <;> exact norm_mul_le .. -- tune
 _ ≤ ‖k‖:= by rw [norm_star]; nth_rw 2 [show ‖k‖= (1*((1*‖k‖)*1))*1 by ring]; gcongr -- tune
lemma max_blink (h:C.Pass X Y)(M:ℝ)(b:‖L X‖ ≤ M)(v:‖B Y‖≤ M)(z:ℂ)(t:z∈ verticalClosedStrip 0 1):‖twinkle C n (L X) z‖≤ M:= by
 unfold twinkle -- refold
 change ‖T z‖≤ M
 have hc: ∀ u:ℂ,u.re=0→ ‖T u‖≤ M:=fun u p=>by
    rw [show u= (u.im:ℂ)*I from Complex.ext (by simp [p]) (by simp),spark]; exact (neither _ _ _ (glacier_safe C n) (flammable _ (C.Cabin_pays _))).trans b
 have hq: ∀ u:ℂ,u.re=1→ ‖T u‖≤ M:=fun u p=>by
    rw [show u= 1+(u.im:ℂ)*I from Complex.ext (by simp [p]) (by simp),summit _ _ _ _ _ h]; exact (neither _ _ _ (glacier_safe C n) (flammable _ (C.Cabin_pays _))).trans v
 have e:= norm_le_interp_of_mem_verticalClosedStrip₀₁' T t ⟨fun x _=>(confined ..).differentiableWithinAt,fun x _=>(confined ..).continuousAt.continuousWithinAt⟩ ?_ hc hq; swap
 · refine ⟨(Real.exp n *‖Q‖*‖L X‖*‖Q‖)*Real.exp n, ?_⟩; rintro _ ⟨x,p,rfl⟩; change ‖R _*Q* (L X)*Q*R (-x)‖≤_
   obtain ⟨u,w⟩:= (show x.re∈Icc (0:ℝ) 1 from p); have H': |x.re|≤1:=by rwa [abs_of_nonneg u]
   have hv: |(-x).re|≤1:=by simpa using H'
   apply (norm_mul_le ..).trans; have e:‖R x*Q*L X‖≤_:=(norm_mul_le ..).trans (mul_le_mul_of_nonneg_right ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (blink C n x H') (norm_nonneg _))) (norm_nonneg _)); gcongr
   · exact (norm_mul_le ..).trans (mul_le_mul_of_nonneg_right e (norm_nonneg _))
   exact blink _ _ _ hv
 rw [←Real.rpow_add_of_nonneg ((norm_nonneg _).trans b) (sub_nonneg.mpr t.2) t.1,sub_add_cancel,Real.rpow_one] at e; exact e
lemma lift_budget (F:H≃ₗᵢ[ℂ]D)(x:H.Op): ‖F.conjStarAlgEquiv x‖≤ ‖x‖:= by
 refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) ?_
 intro y; obtain ⟨y,rfl⟩:= F.surjective y; simp_rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,LinearIsometryEquiv.symm_apply_apply,F.norm_map]; exact x.le_opNorm _
lemma matching (p:ℕ)(z:ℂ)(b:n≤p): glacier C n*rise C n z=glacier C n*rise C p z:=by
 refine ((earth C n).times (rising C n z)).single (?_)
 convert (earth C n).times (rising C p z) using 1; ext1 x; by_cases h:x∈slopeZone C n
 · simp[h,rise_tag,face_ready C n x h,face_ready C p x (grow C n p b h)]
 simp[h]
lemma narrower(p:ℕ)(b:n≤p)(z:ℂ) : Q*(twinkle C p k z)*Q=twinkle C n k z:=by
 let T₁:=glacier C p
 have h(w): Q*(rise C p w*T₁)=rise C n w*Q:= by
   rw [←mul_assoc,←matching _ _ p w b,(glacier_walk ..).eq,mul_assoc,show Q*T₁=Q from skate C n p b]
 have ht(w): T₁*rise C p w*Q=Q*rise C n w:=by
   have e:Commute (rise C p w) Q:= (rising ..).jointly (earth C n);
   unfold T₁; rw [mul_assoc,e.eq, ←mul_assoc, ((earth C p).jointly (earth C n)).eq, skate C n p b,matching C n p w b] -- unfold T₁
 unfold twinkle; change Q*(rise C p z*T₁*k*T₁*rise C p (-z))*Q=_
 rw [show Q*(rise C p z*T₁*k*T₁*rise C p (-z))*Q=(Q*(rise C p z*T₁))*k*(T₁*rise C p (-z)*Q) from by simp only[mul_assoc],h,ht]; simp only[mul_assoc]
end YM.Quartz
