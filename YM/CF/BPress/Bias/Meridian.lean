import YM.CF.BPress.Spin.Blank
/-!
 § VolumeB-marker, eq:nogapz part of lem:B-bias. Discrete, quantitative form of
 the jump argument, so don't need taking symbol or projector limits. Use the actual DC split
 (including Male uniformity) to look at Z = -zen(mixL) Aop. Difference on one tangential
 axis ±y, engine is sin(±y/M)/D; all high-mode fold extras cost bounded slope. Pay the
 loss in the nonsingular parts before taking y (momentum coordinate!) small. Includes
 the antiperiodic seam even at time wrap.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Bias
open Function Finset Filter Lattice Laurent Bloch Next.Free Fir Lat Spin Cube Blank
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators
attribute [local instance] opCStarAlgebra
section BaseCosts
variable {f:Jill.Male→Momentum→ℂ} (h:Moderate (fun _=>1) f)
include h
lemma moderateSize : ∃ C:ℝ,0<C ∧ ∀ M,∀ p∈baseCube, ‖f M p‖ ≤ C:=by
 obtain ⟨η,C,hη,hc,H⟩:=h; exact ⟨C,hc,fun i p hp=> by simpa only [mul_one] using (H i).bound p (mem_cube_real (base_subset_realCube hη hp) hη)⟩
lemma moderateSlope : ∃ C:ℝ,0<C ∧ ∀ M,∀ p∈baseCube,∀ q∈baseCube, ‖f M p-f M q‖ ≤ C*‖p-q‖:=by
 obtain ⟨η,C,v,hc,H⟩:=h; let a:=η/2; let b:= η-a; have ha:0<a:=half_pos v; have hb:0<b:=half_pos v|>.trans_le (by unfold b a; linarith)
 refine ⟨(C+C)/b,by positivity,fun i p hp q hq=>?_⟩; have Ht(x)(y:x∈cube η):‖f i x‖ ≤ C:=by simpa only [mul_one] using (H i).bound x y
 have hb' := ball_inside_cube (η:=η) (mem_cube_real (base_subset_realCube ha hq) ha); have hc' := Ht _ (mem_cube_real (base_subset_realCube v hq) v)
 by_cases ht: p∈ Metric.ball q b; swap
 · rw [Metric.mem_ball, dist_eq_norm, not_lt] at ht; apply (norm_sub_le ..).trans ((add_le_add (Ht _ (mem_cube_real (base_subset_realCube v hp) v)) hc').trans ?_); exact le_trans (le_of_eq (div_mul_cancel₀ (C+C) hb.ne').symm) (mul_le_mul_of_nonneg_left ht (by positivity))
 have hy:=Complex.dist_le_div_mul_dist_of_mapsTo_ball
    (fun z hz=>((H i).hol z (hb' hz)).differentiableWithinAt) (show Set.MapsTo (f i) (Metric.ball q b) (Metric.closedBall (f i q) (C+C)) from fun x hx=>Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; exact (norm_sub_le ..).trans (add_le_add (Ht _ (hb' hx)) hc'))) ht
 simpa only [dist_eq_norm] using hy
lemma moderateFront (w:ℝ)(p: (0:ℝ)<w) : ∃ η,0<η∧∀ M,∀ x∈baseCube, ‖x‖≤η → ‖f M x-f M 0‖≤w:=by
 obtain ⟨C,c,T⟩:=moderateSlope h; refine ⟨w/C,by positivity,fun M x y v=>(T M x y _ ?_).trans ?_⟩
 · refine ⟨star_zero _,fun i=>?_⟩; simpa using Real.pi_pos.le
 rw [sub_zero]; exact (mul_le_mul_of_nonneg_left v c.le).trans_eq (mul_div_cancel₀ _ c.ne') -- tune
end BaseCosts
open scoped BigOperators
variable {M:Jill.Male} {N:Side}
lemma ds_value (M:Side)(k:Site N) (i:Axis): ds M (Rush.mel k) i=((M.val*Real.sin (pm k i / M.val):ℝ):ℂ):=by
 rw [ds_expand,sine]; unfold Rush.mel tmap narrow; dsimp only [Pi.smul_apply,smul_eq_mul]; push_cast; rw [← Complex.ofReal_natCast M.val, ←Complex.ofReal_inv, ← Complex.ofReal_mul]; congr 2; push_cast; ring
lemma ds_norm (M:Side)(k: Site N)(i:Axis) : ‖ds M (Rush.mel k) i‖≤ |pm k i|:=by
 let p:=pm k i; have hx:= nPos M; rw [ds_value,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_pos hx]; exact (mul_le_mul_of_nonneg_left Real.abs_sin_le_abs hx.le).trans_eq (by rw [abs_div,abs_of_pos hx,mul_div_cancel₀ _ hx.ne'])
lemma pm_norm(k:Site N)(i:Axis): ‖Rush.mel k i‖=|pm k i|:=by rw [Rush.mel,tmap,Complex.norm_real, Real.norm_eq_abs]

-- D lower everywhere, upper by sin/Cminus near 0
abbrev clockS (M:Side){N:Side}(k:Site N):=(Fir.D M (Rush.mel k)).re
lemma D_real (k:Site N)(M:Side): Fir.D M (Rush.mel k)=(clockS M k:ℂ):=by apply Complex.ext <;> simp [clockS,phys_D M (Rush.mel_h k).1]
lemma D_angle : ∃ c:ℝ,0<c ∧∀ M:Side,∀ (N:Side)(k:Site N)(r:ℝ),0≤r→ r≤ ‖Rush.mel k‖ → c*r^2≤ clockS M k:=by
 refine ⟨1/2 * meter.low^2, by have:=meter.low_pos; positivity,fun M N k r hr w=>?_⟩; let p:=Rush.mel k; have hx: r^2≤lengthSq p:=by
    obtain ⟨u,g⟩:∃ u, ‖p u‖=‖p‖:= (IsGreatest.pi_norm p).1; refine le_trans ?_ (single_le_sum (f:=fun i:Axis=> ‖p i‖^2) (fun i _=>sq_nonneg _) (mem_univ u)); rw [g]; exact pow_le_pow_left₀ hr w _
 have hp:=Rush.mel_h k; rw [mul_assoc]; exact (mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left hx (sq_nonneg _)).trans (divisor_real_bounds M (base_subset_realCube zone_pos hp)).1) (by norm_num)).trans (D_lower M hp.1)
lemma D_surface : ∃ η,0<η ∧ ∀ (M:Jill.Male) (N:Side) (k:Site N), ‖Rush.mel k‖≤η → clockS M.val k ≤ 4*‖Rush.mel k‖^2:=by
 obtain ⟨η,h,H⟩:=moderateFront (C_cost (·.val) fun i=>i.property) 1 one_pos; refine ⟨η,h,fun M N k hi=>?_⟩; let p:= Rush.mel k; have hc:1≤ ‖Cminus M.val p‖:=by
    have he:= H M p (Rush.mel_h _) hi; have hx: Cminus M.val 0=2:=by norm_num [Cminus, rad, mag, kin, pl, sine, narrow];
    have hu:= norm_sub_norm_le (2:ℂ) (Cminus M.val p); rw [hx,norm_sub_rev] at he; norm_num at hu; linarith
 have ht:= calc
    ‖Fir.D M.val p‖*‖Cminus M.val p‖ = ‖∑ i:Axis, ds M.val p i^2‖:=by rw [← norm_mul,ds_sq]
    _ ≤ _:= norm_sum_le ..
    _ ≤ ∑ i : Axis, ‖p‖^2 := sum_le_sum fun i _=> by rw [norm_pow]; apply pow_le_pow_left₀ (norm_nonneg _); apply (ds_norm ..).trans; rw [← pm_norm]; exact norm_le_pi_norm ..
    _ = 4*‖p‖^2:= by simp [Axis,nsmul_eq_mul]
 exact (Complex.re_le_norm _).trans ((le_mul_of_one_le_right (norm_nonneg _) hc).trans ht)
abbrev axisR : Axis:=2
abbrev biasR (j:ℕ)(M:Jill.Male){N:Side}(k:Site N):=(bloom j M.val (Rush.mel k)).re
lemma bloom_real (M:Jill.Male) (j:ℕ)(k:Site N): bloom j M.val (Rush.mel k)=(biasR j M k:ℂ):=by
 have he:star (bloom j M.val (Rush.mel k))=bloom j M.val (Rush.mel k):=by rw [bloom,star_pow,muff_real _ M.val M.property _ (na_phys M.val (Rush.mel_h _).1)]
 obtain ⟨r,t⟩:=Complex.conj_eq_iff_real.mp he; simp [biasR,t]
lemma bloom_geometry (j:ℕ) : ∃ η C:ℝ,0<η ∧ 0<C ∧ ∀ (M:Jill.Male) (N:Side)(k:Site N), |biasR j M k|≤ C ∧ (‖Rush.mel k‖≤η → 1/2 ≤ biasR j M k):=by
 let f(M:Jill.Male):=bloom j M.val; have ht:= show Moderate (fun _=>1) f from bloomPay j _ fun i=>i.property; obtain ⟨η,h,H⟩:=moderateFront ht (1/2) one_half_pos; obtain ⟨C,hc,hK⟩:= moderateSize ht
 refine ⟨η,C,h,hc,fun M N k=>⟨(Complex.abs_re_le_norm _).trans (hK _ _ (Rush.mel_h _)),fun hx=>?_⟩⟩; have hg:= H M _ (Rush.mel_h _) hx; unfold f at hg; rw [show bloom j M.val 0=1 by simp [bloom,narrow],bloom_real] at hg
 rw [← Complex.ofReal_one,← Complex.ofReal_sub, Complex.norm_real,Real.norm_eq_abs] at hg; linarith [(abs_le.mp hg).1]
end YM.CF.BPress.Bias
