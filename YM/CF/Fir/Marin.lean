import YM.CF.Fir.Navel
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fir
open Function Filter Lattice Laurent Bloch Next.Free Metric Finset Set
open scoped Topology Matrix BigOperators

variable {ι κ : Type*}
lemma switchPay {w w' : ι→ℝ}{f f':ι→Momentum→ℂ}(h:Moderate w f)(he : w≤w')(hf: ∃ η:ℝ,0<η ∧ ∀ i,∀ p∈cube η, f i p=f' i p) : Moderate w' f':=by
  obtain ⟨η,C,hp,hC,H⟩:= h.raise_price he; obtain ⟨θ,hθ,hf⟩:=hf
  refine ⟨min η θ,C,lt_min hp hθ,hC,fun i=>⟨fun p hx=>?_,fun p hx=>?_⟩⟩
  · have hy:=cube_mono (min_le_right ..) hx
    exact ((H i).hol _ (cube_mono (min_le_left ..) hx)).congr_of_eventuallyEq ((cube_open θ).eventually_mem hy |>.mono fun x h=>(hf i x h).symm)
  rw [← hf i p (cube_mono (min_le_right ..) hx)]; exact (H i).bound _ (cube_mono (min_le_left ..) hx)

lemma spicy (L:ι→Side)(hl:∀ i, Odd (L i).val)(l:∀ i, Site (L i))(h:∀ i, l i≠0)(a:Axis): Moderate (fun i=> (grade (l i))⁻¹) fun i p=> ((L i).val:ℂ)⁻¹ * bGraph (aliasAt p (l i)) a:=by
  let Y (i:ι) : Side:=1; have hy : ∀ i, Odd (Y i).val := fun _=>odd_one
  have hi:= (ink Y L hy hl l).inv (lamp Y L hl l h) (fun i=>pow_pos (grade_pos (l i)) 2)
  have hg:= ds_scaled Y L hl l a
  convert hi.mul hg using 2
  · next i => field_simp [(grade_pos (l i)).ne']
  ext p:1
  simp only [Y,D,ds_expand,bGraph,Pi.smul_apply,smul_eq_mul,mul_inv]; simp only [narrow,PNat.val_ofNat] -- inspect
  simp; field_simp


lemma extras_pay (j:ℕ)(hj:1≤j)(M:ι→Side)(h:∀ i,Odd (M i).val)(a:Axis): Moderate (fun _:ι=>1) fun i p=> extras j (M i) p a := by
  let s (i:ι) : Finset (Site (M i)):=univ.erase 0
  let F (i:ι)(l:Site (M i))(p:Momentum):= muff j (M i) (aliasAt p l)^2*((M i).val:ℂ)⁻¹*bGraph (aliasAt p l) a
  have hb : Moderate (fun _:ι=>1) (fun i p=>∑ l∈s i,F i l p) := by
    apply Moderate.sum_family s (fun i l=>decay 2 l)
    · obtain ⟨C,hC,H⟩:=decay_cost
      exact ⟨C,hC,fun i=> by rw [mul_one]; exact (Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun j _ _=> (decay_pos j _).le).trans (H (M i))⟩
    let W:= Σ i, { l // l∈s i}; let t (x:W):ι:=x.1; let l (x:W):Site (M (t x)):=x.2
    simp_rw [F,mul_assoc]
    exact (Moderate.mul ((muff_pay j (M ∘ t) (fun x=>h _) l).pow 2) (spicy (M ∘ t) (fun x=>h _) l (fun x=>ne_of_mem_erase x.2.property) a)).raise_price (fun x=>by
      change decay j (l x) ^ 2*(grade (l x))⁻¹ ≤ decay 2 (l x)
      let l:= l x; apply le_trans (mul_le_of_le_one_right (by positivity) (inv_le_one_of_one_le₀ (grade_ge _)))
      rw [sq, ← decay_add]; exact decay_anti _ (by omega))
  convert hb using 2
  ext p:1; simp only [s,extras,F,Pi.smul_apply, Finset.sum_apply,smul_eq_mul,Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _=>by ring
lemma bloomPay (j:ℕ)(M:ι→Side)(h:∀ i, Odd (M i).val): Moderate (fun _:ι=>1) fun i p=>bloom j (M i) p:=by
  simpa only [bloom,alias_zero_eq,one_pow] using ((muff_pay j M h (fun _=>0)).raise_price (u:=fun _=>1) (fun i=>decay_le_one ..)).pow 2
lemma massPay (j:ℕ)(hj:1≤j)(M:ι→Side)(h:∀ i, Odd (M i).val): Moderate (fun _:ι=>1) fun i p=>mass j (M i) p:=by
  have he (f g:ι→Momentum→Momentum) (H:∀ a, Moderate (fun _:ι=>1) fun i p=> (f i p : Momentum) a) (K:∀ a, Moderate (fun _:ι=>1) fun i p=> (g i p : Momentum) a): Moderate (fun _:ι=>1) fun i p=> prodM (f i p) (g i p):=by
    apply Moderate.sum _ _ (fun _=>zero_le_one); intro a _; simpa only [mul_one] using (H a).mul (K a)
  have hp := he _ _ (extras_pay j hj M h) (extras_pay j hj M h)
  have hh := (D_cost M h).mul ((Moderate.const 1).add hp)
  have ht := ((Moderate.const 2).mul (bloomPay j M h)).mul (he _ _ (ds_cost M) (extras_pay j hj M h))
  have hv := ((bloomPay j M h).pow 2).mul (C_cost M h)
  simp only [one_pow,mul_one] at hh ht hv; exact (hh.add ht).add hv
lemma invMass (j:ℕ)(hj:1≤j)(M:ι→Side)(h:∀ i, Odd (M i).val): Moderate (fun _:ι=>1) fun i p=>(mass j (M i) p)⁻¹:=by
  have he:= massPay j hj M h
  suffices H : Firm (fun _:ι=>1) (fun i=>mass j (M i)) by simpa only [inv_one] using he.inv H (fun _=>one_pos)
  obtain ⟨η,C,hη,hC,H⟩:=he; let a:=min η zone; have ha:=lt_min hη zone_pos
  let F i:=mass j (M i); have hx i:= (H i).mono (min_le_left η zone) le_rfl
  let r:=a/2; have hr:0<r:=by unfold r; positivity
  have hb: ball (0:Momentum) r ⊆ cube a:=ball_inside_cube (cube_zero r hr) |>.trans' (ball_subset_ball (show r≤a-r by unfold r; linarith)) -- fix
  let t:=min (r/2) (r/(C+2)); have ht: 0<t:=lt_min (by linarith) (by positivity)
  let d:ℝ:= 1/2*meter.low^2*t^2; have hd:0<d:=by have:=meter.low_pos; positivity
  refine ⟨a,min 1 d,ha,lt_min one_pos hd,fun i p hm=> ?_⟩
  dsimp only; rw [mul_one]
  by_cases hs: ‖p‖<t
  · apply (min_le_left ..).trans
    have hu : MapsTo (F i) (ball 0 r) (closedBall (F i 0) (C+2)) := by
      intro z hz; rw [mem_closedBall,dist_eq_norm]
      have hs : ‖F i z‖≤C:=by simpa using (hx i).bound _ (hb hz)
      exact (norm_sub_le ..).trans (by simpa [F] using add_le_add_right hs 2)
    have he := Complex.dist_le_div_mul_dist_of_mapsTo_ball
      (fun z hz=>((hx i).hol z (hb hz)).differentiableWithinAt) hu (show p ∈ Metric.ball (0:Momentum) r from mem_ball_zero_iff.mpr (hs.trans ((min_le_left ..).trans_lt (by linarith))))
    have hv : dist (F i p) (F i 0)≤1 := he.trans (calc
        _ ≤ (C+2)/r * (r/(C+2)):=by rw [dist_zero_right]; gcongr; exact hs.le.trans (min_le_right ..)
        _ = 1:=by field_simp)
    have he := norm_sub_norm_le (F i 0) (F i p); rw [dist_comm,dist_eq_norm] at hv; simp only [F,mass_origin] at hv he; norm_num at hv he; linarith
  apply (min_le_right ..).trans
  push Not at hs
  have hy : p ∈ realCube zone := ⟨hm.1,fun u=>(hm.2 u).trans_le (by gcongr; exact min_le_right ..)⟩
  have hu : p≠0:= norm_pos_iff.mp (ht.trans_le hs)
  have hh:= (D_lower (M i) hm.1).trans ((mass_price j _ (h i) hy hu).trans (Complex.re_le_norm _))
  obtain ⟨u,he⟩:∃ u, ‖p‖=‖p u‖:= -- search
    by obtain ⟨u,heu⟩:= (IsGreatest.pi_norm p).1; exact ⟨u,heu.symm⟩
  have hz:= calc
     t^2 ≤ ‖p u‖^2 := by rw [← he]; gcongr
     _ ≤ lengthSq p := Finset.single_le_sum (f:=fun i: Axis=>‖p i‖^2) (fun i _=>sq_nonneg _) (Finset.mem_univ u)
  unfold d; rw [mul_assoc]
  exact (mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left hz (by positivity)).trans (divisor_real_bounds (M i) hy).1) (by norm_num)).trans hh
lemma shellPay (j:ℕ)(hj:1≤j)(M:ι→Side)(h:∀ i, Odd (M i).val): Moderate (fun _:ι=>1) fun i p=>shell j (M i) p:=by
  simpa only [one_mul, shell, div_eq_mul_inv] using (D_cost M h).mul (invMass j hj M h)
lemma skinPay (j:ℕ)(hj:1≤j)(M:ι→Side)(h:∀ i, Odd (M i).val)(a:Axis): Moderate (fun _:ι=>1) fun i p=> skin j (M i) p a:=by
  have he:= (bloomPay j M h).mul (ds_cost M a); have hx := (D_cost M h).mul (extras_pay j hj M h a)
  simpa only [mul_one,Pi.smul_apply,Pi.add_apply,smul_eq_mul,skin] using (invMass j hj M h).mul (he.add hx)
end YM.CF.Fir
