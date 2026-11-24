import YM.CF.BPress.SheetSum
/-!
Costs from `eq:B-mood`--`eq:B-lift` and near `eq:B-healthy`. Build labels from the above Atlas. Single face pointwise versions: the neighborhood used in the bond statement can be enforced by the horizontal fields at nearby points, no global gauge assertion (fields integrated pointwise on actual draws).
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Sheet.Atlas
open Function MeasureTheory LocalH Lattice SU Mag Cube Grid Filter Branch Gauge
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius Asymptotics
attribute [local instance] frobInner
variable {s : Side} (T : Atlas)
open Asymptotics
-- prices to translate tolerances. δ read *strict*.
private lemma exp_fare : ∃ K : ℝ, 0<K ∧ ∀ v, ‖v‖ ≤ T.eps → group.chord (group.lieExp v) ≤ K*‖v‖:=by
 obtain ⟨K,h⟩:= chord.exp_lip group T.eps; refine ⟨ K/group.colorScale +1, by have he:=group.colorScale_pos; positivity, fun v p=>?_ ⟩
 have hx:= h.dist_le_mul v (Metric.mem_closedBall.mpr (by rwa [dist_zero_right])) 0 (Metric.mem_closedBall_self T.radius.le); simp only [chord.emb,dist_eq_norm,mat_lieExp_zero,sub_zero] at hx; unfold Gauge.chord; refine (div_le_div_of_nonneg_right hx group.colorScale_pos.le).trans ?_; rw [mul_div_right_comm]; gcongr; exact le_add_of_nonneg_right zero_le_one
private lemma tone_cost (H : Hue)(p : H∈Mood 1) : ‖H‖ ≤ 1+‖magnet‖:=by
 obtain ⟨k,v⟩:= p; have hu:‖shade k‖=‖magnet‖:=by
   rw [←dist_zero_right]; unfold shade Mag.paint; rw [← show spin k⁻¹ 0=(0:Hue) from PiLp.ext fun i=> by simp [spin_at],spin_dist,dist_zero_right] -- tune
 rw [dist_eq_norm] at v; exact (norm_le_norm_sub_add ..).trans (add_le_add v hu.le)
private lemma log_cost {y : ℝ}{x : Tri s}{U : Horiz s} (a : 0<y)(p : T.passes y U x)(i) :
    group.chord (plaq U x (first i) (second i)) < T.δ ∧ ‖snap group (plaq U x (first i) (second i))‖ ≤ mA y * (1+‖magnet‖):=by
 have t:=p.1 i; refine ⟨t,?_⟩
 have h : ‖(T.hue y U x) i‖ ≤ 1+‖magnet‖:= (PiLp.norm_apply_le ..).trans (tone_cost _ ?_); swap; · obtain ⟨l,v⟩:=p.2; exact ⟨l,v.trans (sigma_price y|>.symm ▸ inv_le_one_of_one_le₀ (rise y))⟩
 let g:=mA y; have he:0<g:=mA_pos a; change ‖g⁻¹ • T.logV _‖ ≤ _ at h; rw [chord.Chart.logV,if_pos t,norm_smul,Real.norm_of_nonneg (by positivity),mul_comm] at h; unfold g at *; rw [←div_eq_mul_inv] at h; rw [mul_comm]; exact (div_le_iff₀ he).mp h
/-- Curvature bound independent of thresholds on bonds, including reading curvature in any gauge after acceptance. -/
theorem horizon : ∃ C : ℝ, 0<C ∧ ∀ (s : Side) (y : ℝ), 0<y→ ∀ (g : HFrame s)(U : Horiz s), (∀ x,T.passes y U x) → Flat (adjust g U) (C*mA y):= by
 obtain ⟨K,h,H⟩:= T.exp_fare; refine ⟨K*(1+‖magnet‖),by positivity,?_⟩; intro s y t a U p; have ht : 0≤ K*(1+‖magnet‖)*mA y:=by have he:= mA_pos t; positivity
 refine ⟨ht,?_⟩; intro x i j; have e (i j : SpatialDir) (v:i<j): tension (adjust a U) 1 1 x i j ≤ K*(1+‖magnet‖)*mA y:= by
    rw [←plaq_tension]; obtain ⟨k,w,q⟩:=directions_back i j v; rw [w,q]; let Y:= plaq (adjust a U) x (first k) (second k); obtain ⟨v,E⟩:= T.log_cost t (T.Pass_g y a (p x)) k; change group.chord Y≤_
    rw [←T.read Y v.le]; refine (H _ (T.snap_small Y v.le).le).trans ((mul_le_mul_of_nonneg_left E h.le).trans_eq ?_); ring
 rcases lt_trichotomy i j with v|rfl|v; exact e _ _ v; simp [tension, ht]; rw [tension_sym]; exact e _ _ v

include T in
private lemma close_plaq : ∃ C : ℝ, 0<C ∧ ∀ᶠ y in atTop, ∀ s:Side, ∀ (x : Tri s)(i : Fin 3),
    let P:= plaq (magnetHoriz s y) x (first i) (second i)
    group.chord P≤ C*mA y ∧ dist (snap group P) (mA y • magnet i)≤ C*aA y^3 := by
 obtain ⟨C,p,Q⟩:= background_cost T.toChart; refine ⟨C,p, Q.mono fun y t s x i=>?_⟩; dsimp only; rw [←horiz_background (0:Per s),←hq_eq]
 obtain ⟨h,k,v⟩:= t s (event 0 x,⟨((first i).succ,(second i).succ), Fin.succ_lt_succ_iff.mpr (directions i)⟩); exact ⟨k,by rw [magnet_eval]; exact v⟩ -- tune
private lemma hue_triple (a b : Hue){r : ℝ} (p:0≤ r)(v : ∀ i, dist (a i) (b i)≤r) : dist a b ≤ 2*r:=by
 apply (sq_le_sq₀ dist_nonneg (by positivity : 0≤2*r)).mp; rw [dist_eq_norm, PiLp.norm_sq_eq_of_L2]; simp only [PiLp.sub_apply] -- tune
 apply le_trans (Finset.sum_le_sum (g:=fun (_:Fin 3)=> r^2) fun i _=> pow_le_pow_left₀ (norm_nonneg _) (by rw [←dist_eq_norm]; exact v i) _); simp; nlinarith -- tune

private lemma wc_pos {y : ℝ} (a:0<y) : 0<wc y:= by rw [wc_price a]; have h:=heigh_pos y; have he:= root_pos a; positivity
private lemma price_y : ∀ᶠ y:ℝ in atTop, 0<y ∧ aA y ≤ (heigh y)⁻¹^2 ∧ wc y=mA y * (heigh y)⁻¹^2 := by
 filter_upwards [(root_tall 5 1 (by omega)).drop.eventually (ge_mem_nhds zero_lt_one), eventually_gt_atTop (0:ℝ)] with y p q; change root y ^ 1 * heigh y ^ (5:ℤ) ≤ _ at p
 have he:=heigh_pos y; refine ⟨q,?_,?_⟩
 · rw [pow_one] at p; rw [aA_price q]; change root y * heigh y^5 ≤ _ at p; field_simp; refine le_trans ?_ p; exact Eq.le (by ring_nf; rfl)
 rw [wc_price q,mA_price q]; field_simp
private lemma plaque_healthy (C : ℝ)(p : 0≤C) : ∃ K : ℝ, 0<K ∧ ∀ᶠ y:ℝ in atTop, ∀ (s:Side) (U:Horiz s)(x:Tri s)(i : Fin 3),
    chord (plaq U x (first i) (second i)) (plaq (magnetHoriz s y) x (first i) (second i)) ≤ C*wc y →
    group.chord (plaq U x (first i) (second i))< T.δ ∧ dist (T.hue y U x i) (magnet i) ≤ K*(heigh y)⁻¹^2 := by
 obtain ⟨Q,h,H⟩:= T.close_plaq; refine ⟨T.C*C + Q, by have he:=T.span; positivity,?_⟩; filter_upwards [price_y,H, ((npl_wc.const_mul C).add (npl_mA.const_mul Q)).drop.eventually (gt_mem_nhds T.size)] with y q u t
 intro s U x i v; obtain ⟨q,e,b⟩:=q; obtain ⟨o,w⟩:=u s x i; let A:= plaq U x (first i) (second i); let B:= plaq (magnetHoriz s y) x (first i) (second i); have ht : group.chord A<T.δ:= by rw [←chord.one]; apply lt_of_le_of_lt _ t; exact (chord.triangle A B 1).trans (add_le_add v (chord.one ..|>.le.trans o)); -- maybe t implicit
 have hm:=mA_pos q; have hb : group.chord B ≤ T.δ:= o.trans ((le_add_of_nonneg_left (mul_nonneg p (wc_pos q).le)).trans t.le)
 refine ⟨ht,?_⟩; change dist ((mA y)⁻¹ • T.logV A) _≤_; rw [chord.Chart.logV,if_pos ht]; have hx: dist (snap group A) (mA y • magnet i) ≤ (T.C*C+Q)* mA y * (heigh y)⁻¹^2:= by
    apply (dist_triangle _ (snap group B) _).trans ((add_le_add ((T.fee A B ht.le hb).trans (mul_le_mul_of_nonneg_left v T.span.le)) w).trans ?_); have hs : aA y ^ 3 ≤ mA y * (heigh y)⁻¹^2:= by rw [pow_succ,aA_sq q]; exact mul_le_mul_of_nonneg_left e hm.le
    rw [b]; exact le_trans (add_le_add_right (mul_le_mul_of_nonneg_left hs h.le) _) (Eq.le (by ring))
 conv_lhs=>arg 2; rw [← inv_smul_smul₀ hm.ne' (magnet i)]
 rw [dist_eq_norm,←smul_sub,norm_smul,Real.norm_of_nonneg (by positivity),←dist_eq_norm]; refine (mul_le_mul_of_nonneg_left hx (by positivity)).trans_eq ?_; field_simp
private lemma ahead : ∃ C : ℝ, 0<C ∧ ∀ᶠ y:ℝ in atTop, ∀ i : Fin 3, group.chord (magnetH y i)≤ C*(heigh y)⁻¹^2:=by
 have hu(X : group.Color): ∃ C:ℝ, 0<C ∧ ∀ᶠ r:ℝ in 𝓝 0, group.chord (group.lieExp (r • X))≤ C*|r|:= by
   obtain ⟨C,h,v⟩:= (chord.exp_order X).exists_pos; refine ⟨C/group.colorScale,div_pos h group.colorScale_pos, v.bound.mono fun r e=>?_⟩
   unfold Gauge.chord; apply le_trans (div_le_div_of_nonneg_right e group.colorScale_pos.le); exact Eq.le (by rw [mul_div_right_comm]; rfl)
 choose C h v using fun i=>hu (generator i); let k:=∑ i,C i; have hL(i) : C i ≤ k := Finset.single_le_sum (f:=C) (fun i _=> (h i).le) (Finset.mem_univ i); refine ⟨k,(h 0).trans_le (hL _),?_⟩; filter_upwards [ eventually_all.mpr (fun i=> npl_aA.drop.eventually (v i)), price_y] with y p q i; apply (p i).trans; rw [abs_of_pos (aA_positive q.1)]; exact mul_le_mul (hL i) q.2.1 (aA_positive q.1).le ((h 0).le.trans (hL _))

-- local hypothesis is tangent readings on the base points in Bay ONE. This doesn't test an assignment at neighbors. For later support prices, every plaquette here and evaluation of an h_p needs radius two over these base points; not at further PL radius.
def Heals (C y : ℝ)(U : Horiz s)(x : Tri s) := ∀ i : FlatLink s, delta x i.1≤1→ chord (U i) (magnetH y i.2) ≤ C*wc y
structure Healthy (C y : ℝ) (T : Atlas)(U : Horiz s)(x : Tri s) : Prop where
 pass : T.passes y U x
 near_center (i : Fin 5) : chord (T.give y U x i) (center i) ≤ C*(heigh y)⁻¹^2

lemma heals_pass (C : ℝ)(p : 0≤C) : ∃ K : ℝ, 0<K ∧ ∀ᶠ y:ℝ in atTop, ∀ (s:Side)(U:Horiz s)(x:Tri s), Heals C y U x → Healthy K y T U x:=by
 obtain ⟨K,h,H⟩:= T.plaque_healthy (4*C) (by positivity); refine ⟨T.liftK*(2*K),by have he:= T.liftK_pos; positivity,?_⟩
 filter_upwards [H,(heigh_npl.const_mul (2*K)).drop.eventually (ge_mem_nhds zero_lt_one),T.coasts_y] with y t v f s U x p
 have he(i:Fin 3) : group.chord (plaq U x (first i) (second i))< T.δ ∧ dist (T.hue y U x i) (magnet i)≤ K*(heigh y)⁻¹^2:= by
   apply t; have he(i:SpatialDir) : chord (U (x,i)) (magnetH y i) ≤ C*wc y:= p (x,i) (by simp); exact (plaq_close U (magnetHoriz s y) x (first i) (second i) (he _) (he _) (p (_,second i) (delta_hop ..)) (p (_,first i) (delta_hop ..))).trans_eq (mul_assoc ..|>.symm)
 have hw:= heigh_pos y; have hx:= hue_triple (T.hue y U x) magnet (show 0≤ K * (heigh y)⁻¹^2 by positivity) fun i=>(he i).2; have hb:2*(K*(heigh y)⁻¹^2) ≤ sigmaN y:= by
   rw [sigma_price]; have ht:= inv_pos.mpr hw; change 2*K*(heigh y)⁻¹≤1 at v; nlinarith only [v, mul_le_mul_of_nonneg_right v ht.le]
 refine ⟨⟨fun i=>(he i).1,1, shade_one.symm ▸ hx.trans hb⟩, fun i=> (T.give_cost y i hx (hb.trans f.pass)).trans_eq ?_⟩ -- tune implicit y
 ring

/-- Verification of lifts near center z. The test on an edge, *for each i,j*: true iff i=j. This is needed on healthy components **including edges** of that condition, not presuming a lift on nonhealthy. -/
theorem heals_bond (C : ℝ)(p : 0≤C) : ∀ᶠ y:ℝ in atTop, ∀ (s:Side)(U:Horiz s)(z:FlatLink s), let x:=z.1; let x':= hop z.1 z.2 1; Heals C y U x → Heals C y U x' → ∀ i j, group.chord (T.give y U x i*U z*(T.give y U x' j)⁻¹) ≤ sigmaN y ↔ i=j := by
 obtain ⟨K,h,H⟩:= T.heals_pass C p; obtain ⟨A,t,G⟩:= ahead; let B:=2*K+C*1+A; filter_upwards [H,G,T.coasts_y,price_y,(heigh_npl.const_mul B).drop.eventually (ge_mem_nhds zero_lt_one),npl_mA.drop.eventually (ge_mem_nhds zero_lt_one)] with y g u o q v Q s U z; intro x x' hx hk
 let V:=T.give y U; have hY:(heigh y)⁻¹≥0:= inv_nonneg.mpr (heigh_pos _).le; have same(i:Fin 5): group.chord (V x i * U z * (V x' i)⁻¹)≤ sigmaN y:= by
    let h := (heigh y)⁻¹^2; have hl: chord (U z) 1 ≤ C*h + A*h:= by
       apply (chord.triangle _ (magnetH y z.2) _).trans; have he:= hx z (by dsimp [x]; simp); apply add_le_add (he.trans (mul_le_mul_of_nonneg_left ?_ p)) (chord.one ..|>.le.trans (u z.2)); rw [q.2.2]; exact mul_le_of_le_one_left (sq_nonneg _) Q
    have he : group.chord _ ≤ B*h:= calc
      _ = chord (V x i * U z * (V x' i)⁻¹) (center i * 1 * (center i)⁻¹):= (by rw [mul_one,mul_inv_cancel,chord.one])
      _ ≤ _:= (chord.product ..).trans ((add_le_add ((chord.product ..).trans (add_le_add ((g s U x hx).near_center i) hl)) ((chord.inv ..).le.trans ((g s U x' hk).near_center i))).trans_eq (by unfold B h; ring))
    rw [sigma_price]; exact he.trans (by unfold h; rw [pow_two,←mul_assoc]; exact mul_le_of_le_one_left hY v)
 intro i j; constructor
 · intro p; by_contra w; apply not_lt_of_ge (T.apart w); refine lt_of_le_of_lt ?_ o.sep; let a:= V x i * U z; let b:= a * (V x' i)⁻¹; let c:= a * (V x' j)⁻¹; refine (Eq.le (show chord (center i) (center j)=chord b c by unfold b c; rw [chord.left,chord.inv]; unfold V give; rw [chord.right])).trans ((chord.triangle b 1 c).trans (add_le_add (chord.one ..|>.le.trans (same i)) ((chord.comm ..).le.trans (chord.one ..|>.le.trans p))))
 rintro rfl; exact same _
end YM.CF.BPress.Sheet.Atlas
