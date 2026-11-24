import YM.CF.BPress.Neumann
/-! VolumeB-gate internal flag bounds using eq:B-blend and the true smoothing sizes. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress
open Function MeasureTheory LocalH Lattice SU Mag Cube Grid Filter Branch Sheet Tunnel Finset Pressure
open scoped Topology BigOperators Classical Matrix
variable {s : Side} {T : Atlas} {y C C' Lf : ℝ} {B : ℕ} (F : Net s T Lf y C C' B) (W : Tunnel s) (U V : Micro s) (p : Duo s)
namespace Net
private theorem ceiling_T (T : Atlas) : ∃ K δ : ℝ, 0<K ∧ 0<δ ∧ ∀ (s:Side)(C C' y Lf:ℝ)(B:ℕ) (W:Tunnel s)(F:Net s T Lf y C C' B)(p:Duo s)(x:FacesH s), let r:= C/(frameWidth Lf y).val; 0≤ C→ r<δ →(∀ i, T.passes y x.1 i ∧ T.passes y x.2 i) →
    (∀ k≤W.n.val, ∀ (i:Tri s) (j l:SpatialDir), group.chord (plaq (F.built W x p k) i j l)≤ C'*mA y + K*r^2) ∧
    ∀ k<W.n.val, ∀ (i:FlatLink s), chord (F.built W x p (k+1) i) (F.built W x p k i) ≤ K*(2/(W.n.val:ℝ))*r := by
 obtain ⟨δ,K,h,P,l,G⟩:= chord.blend_cost T.toChart; refine ⟨K,δ,P,h,?_⟩; intro s C C' y Lf B W F p x r t e H
 let a:= adjust (F.fill x p).1 x.1; let b:= adjust (F.fill x p).2 x.2
 have bnd (i:FlatLink s) : group.chord (a i) ≤ r ∧ group.chord (b i) ≤ r:= ⟨F.frame_small _ (fun x=>(H x).1) i, F.frame_small _ (fun x=>(H x).2) i⟩
 have f(k:ℕ)(i): F.built W x p k i=chord.blend _ (W.progress k) (a i) (b i):=rfl -- tune
 constructor
 · intro k _ i j l; let g:Fin 4 → FlatLink s:= ![(i,j),(hop i j 1,l),(hop i l 1,j),(i,l)]; exact (G r e _ _ (bnd (i,j)).1 (bnd (i,j)).2).2 (W.progress k) (C'*mA y) (fun i=>a (g i)) (fun i=> b (g i)) (fun i=> bnd (g i)) (W.ratio_I k) ((plaq_tension a i j l).le.trans ((F.flat (F.fill x p).1 x.1 (fun i=>(H i).1)).flat i j l)) ((plaq_tension b i j l).le.trans ((F.flat (F.fill x p).2 x.2 (fun i=>(H i).2)).flat i j l))
 intro k _ i; rw [f,f]; apply ((G r e _ _ (bnd i).1 (bnd i).2).1 _ (W.ratio_I _) _ (W.ratio_I _)).trans; gcongr -- tune
 · exact W.ratio_step k

private lemma kernel_widths (G:GapSize)(K C C' : ℝ)(p:0<K)(h:0<C)(v:0<C') : ∀ᶠ L:ℝ in atTop, 0<L ∧ ∀ᶠ y:ℝ in atTop, 0<y ∧
   let R:= ((frameWidth L y).val:ℝ)
   let n:= ((G.select y).marked.val:ℝ)
   4*xi y +(C'*mA y + K*(C/R)^2) ≤ temp y/2 ∧ 4*xi y + (K*(2/n)*(C/R)) ≤ temp y/2 := by
 -- buy L large so K*C²/L² ≤ 1/8; use n ≥ t⁻¹ after delay, C/R NPL etc
 have ht : ∀ᶠ L:ℝ in atTop, K*C^2/L ≤ 1/8 := (tendsto_const_nhds.div_atTop (g:=fun L:ℝ=>L) tendsto_id (a:=K*C^2)).eventually (ge_mem_nhds (by norm_num)) -- tune
 filter_upwards [ht,eventually_ge_atTop (1:ℝ)] with L l hL; have hl : 0<L:=zero_lt_one.trans_le hL
 have xi_l : NPL (fun i=>xi i/temp i) := npl_congr ((eventually_gt_atTop (0:ℝ)).mono fun i p=> show root i^4*heigh i^(-8:ℤ)=_ from by have h:=root_pos p; have hv:=heigh_pos i; rw [temp_price p,xi_price p,zpow_neg]; field_simp  -- tune
    ) (root_tall _ _ (by omega))
 have m_l : NPL (fun i=>mA i/temp i):= npl_congr ((eventually_gt_atTop (0:ℝ)).mono fun i p=> show (heigh i)⁻¹^2=_ from by have h:=root_pos p; have hv:=heigh_pos i; rw [temp_price p,mA_price p]; field_simp) (npl_power heigh_npl _ (by omega))
 let B:= (2:ℝ) * (G.collar:ℝ); refine ⟨hl,?_⟩; filter_upwards [frame_bounds hl,G.bounds,G.tail_P,npl_temp.drop.eventually (gt_mem_nhds (by norm_num : 0< (1/2:ℝ))), G.marked_late.eventually_ge_atTop B,(xi_l.const_mul 4).drop.eventually (ge_mem_nhds (by norm_num : 0<(1/8:ℝ))), (m_l.const_mul C').drop.eventually (ge_mem_nhds (by norm_num : 0<(1/8:ℝ))),w_late hl|>.eventually_ge_atTop (16*K*C), eventually_gt_atTop (0:ℝ)] with y w q k x b d e o a; refine ⟨a,?_⟩; dsimp only
 let t:=temp y; let n:= ((G.select y).marked.val:ℝ); let R:=((frameWidth L y).val:ℝ); have hp:= q.2.1; have hR:0<R:=by unfold R; positivity
 rw [←k] at hp
 have hB : (((G.select y).P):ℝ)= n+B:= by unfold BandWidth.P n B; push_cast; rfl -- tune
 have ht:0<t:=temp_pos a; have hv:t⁻¹≤ n:= by
   rw [hB] at hp; change t⁻¹^2≤ _ at hp; change t<1/2 at x; change n≥ B at b; have e : (2:ℝ) ≤ t⁻¹:=by rw [inv_eq_one_div,le_div_iff₀ ht]; linarith
   nlinarith -- tune
 have xi : 4*xi y ≤ 1/8*t:=by apply (div_le_iff₀ ht).mp; rw [mul_div_assoc]; exact d
 have m : C'*mA y ≤ 1/8*t:=by apply (div_le_iff₀ ht).mp; rw [mul_div_assoc]; exact e
 have nW : 2/n ≤ 2*t:=by
   rw [div_eq_mul_inv]; apply mul_le_mul_of_nonneg_left ?_ (by norm_num); rw [←inv_inv t]; -- tune
   exact inv_anti₀ (inv_pos.mpr ht) hv
 have aW : K*(C/R)^2 ≤ 1/8*t:= by
   have hw := w.1; let s:= Real.sqrt t; have hs:0<s:=Real.sqrt_pos.mpr ht; have h:s⁻¹*L ≤ R:=by rw [mul_comm,←div_eq_mul_inv]; exact hw
   have hz:/- t R² ≥ L² -/ L^2 ≤ R^2*t:=by have hh:L≤ R*s:=(div_le_iff₀ hs).mp hw; exact le_trans (pow_le_pow_left₀ hl.le hh _) (by unfold s; rw [mul_pow,Real.sq_sqrt ht.le]) -- tune
   have hg:K*C^2≤1/8*L^2:= (div_le_iff₀ hl|>.mp l)|>.trans (by nlinarith) -- tune shadow
   rw [div_pow,←mul_div_assoc,div_le_iff₀ (by positivity)]; nlinarith only [hz,hg]
 have pW : K*(2/n)*(C/R) ≤ 1/8*t := calc
   _ ≤ K*(2*t)*(C/R):=by gcongr
   _ ≤ _:= by rw [←mul_div_assoc,div_le_iff₀ hR]; change 16*K*C ≤ R at o; nlinarith only [o, mul_le_mul_of_nonneg_left o ht.le] -- tune shadow
 unfold R at aW pW; unfold n at pW; constructor <;> change _ ≤ t/2 <;> first| linarith only [ht,xi,m,aW]| linarith only [ht,xi,pW]

/-- VolumeB-gate `t/2` bound on true N Mark arguments. Keep as an eventual L and on tails of y; period independent. -/
theorem flags_N (G:GapSize)(T : Atlas)(C C':ℝ) (u:0<C)(h:0<C'): ∀ᶠ L:ℝ in atTop, 0<L ∧ ∀ᶠ y:ℝ in atTop, ∀ (s:Side)(B:ℕ)(F:Net s T L y C C' B)(X:Bands s (G.select y))(i:X.Index), let W:=X.mark i; ∀ (U:Micro s)(p:Duo s), p∈T.pairs y (W.reads U)→ F.markN W U p≠0 → ∀ j:Face (Per s), RG.touched j⊆ W.mem→ group.chord (faceValue U j)≤ temp y/2:=by
 obtain ⟨K,δ,b,P,f⟩:= ceiling_T T; filter_upwards [kernel_widths G K C C' b u h] with L x; refine ⟨x.1,?_⟩; filter_upwards [x.2, T.coasts_y, (w_late x.1).eventually_gt_atTop (C/δ)] with y a t l s B F X i; intro W U p v g j q
 let R:= ((frameWidth L y).val:ℝ); have hR: 0<R:=by unfold R; positivity
 have hr : C/R<δ:=by rw [div_lt_iff₀ hR]; rw [mul_comm]; exact (div_lt_iff₀ P).mp l
 let V:=W.reads U; let A:= F.template W V p; let E:= F.atlasG W V p; let M:=gauge E A; have hv:= T.pairs_ok y p V t|>.mp v -- tune arguments order
 obtain ⟨vv,AQ⟩:= f s C C' y L B W F p V u.le hr (fun i=>⟨(hv.1.1 i).1,(hv.2.1 i).1⟩); obtain ⟨hh,hw⟩:=a.2; let K':= temp y/2-4*xi y
 have hp : group.chord (faceValue A j) ≤ K':=by
   rw [← group.chord_conj (E j.1) (faceValue A j), ←face_gauge E A]; apply W.every_face (U:=M) ?_ ?_ j q
   · intro k p x o i _; rw [hq_eq]; unfold M E A; rw [F.universe_H W V _ p]; apply (vv k p x o i).trans; unfold K'; linarith only [hh]
   intro k p x i; rw [nq_price]; unfold M E A; rw [F.universe_V W V _ p,←rise_succ,F.universe_H W V _ p, F.universe_H W V _ p.le]; simp only [Pi.one_apply,one_mul,mul_one]; refine (AQ k p (x,i)).trans ?_; unfold K'; change 4 * xi y + K*(2/(W.n.val:ℝ))*(C/(frameWidth L y).val)≤ _ at hw; linarith
 rw [←group.chord_conj (W.axial U j.1) _,←face_gauge _ U, ←chord.one]; refine (chord.triangle _ (faceValue A j) _).trans ((add_le_add (chord.face _ _ _ _ (chord.Close.smaller (W.orient U) A q (F.isclose W p g (xi_pos a.1).le))) (chord.one _|>.le.trans hp)).trans ?_); unfold K'; linarith
end Net
end YM.CF.BPress
