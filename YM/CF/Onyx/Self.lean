import YM.CF.Onyx.Tint
set_option autoImplicit false
noncomputable section
namespace YM.CF.Onyx
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Flare
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {N:Side}{j:ℕ}{r C:ℝ}{M:Male}
def fac(s:Offset N)(j:ℕ)(M:Male)(r:ℝ)(k:Site N):Peb:= if r*pinch N^2<disk j M (glen s k) then dip j M (tmap (glen s k)) else 0
lemma fab(s:Offset N)(j)(M:Male)(r C:ℝ)(h:0<C):FormU s j M r C (fac s j M r):=⟨fun i he=>if_pos he,fun i he=>by rw [fac,if_neg (not_lt.mpr he)]; exact norm_zero.trans_le (div_pos h (pinch_pos _)).le⟩
lemma nil_t(j)(M:Male)(r:ℝ)(s:Side)(p:Even s.val): ∑ k,fac (zeroF s) j M r k=0:=by
 let A:= fac (zeroF s) j M r; have he(k:Site s):A (Rush.backN k)= -A k:=by
    obtain ⟨y,hy⟩:=Rush.dollar k; let i:= Rush.backN k; let x:=tmap (pm k); let z:=tmap (pm i)
    change z= -x + _ at hy; have hv(K:Site s): glen (zeroF s) K=pm K:=add_zero .. 
    have ha:x∈realCube zone:= base_subset_realCube zone_pos (Rush.mel_h k); have hb:z∈realCube zone:=base_subset_realCube zone_pos (Rush.mel_h i); have he:=realCube_neg ha
    have hz : shell j M.val z=shell j M.val (-x):=by rw [hy]; exact shell_overlap _ _ _ he y (hy ▸ hb)
    have hm : dip j M z=dip j M (-x):=by unfold dip; rw [hz,←pear,←pear, hy,bar_overlap _ _ he y (hy ▸ hb)]
    unfold A fac disk; rw [hv,hv]; change (if _< ‖shell j M.val z‖ then dip j M z else _) = -(if _< ‖shell j M.val x‖ then dip j M x else _)
    rw [hz, foxy j M ha he,hm,dusk j M ha he]; split_ifs <;> simp
 have ht: (∑ k,A k) = -(∑ k,A k):=by nth_rw 1 [← Equiv.sum_comp (Rush.backN (N:=s)) A]; simp_rw [he,sum_neg_distrib]
 let Y:= ∑ k,A k; have hp : (2:ℂ) • Y=0:=by rw [two_smul, ← sub_neg_eq_add, ← ht, sub_self] -- inspect
 exact (smul_eq_zero.mp hp).resolve_left (by norm_num)
lemma gross (H:1≤j)(p:0<r)(u:0<C): ∃ V:ℝ,0<V∧∀ {N: Side}{A:Site N→Peb}{M:Male}{s:Offset N}, Even N.val→FormU s j M r C A→∀ k:Site N,‖A k‖≤ V/pinch N:=by
 obtain ⟨b,B,h,hB,P⟩:=soul j H; obtain ⟨c,V,t,hv,L⟩:=stern H p; refine ⟨max (B*V) C,lt_max_of_lt_right u,fun {N} {A} {M} {s} g e k=>?_⟩; let l:=pinch N; have hh:0<l:=pinch_pos N; let x:=glen s k; by_cases o:r*l^2<disk j M x
 · rw [e.far k o]; have hx := (L N M s k g).2 o; change l ≤ V*‖x‖ at hx; have hg:0<‖x‖:=by nlinarith
   exact ((P M x (orb _ s g) 1 one_pos).2).trans ((show B/‖x‖ ≤ B*V/l by rw [div_le_div_iff₀ hg hh]; nlinarith only [mul_le_mul_of_nonneg_left hx hB.le]).trans (div_le_div_of_nonneg_right (le_max_left ..) hh.le))
 exact (e.near k (le_of_not_gt o)).trans (div_le_div_of_nonneg_right (le_max_right ..) hh.le)
def countR (w:ℝ)(d: Axis)(k:Site N)(A B:Site N→Peb):= B k-∑ i∈range 8,(bead 8 w i:ℂ) • A (k+wrap N (i • step d))
set_option maxHeartbeats 500000 in
lemma bedK (H:1≤j)(p:0<r)(a:Axis):∃ V G:ℝ,0<V∧0<G∧∀ {N: Side}{A B:Site N→Peb}{M:Male}{s x:Offset N}{C:ℝ}, Even N.val→FormU s j M r C A→FormU x j M r C B→16*pinch N<zone→∀ w:ℝ,|w|≤1→ x.val=s.val+beam a (w*(2*pinch N))→∀ k:Site N,V ≤ tall k →‖countR w a k A B‖≤ G/(pinch N * tall k^8):=by
 obtain ⟨b,h,ht,hv,L⟩:=Jill.plunge (drill (A:=crop) (x:=RayH.x) (fun _=>rfl) RayH.cap RayH.M H a) 8 (by decide)
 obtain ⟨c,d,hc,hd,X⟩:=stern H p; let V:=20+c+4/b; have hV:0<V:=by unfold V; positivity
 refine ⟨V,h*4^8,hV,by positivity,fun {N} {A B} {M} {s x} {C} g f l e w u hp k H=>?_⟩
 let D:=glen s k; let U:=tall k; have hu:1 ≤ U:=tall_p _; have hc': c+19<U:=by change V≤U at H; unfold V at H; have hh:0<4/b:=(by positivity); linarith
 have hp':= pinch_pos N; have hh: (18+c)*pinch N< ‖D‖:=lt_of_lt_of_le (by nlinarith : _ < (U-1)*pinch N) (crest k s).1; have he: pinch N≤ ‖D‖:=(by nlinarith); have hE:= hp'.trans_le he; let i:RayH:=⟨M,D,orb _ _ g,hE⟩; let y:= 2*pinch N/‖D‖; have hy:0<y:=by unfold y; positivity
 have hz: y*U≤4:=by unfold y; rw [div_mul_eq_mul_div,div_le_iff₀ hE]; have z : (U-1)*pinch N≤‖D‖:=(crest k s).1; nlinarith
 have hm: ‖(y:ℂ)‖=y:=by rw [Complex.norm_real,Real.norm_of_nonneg hy.le]
 have ht:=L i w u y (hm.trans_lt (by have hx:4/b<U:=(by unfold V at H; change _≤U at H; linarith); rw [div_lt_iff₀ ht] at hx; nlinarith))
 let F(Z:ℂ):= dip j M (tmap D+spark a (raf crop i (Z*y)))
 have hq (q:ℝ)(p:|q|≤8)(C':Site N→Peb)(v:Offset N)(J:FormU v j M r C C')(y':Site N)(hq:peers (D+beam a (q*(2*pinch N))) (glen v y')): F (q:ℂ)=C' y':=by
    let S:=glen v y'; let T:=beam a (q*(2*pinch N)); have hh': Bound Real.pi S:=orb _ _ g; have hu:= (neigh (orb k s g) hh' hq).trans (rod_q a q p) -- tune
    have hm : c*pinch N≤‖S‖:=by obtain ⟨_,hx⟩:=abs_le.mp hu; change ‖D‖-‖S‖≤_ at hx; nlinarith
    have he:tmap (D+T) ∈ realCube zone:=by
      refine ⟨tmap_physical _,fun a'=>?_⟩; have hx:‖D‖≤Real.pi:=i.cap; have hh:‖T‖≤16*pinch N:=rod_q a q p; change |((_ :ℝ):ℂ).re|<_; rw [Complex.ofReal_re]; have hu:= (b_abs (D+T) a').trans (norm_add_le D T); linarith
    unfold F; rw [show tmap D=tmap i.x from rfl,snap]; rw [show ‖i.x‖*y=2*pinch N from (by change ‖D‖*_=_; unfold y; field_simp), J.far y' ((X N M v y' g).1 hm)]; exact seep _ _ hq he (base_subset_realCube zone_pos (b_base hh'))
 have hb:glen x k=D+beam a (w*(2*pinch N)):=by unfold D glen; rw [hp,←add_assoc]; -- tune
 change ‖F (w:ℂ)-∑ l∈range 8,(bead 8 w l:ℂ) • F (l:ℂ)‖ ≤ _ at ht; rw [sum_congr (g:=fun i=> (bead 8 w i:ℂ) • A (k+wrap N (i • step a))) rfl (fun j hj=>by rw [← Complex.ofReal_natCast j,hq (j:ℝ) (show _ from (by simpa using below8 hj)) A s f _ (sprout a s.val k j)]),hq w (u.trans (by norm_num)) B x l k (hb.symm ▸ peers.roll _), hm,zpow_neg,zpow_one,← div_eq_mul_inv] at ht
 change _ ≤ h/‖D‖*y^8 at ht; refine ht.trans ?_; change _≤h*4^8/(pinch N*U^8); rw [← div_div]; rw [le_div_iff₀ (one_pos.trans_le (one_le_pow₀ hu))]; rw [mul_assoc,←mul_pow]; rw [mul_div_right_comm]; gcongr
end YM.CF.Onyx
