import YM.SU5.FiniteGaugeData.ArchiveK.Pyr
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.ArchiveK
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush Largo WithLp
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
set_option linter.unusedSectionVars false
attribute [local instance] opCStarAlgebra
namespace Midway
open LightK Violas GramK MeasureTheory.Measure
set_option quotPrecheck false
variable {G:E4 ≃ₗᵢ[ℝ] E4}(L:FilterK){r:ℝ}(H:∀ p:Space3,‖p‖≤r→1/2≤ (garnet G L p).re){D c:ℕ}(K:ZephyrG G D c)(u:0<D)(q w:ℕ)
abbrev acc (n:ℝ)(q w:ℕ):ℝ:=Real.exp (n*q*w)
local notation "B"=> Metric.closedBall (0:Space3) r
local notation "V"=> Helix D
local notation "Ρ"=> pulseQ (D:=D) q w
local notation "Ω"=> songm (G:=G) (D:=D) L q w
local notation "Σ"=> Stamp q w
local notation "T" i:max=> tempoC (hornC D) (frostT w i)
include u H
lemma atuin (e:0<w)(x:‖(0:Space3)‖≤r)(v:32*w/D ≤ r)(p:Space3)(h:p∈ Helix D)(j:Zpo w) (i:Ket Σ) : let q':=p+arrowX D w j; acc (-2048) q w*(1/2)*‖(Ρ) i q'‖^2 ≤ songm (G:=G) (D:=D) L q w i q':=by
 intro q'; have hv:‖q'‖≤ _:= (budget_Q p u e h j).2; unfold songm; refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _); rw [mul_comm _ (1/2)]; have he: 0<(D:ℝ):=Nat.cast_pos.mpr u; apply mul_le_mul (H q' (hv.trans v)) _ ((Real.exp_pos _).le) ((by norm_num : (0:ℝ)≤ 1/2).trans (H _ (hv.trans v))); apply Real.exp_monotone; rw [le_div_iff₀ he] at hv; nlinarith only [mul_le_mul_of_nonneg_left hv (show 0≤(q:ℝ) by positivity)]
variable {e:ℝ}{U:Set Space3}(p:U⊆Helix D)(t: IsCompact U)(P:0<w)(Z:∀ p∈U,∀ v:Ket (Zpo w),e*‖v‖ ≤ ‖ract (WicketL D w p) v‖) (e₀:0<e) (hp:needLaunch K L q w) (g:32*w/D ≤ r)
include p t P Z e₀ hp g
-- Estimate head.Walt.H
lemma issueQ (i:Ket (Stamp q w)): acc (-2048) q w * (1/2)*e^2* (∫ p in U,∑ j:Zpo w,‖kNote D q w p i j‖^2) ≤ ∫ p in Metric.closedBall (0:Space3) r, songm (G:=G) (D:=D) L q w i p:= by
 let f:= (Ω) i; let S:= Helix D; let f₀(x):=∑ j:Zpo w, ‖kNote D q w x i j‖^2; have he:=K.unitC
 let A:= (closedBall (0:Space3) r); let X(j:Zpo w):=tempoC (hornC D) (frostT w j) '' U; let W:=⋃ j,X j; have hm:MeasurableSet A:= isClosed_closedBall.measurableSet; have hI(j:Zpo w):MeasurableSet (X j):=((T j).measurableEmbedding.measurableSet_image).mpr t.measurableSet
 have ht: W⊆A:= by intro x e; obtain ⟨j,y,l,rfl⟩:= Set.mem_iUnion.mp e; apply mem_closedBall_zero_iff.mpr; exact (budget_Q y he P (p l) j).2.trans g
 have hj:0<r:=by refine lt_of_lt_of_le (show 0<32*(w:ℝ)/D by have ht:0<(D:ℝ):=Nat.cast_pos.mpr u; have hg:0<(w:ℝ):=Nat.cast_pos.mpr P; positivity) g
 have hf: Integrable f:= (bbl K L q w i hp).1
 let b:= acc (-2048) q w*(1/2); have hb:0≤b:= mul_nonneg (Real.exp_pos _).le (by norm_num); have hY: (∫ x in W,f x)=∫ x in U,∑ i:Zpo w,f (x+arrowX D w i):=by
    have hQ: Pairwise (Function.onFun Disjoint X):= fun i j e=> (pac_disjoint 0 _ (horn_p u) (first_frost.ne e)).mono (Set.image_mono p) (Set.image_mono p)
    rw [show W=_ from rfl,integral_iUnion_fintype hI hQ (fun i=>hf.integrableOn),integral_finsetSum]; swap; · intro i _; exact ((tempo_c (hornC D) (frostT w i)).integrable_comp_of_integrable hf).integrableOn
    exact sum_congr rfl fun i _=> (picH f U (frostT w i)); -- tune `?_`
    -- picnic
 change b*e^2*(∫ p in U,f₀ p) ≤ ∫ p in A,f p; apply le_trans (b:=∫ p in W,f p) ?_ (setIntegral_mono_set _ _ ?_); -- focus check
 · rw [hY, ←integral_const_mul]; refine setIntegral_mono_on ?_ ?_ t.measurableSet fun p' p''=>?_
   · apply Integrable.const_mul ?_; exact (show Continuous f₀ from (by unfold f₀; fun_prop)).continuousOn.integrableOn_compact t
   · exact integrable_finsetSum _ (fun i _=>((tempo_c (hornC D) (frostT w i)).integrable_comp_of_integrable hf).integrableOn)
   let Y:Ket (Zpo w):= WithLp.toLp 2 (kNote D q w p' i); have hv: ‖Y‖^2=f₀ p':= EuclideanSpace.norm_sq_eq _; have hg := Z p' p'' Y
   have hw: ‖ract (WicketL D w p') Y‖^2= ∑ j:Zpo w,‖(Ρ) i (p'+ arrowX D w j)‖^2:= by rw [EuclideanSpace.norm_sq_eq]; simp_rw [babeEq p' K]; rfl -- tune
   rw [←hv, mul_assoc b, ←mul_pow]; apply le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hg 2) hb); rw [hw,mul_sum]; exact sum_le_sum (fun v _=> atuin L H u q w P (by simp [hj.le]) g _ (p p'') v i) -- tune signature
 · exact hf.integrableOn
 · refine ae_restrict_of_forall_mem hm (fun i t=>?_); have hg:= H _ (mem_closedBall_zero_iff.mp t); change 0≤ _* _ * ‖_‖^2; exact mul_nonneg (mul_nonneg (le_trans (by norm_num:0 ≤ (1:ℝ)/2) hg) (Real.exp_pos _).le) (sq_nonneg _)
 exact Eventually.of_forall ht
omit p t Z e₀ hp g
-- outside. ≥ 2048*w/D.Late. same filter, L tolerance. h eventually. < e-30000qw.
include K
lemma outside (t: 2000*w/D ≤ r): ∀ᶠ q:ℕ in atTop, ∀ i:Ket (Stamp q w), ‖∫ (p:Space3) in Bᶜ,songm (G:=G) (D:=D) L q w i p‖ ≤ acc (-10000) q w*‖i‖^2 := by
 obtain ⟨α,c,t',g,V'⟩:= garnet_cost G L; let A:=2^4; let Q(q:ℕ):= ((page (Stamp q w)):ℝ); let Tt(p:Space3):ℝ:= Real.exp (-1*‖p‖); -- conflict Tt notation
 have hp : ∀ᶠ q:ℕ in atTop, (Q q)^2*(c*∫ p':Space3,Tt p') ≤ acc 10000 q w :=by
    let Bκ:= (w:ℝ)^6*(c*∫ p':Space3,Tt p'); have h : 0<(w:ℝ):=Nat.cast_pos.mpr P; have hs : Tendsto (fun q:ℕ=> (q:ℝ)^6* acc (-10000) q w) atTop (𝓝 0):=by
        convert! (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 6 (10000*w) (by positivity)).comp (tendsto_natCast_atTop_atTop (R:=ℝ)) using 2; rename_i i; unfold acc; simp; ring_nf; simp -- tune
    filter_upwards [((by simpa using hs.mul_const Bκ : Tendsto (fun q:ℕ=> (q:ℝ)^6 *(acc (-10000) q w)* Bκ) atTop (𝓝 (0:ℝ)))).eventually (ge_mem_nhds (show (0:ℝ)<1 from zero_lt_one))] with q h; -- `q^6 as Nat cast?`
    apply le_of_mul_le_mul_right ?_ (Real.exp_pos (-(10000:ℝ)*q*w)); unfold Q acc; rw [inn, ←Real.exp_add, show (10000:ℝ)* q*w + -10000*q*w=0 from (by ring),Real.exp_zero]; apply le_trans (le_of_eq ?_) h; unfold Bκ acc; push_cast; ring
 have hz : ∀ᶠ q:ℕ in atTop, α+1 ≤32*q*D:= ((((tendsto_natCast_atTop_atTop (R:=ℝ)).const_mul_atTop (by norm_num: (0:ℝ)<32)).atTop_mul_const (Nat.cast_pos.mpr u)).eventually_ge_atTop _); -- tune type
 filter_upwards [hp,hz] with q hx ht i
 let X:= Q q; let U':= acc (-20000) q w; have hu':0≤U':= (Real.exp_pos _).le; let f:= songm (D:=D) (G:=G) L q w i; let Y:= U' *(X^2*‖i‖^2*c); have hy:0 ≤ Y:=by unfold Y; positivity; -- precedence
 change ‖∫ p' in Bᶜ, f p'‖ ≤ _; have hU : ∀ r':Space3,r'∈ Bᶜ→ ‖f r'‖ ≤ Y*Tt r':=by
    intro p' t0; let e:= ‖p'‖; let b:= Real.exp (α* e); have hv:r ≤ e:= (lt_of_not_ge (fun v=>t0 (mem_closedBall_zero_iff.mpr v))).le; have ht': b*levelE q D p' ≤ U'* Tt p':= by
        have hc:0<(D:ℝ):= Nat.cast_pos.mpr u; have he := (div_le_iff₀ hc).1 (t.trans hv); unfold b levelE U' Tt acc; rw [←Real.exp_add,←Real.exp_add]; apply Real.exp_monotone; -- tune linarith
        change α*e + _*e ≤ _ + _*e; nlinarith only [mul_le_mul_of_nonneg_right he (show 0≤(q:ℝ) by positivity),mul_le_mul_of_nonneg_right ht (show 0≤e from norm_nonneg p'), show 0≤(q:ℝ)*(w:ℝ) by positivity]
    have hg:= mul_le_mul_of_nonneg_right ((Complex.abs_re_le_norm (garnet G L p')).trans (V' p')) (show 0 ≤ levelE q D p' from (Real.exp_pos _).le); unfold f songm; rw [norm_mul,norm_mul,Real.norm_of_nonneg (show 0 ≤ levelE q D p' from (Real.exp_pos _).le),Real.norm_of_nonneg (sq_nonneg _)]; refine (mul_le_mul ((hg.trans ((mul_assoc c b _).le.trans (mul_le_mul_of_nonneg_left ht' g.le)))) (pow_le_pow_left₀ (norm_nonneg _) (lapping p' K _ _ _) _) (sq_nonneg _) (by unfold Tt; positivity)).trans_eq ?_; unfold Y X Q; ring
 have hI:Integrable Tt := exp3 1 (by norm_num); apply (norm_integral_le_of_norm_le (g:=fun r':Space3=>Y*Tt r') (hI.integrableOn.const_mul Y) (ae_restrict_of_forall_mem isClosed_closedBall.measurableSet.compl hU)).trans; rw [integral_const_mul]; refine (mul_le_mul_of_nonneg_left (setIntegral_le_integral (s:=(B)ᶜ) hI (ae_of_all _ fun x=> (Real.exp_pos _).le)) hy).trans ?_; -- tune μ
 let B':=∫ x,Tt x; have hm: (X^2)*(c*B')≤acc 10000 q w:= hx; change Y*B' ≤ _; calc
    _ = U'*((X^2)*(c*B'))*‖i‖^2:= by unfold Y; ring
    _ ≤ (U' * acc 10000 q w)*‖i‖^2:= by gcongr
    _ = _:= by unfold U' acc; rw [←Real.exp_add]; ring_nf
#print axioms outside
-- combine ⇒ α-rank certificate.Real coerc positivity restricted.H eventual, exp A∼4096qw. true Beam.Cluster.
lemma Horcrux (g:2000*w/D ≤ r) : ∀ᶠ q:ℕ in atTop,∃ W :PlansM (Stamp q w), page (Stamp q w)≤2*dim W ∧ ∀ i∈ W, acc (-4096) q w*‖i‖^2 ≤ gas (modelK K L q w) i:= by
 obtain ⟨U,p,t,v,hZ⟩:= budget_K u P; obtain ⟨e,h,wk⟩:=wicket_pay t u hZ
 have he:0<(D:ℝ):=Nat.cast_pos.mpr u; have ht:32*w/D ≤ r:= by exact le_trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num:(32:ℝ)≤2000) (show 0 ≤ (w:ℝ) by positivity)) he.le) g
 let A(q:ℕ):=acc (-2048) q w; let b:= (1/2:ℝ)*e^2*(lobby D/2); have hb:0<b:= by unfold b; have he:=lobby_p u; positivity
 have hw:Tendsto A atTop (𝓝 0):= by
    have ht:0<(w:ℝ):= Nat.cast_pos.mpr P; have hv:= Real.tendsto_exp_atBot.comp ((tendsto_natCast_atTop_atTop (R:=ℝ)).const_mul_atTop_of_neg (by nlinarith only [ht]: -(2048:ℝ)*w<0)); refine hv.congr (?_); intro i; simp only [A,acc,Function.comp_apply]; ring_nf
    -- rewrite simpler.M
 filter_upwards [launch_budget K L w, outside L H K u w P g, hw.eventually (ge_mem_nhds (half_pos hb))] with q y ψ a; obtain ⟨W,hW,l⟩:= retinue q w D u U t.measurableSet p v; refine ⟨W,hW,fun i hi=>?_⟩; -- tune notation Σ conflict
 have hp: acc (-4096) q w= A q*A q:=by unfold A acc; rw [←Real.exp_add]; ring_nf
 have hu: A q*b*‖i‖^2 ≤ ∫ p in B,songm (G:=G) (D:=D) L q w i p := le_trans (le_trans (le_of_eq (b:=A q*(1/2)*e^2*(lobby D/2*‖i‖^2)) (by unfold b; ring)) (mul_le_mul_of_nonneg_left (l i hi) (mul_nonneg (mul_nonneg (Real.exp_pos _).le (by norm_num)) (sq_nonneg _)))) (issueQ L H K u q w p t P wk h y ht i)
 obtain ⟨hf,Q0⟩:= bbl K L q w i y; let U':=∫ p in Bᶜ,songm (G:=G) (D:=D) L q w i p; have hy: -(acc (-4096) q w*‖i‖^2) ≤ U':= (abs_le.mp (le_trans (show |U'|≤ _ from ψ i) (mul_le_mul_of_nonneg_right (Real.exp_monotone (by nlinarith only [show 0 ≤ (q:ℝ)*(w:ℝ) by positivity] : (-10000:ℝ)*q*w ≤ -4096*q*w)) (sq_nonneg _)))).1
 rw [Q0, ←integral_add_compl isClosed_closedBall.measurableSet hf]; apply le_trans ?_ (add_le_add hu hy); rw [hp]; let t0:=A q; have ht:t0>0:= Real.exp_pos _; change t0*t0*‖i‖^2 ≤ t0*b*‖i‖^2+ -(t0*t0*‖i‖^2); change t0 ≤ b/2 at a; nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left a ht.le) (sq_nonneg ‖i‖)]
#print axioms Horcrux
end Midway
end YM.CF.Window.ArchiveK
