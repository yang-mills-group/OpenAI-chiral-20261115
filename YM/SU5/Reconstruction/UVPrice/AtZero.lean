import YM.SU5.Reconstruction.UVPrice.Entire
/-!
# One comparison per test eliminating all zero-energy far permissions. Abstract pair.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Roy
open Function Set Filter MeasureTheory Spectral Analysis Metric InnerProductSpace
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace ComplexConjugate
open YM.Multiplier Chirp CrossedFrame OS Semigroup Boundary Probe CF.Buffered.Afterglow.Tower MeshClock Germ SelectionAnalysis ConePrice Real Picket
variable {H Y : Hilbert} {a b : Axis} (S : OS.Semigroup H a)(T : OS.Semigroup Y b)
local notation "P" => S.ℚmeasure
local notation "μ" x:max=> (P).diagonal x
variable (t:b≠a)
local notation "B"=> cross a b t
variable (x:H)(p : IsCompact (Beneath S 0))
private lemma story_fix (u v:Cross a) (x y:H) : inner ℂ (S.U v x) (S.U u y)=inner ℂ x (S.U (u-v) y):= by
 have h := LinearIsometry.inner_map_map (f:= (⟨(S.U v).toLinearMap,fun x=> S.unitary v x⟩ : H.space →ₗᵢ[ℂ] H.space)) x (S.U (u-v) y)
 change inner ℂ (S.U v x) (S.U v (S.U (u-v) y))=_ at h; rw [← ContinuousLinearMap.comp_apply, ← S.space,add_sub_cancel] at h; exact h
private lemma investor (q:ℕ→ℂ→ℂ)(D:Set ℝ)(m:Dense D)(G:ℂ→ℂ)(p:Differentiable ℂ G)(e:ℝ)(δ:ℝ)(v:∀ n, AnalyticOnNhd ℂ (q n) inside)(u:∀ n,∀ z∈inside,‖q n z‖≤e) (s:∀ x∈D, 0<x→Tendsto (fun i=>q i (x:ℂ)) atTop (𝓝 (G (x+δ:ℝ)))) : ∀ z:ℂ,0<z.re→ ‖G (z+δ)‖≤ e:=by
 obtain ⟨f,h,b⟩:= Sail.limit_chance q open_inside (fun i z a=> (v i z a).differentiableAt.differentiableWithinAt) u
 let F(z:ℂ):= G (z+(δ:ℂ)); let r:= Ioo (0:ℝ) 2
 have h₁:AnalyticOnNhd ℂ F inside:= fun z _=> (p.comp ((differentiable_id).add_const (δ:ℂ))).analyticAt z
 have h₀ :MapsTo (fun x:ℝ=> (x:ℂ)) (Ioo (0:ℝ) 2) inside:= fun x h=> by change 0< Complex.re (x:ℂ); simpa using h.1
 have hs: EqOn f F inside:= by
   refine Sail.pioneer ((convex_halfSpace_gt Complex.reCLM.toLinearMap.isLinear 0).isPreconnected) (h₀ (show (1:ℝ)∈ r from ⟨zero_lt_one,by norm_num⟩)) _ _ (show (1:ℝ)∈ r from ?_) h h₁ ?_
   · exact ⟨zero_lt_one,by norm_num⟩
   have hf' : ContinuousOn (fun x:ℝ=> f (x:ℂ)) r:= h.continuousOn.comp Complex.continuous_ofReal.continuousOn h₀
   have hG :ContinuousOn (fun x:ℝ=> F (x:ℂ)) r:= h₁.continuousOn.comp Complex.continuous_ofReal.continuousOn h₀
   intro y hy
   haveI : (𝓝[r ∩ D] y).NeBot:= mem_closure_iff_nhdsWithin_neBot.mp (m.open_subset_closure_inter isOpen_Ioo hy)
   apply tendsto_nhds_unique (f:=fun i:ℝ=> f (i:ℂ)) ((hf' y hy).mono_left (nhdsWithin_mono _ (inter_subset_left (s:=r) (t:=D))))
   apply ((hG y hy).mono_left (nhdsWithin_mono _ inter_subset_left)).congr'
   filter_upwards [self_mem_nhdsWithin] with j hp
   have hb:= s j hp.2 hp.1.1
   rw [Complex.ofReal_add] at hb
   exact tendsto_nhds_unique (hb.mono_left (Ultrafilter.of_le atTop)) (b _ (h₀ hp.1))
 intro z hz; change ‖F z‖ ≤ _; rw [←hs hz]; exact le_of_tendsto_of_tendsto' (b z hz|>.norm) tendsto_const_nhds (fun i=>u i z hz)

variable {D:Set ℝ}(d:Dense D)(τ:ℝ)(s:ℕ→ℝ≥0)(ht:Tendsto s atTop atTop) (l r:Y)
open Complex
section
-- compare shifted relative ±τ before and after. stamps only!
variable (u : ∀ n,∀ z∈D, 0<z → inner ℂ (S.U ((-τ) • cross a b t) x) (S.U (z • cross a b t) (S.E (s n) (S.U (τ • cross a b t) x)))= inner ℂ l (T.E z.toNNReal (T.U (((s n):ℝ) • cross b a t.symm) r)))
include t d s ht u p T
lemma frostBill (y:ℝ) : S.U (y • cross a b t) (cue S x)=cue S x:= by
 obtain ⟨R,r₀,r'⟩:= bdd_beneath S 0 p b; let X:= cue S x; let G:= reward S x b R
 let Z := cross a b t; let Z':= cross b a t.symm
 let A(n:ℕ):= (T.U (((s n):ℝ) • Z') r:Y); let L(n:ℕ):= (innerSL ℂ (E:=Y.space) l).comp (ContinuousLinearMap.apply ℂ Y.space (A n))
 let f(n:ℕ)(z:ℂ):= L n (T.F z)
 let e:=‖l‖ * ‖r‖; let δ:=2*τ
 have h1(n): AnalyticOnNhd ℂ (f n) inside:= fun z g=> (((L n).analyticAt _).comp (T.localHeat _ g))
 have h2(n)(z:ℂ)(p:z∈inside): ‖f n z‖≤e:= (norm_inner_le_norm l (T.F z (A n))).trans (mul_le_mul_of_nonneg_left (by refine le_trans ?_ (show ‖A n‖≤ ‖r‖ from (T.unitary ..).le); exact ((T.F z).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (T.norm_row p))) (norm_nonneg _)) -- tune indentation
 have h3(z:ℝ)(h:z∈D)(p:0<z):Tendsto (fun i=> f i (z:ℂ)) atTop (𝓝 (G (z+δ:ℝ))):= by
   let ξ:= S.U (τ • Z) x; let l':= S.U ((-τ) • Z) x; let E:= S.U (z • Z)
   have v(i:ℕ): f i (z:ℂ)=inner ℂ l' (E (S.E (s i) ξ)):=by
      change inner ℂ l (T.F (z:ℂ) (A i)) = _
      rw [show T.F (z:ℂ)=T.E z.toNNReal from ?_]; exact (u i z h p).symm
      rw [← T.roots_heat (Real.toNNReal_pos.mpr p)]; unfold duration; rw [Real.coe_toNNReal _ p.le]
   let F(i:ℕ):= inner ℂ l' (E (S.E (s i) ξ)); simp_rw [v]
   have hz : Tendsto F atTop (𝓝 (inner ℂ l' (E (cue S ξ)))):= tendsto_const_nhds.inner ((E.continuous.continuousAt).tendsto.comp ((truth S ξ).comp ht))
   convert hz using 1
   rw [show G (z+δ:ℝ) = _ from on_fullReal S r₀ x (z+δ) t r']
   congr 1
   have stay (u:Cross a)(x): cue S (S.U u x)= S.U u (cue S x):= DFunLike.congr_fun (((toe_pays S).jointly (costU S u)).eq) x
   have hy: cue S (cue S x)= cue S x:= DFunLike.congr_fun (cue_project S).1.eq _
   dsimp only [E,l',ξ]; rw [stay,story_fix]
   rw [← ContinuousLinearMap.comp_apply (S.U (z • Z- -τ • Z)) (S.U (τ • Z)),← S.space, show z • Z - -τ • Z + τ • Z=(z+δ) • Z from ?_]
   · nth_rw 1 [← show (cue S).adjoint=(cue S) from (cue_project S).2]
     rw [ContinuousLinearMap.adjoint_inner_left,stay,hy]
   · unfold δ; rw [neg_smul, add_smul,two_mul,add_smul]; abel
 let C:= max 1 (δ+1); have h:0<C:= zero_lt_one.trans_le (le_max_left ..)
 have hz(v:ℂ)(h:C≤ v.re): ‖G v‖≤e:= by
   have he := investor f D d G (interest S r₀ x) e δ h1 h2 h3 (v-(δ:ℂ)) (by simp; linarith [show δ+1 ≤ C from le_max_right ..]); simpa using he
 have he:= same_pay h r₀ (interest S r₀ x) (bill_sym S r₀ x) ⟨‖X‖^2,sq_nonneg _, ready_bound S r₀ x⟩ hz
 have hv: inner ℂ X (S.U (y • Z) X)=inner ℂ X X:=by rw [← on_fullReal S r₀ x y t r', he, show (0:ℂ)=(↑(0:ℝ)) from by simp, on_fullReal S r₀ x 0 t r',zero_smul,S.uZero]; rfl
 apply sub_eq_zero.mp; apply norm_eq_zero.mp; suffices g : ‖X-S.U (y • Z) X‖^2=0 by rw [norm_sub_rev]; nlinarith [g]
 rw [norm_sub_sq (𝕜:=ℂ),hv,inner_self_eq_norm_sq,S.unitary]; ring
end
end YM.Roy
