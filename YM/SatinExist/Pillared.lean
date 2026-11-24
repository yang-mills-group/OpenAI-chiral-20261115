/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SatinExist.Angular
import YM.SU5.Reconstruction.Vermont.Seam

set_option autoImplicit false
set_option maxHeartbeats 240000
noncomputable section
namespace YM.SatinJets
open Function Filter Metric InnerProductSpace Set Complex MeasureTheory Measure
open Analysis Boundary Spectral OS.Semigroup LineDeriv
open scoped NNReal ENNReal Topology BigOperators InnerProductSpace ComplexOrder Classical
variable {H:Hilbert} {ι:Type} [DecidableEq ι][Fintype ι]
private lemma fromInner {D : Hilbert} {f g : ℂ → D} {c : ℂ}
    (hf : DifferentiableAt ℂ f (star c)) (hg : DifferentiableAt ℂ g c) :
    DifferentiableAt ℂ (fun d => inner ℂ (f (star d)) (g d)) c := by
  have hs : Tendsto (star : ℂ → ℂ) (𝓝[≠] c) (𝓝[≠] star c) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact (continuous_star.tendsto c).mono_left nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin] with d hd
    exact fun he => hd (star_injective he)
  let w : ℂ := inner ℂ (deriv f (star c)) (g c)+inner ℂ (f (star c)) (deriv g c)
  suffices H : HasDerivAt (fun d => inner ℂ (f (star d)) (g d)) w c from H.differentiableAt
  apply hasDerivAt_iff_tendsto_slope.mpr
  have h₁ := (hf.hasDerivAt.tendsto_slope.comp hs).inner (𝕜:=ℂ)
    (hg.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s:={c}ᶜ)))
  have h₂ := (tendsto_const_nhds (x:= f (star c))).inner (𝕜:=ℂ) hg.hasDerivAt.tendsto_slope
  refine (h₁.add h₂).congr' (Eventually.of_forall fun d => ?_)
  simp [slope_def_module,inner_smul_left,inner_smul_right,inner_sub_left,inner_sub_right]; ring
private lemma find_r (f:ℂ→ℂ)(h:Continuous f)(p:AnalyticOnNhd ℂ f inside)(v:f 1≠0){a b:ℝ}(u:a<b):∃ t∈ Set.Ioo a b,f (sideways t) ≠0:=by
 -- one arc. Adapt seam argument
 by_contra! he
 let U:= {x:ℂ| x.im∈ Ioo (-b) (-a)}; let V:= {x:ℂ|x.re<0}; obtain ⟨s,tA,tB⟩:= exists_between (neg_lt_neg u); let z₁:ℂ:=⟨-1,s⟩; let z₂:ℂ:=⟨1,s⟩; have a1:z₁ ∈ U:= ⟨tA,tB⟩; have a2:z₂ ∈ U:= ⟨tA,tB⟩
 have hP:IsOpen V:= isOpen_lt continuous_re continuous_const; have hU:IsOpen U:= isOpen_Ioo.preimage continuous_im; have k1:z₁∈ V:= show (-1:ℝ)<0 by norm_num
 have k2:z₂∈inside:=show (0:ℝ)<1 by norm_num
 let g(z:ℂ):= if 0< z.re then f z else 0
 have e1 : ∀ x∈V,g =ᶠ[𝓝 x] 0:= fun x v=> (show ∀ᶠ i in 𝓝 x,i∈ V from hP.mem_nhds v).mono fun _ h=> if_neg (not_lt.mpr (show _<_ from h).le)
 have e2 : ∀ x∈inside,g =ᶠ[𝓝 x] f:= fun x v=> (show ∀ᶠ i in 𝓝 x,i∈ inside from open_inside.mem_nhds v).mono fun _ h=> if_pos h
 have hc : ContinuousOn g U:= by
   intro x v; rcases lt_trichotomy x.re 0 with v0|v0|v0
   · exact ((continuousAt_const (y:=(0:ℂ))).congr (e1 x v0).symm).continuousWithinAt
   · have hz:g x=0:=if_neg (not_lt.mpr v0.le)
     have hv : f x=0 := by
       have ht:x.im∈ Set.Ioo (-b) (-a):=v
       refine Eq.trans (congrArg f (show x=sideways (-x.im) from ?_)) (he _ ?_) -- he binders
       · apply Complex.ext <;> simp [sideways,Complex.mul_im,v0]
       exact ⟨by linarith only [ht.2],by linarith only [ht.1]⟩
     apply Metric.tendsto_nhds.mpr; intro ε p; filter_upwards [(h.tendsto x |>.mono_left (nhdsWithin_le_nhds (s:=U))).eventually (ball_mem_nhds _ p)] with y hy
     rw [hv] at hy; rw [hz]; unfold g; split; exact hy; simpa using p
   exact (h.continuousAt.congr (e2 x v0).symm).continuousWithinAt
 have ha:AnalyticOnNhd ℂ g U:= by
    apply DifferentiableOn.analyticOnNhd _ hU; apply Lens.seam_cement (t:=0) _ hc hU; intro z q r; rcases lt_or_gt_of_ne r with w|w
    · exact DifferentiableAt.congr_of_eventuallyEq (differentiableAt_const _) (e1 z w)
    exact (p z w).differentiableAt.congr_of_eventuallyEq (e2 z w)
 have h0:EqOn g 0 U:= ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero ((show Convex ℝ U from (convex_halfSpace_gt Complex.imCLM.toLinearMap.isLinear _).inter (convex_halfSpace_lt Complex.imCLM.toLinearMap.isLinear _)).isPreconnected) a1 (e1 z₁ k1)
 apply v; exact p.eqOn_zero_of_preconnected_of_eventuallyEq_zero ((convex_halfSpace_gt Complex.reCLM.toLinearMap.isLinear 0).isPreconnected) k2 ((e2 z₂ k2).symm.trans ((show ∀ᶠ i in 𝓝 z₂,i∈ U from hU.mem_nhds a2).mono fun x k=>h0 k)) (show (1:ℂ)∈ inside from (show (0:ℝ)<1 from zero_lt_one))

-- avoid needing common test exponent changes. carry exact scale of each field (even if pref undefined at 0)
lemma coined (f:ℂ→ Matrix ι ι ℂ)(h:∀ i j:ι,Continuous (fun k=>f k i j))(p:∀ i j:ι,AnalyticOnNhd ℂ (fun k=>f k i j) inside)
    (v:(f 1).det≠0)(g:∀ i:ι,f 1 i i≠0){a b:ℝ}(t:a<b):∃ s∈ Set.Ioo a b,(f (sideways s)).det ≠0 ∧ ∀ i:ι,f (sideways s) i i≠0:=by
 let F(z:ℂ):= (f z).det * ∏ i, f z i i
 have ha : AnalyticOnNhd ℂ (fun z=> (f z).det) inside:=by
    simp_rw [Matrix.det_apply']; intro z hz
    exact Finset.analyticAt_fun_sum _ (fun i _=> analyticAt_const.mul (Finset.analyticAt_fun_prod _ (fun j _=> p _ _ z hz))) -- inspect prod names
 obtain ⟨s,h,z⟩:=find_r F ((show Continuous f from continuous_pi fun i=> continuous_pi fun j=> h i j).matrix_det.mul (continuous_finsetProd _ fun i _=> h i i)) (ha.mul (fun _ hz=> Finset.analyticAt_fun_prod _ fun i _=> p i i _ hz)) (mul_ne_zero v (Finset.prod_ne_zero_iff.mpr fun i _ => g i)) t
 obtain ⟨l,w⟩:= mul_ne_zero_iff.mp z; exact ⟨s,h,l, fun i=> Finset.prod_ne_zero_iff.mp w i (Finset.mem_univ _)⟩

-- determinant with scalars
variable (A B:ι→ℂ)
def desk (P Q:ι→H.space) : Matrix ι ι ℂ:= Matrix.of (fun i j=>inner ℂ (P i) (Q j))
lemma desk_c (P Q:ι→H):desk (H:=H) (fun i=> A i • P i) (fun i=> B i • Q i) = Matrix.diagonal (fun i=> star (A i))* desk (H:=H) P Q * Matrix.diagonal B:=by
 ext i j; simp only [Matrix.mul_diagonal, Matrix.diagonal_mul,desk,Matrix.of_apply,inner_smul_left,inner_smul_right]; change B j * (star _ * _)=_; ring

variable {S:OS.Semigroup H timeAxis} {Y:ι→ℝ→ H.space} (W:ι→ VacuumVector H)

/-- Wick bridge ON the two fixed normalized tests. On the RIGHT sign
    of both ballots. Scalars included as normalized factor z^m,
    might vanish at 0; no query at zero λ required.
    Does NOT allocate local operators, only these vacuum-seam vectors. -/
structure WickLeg (P Q:ι→H.space) (f g:Probe E4) : Prop where
 legs : ∃ p q:ι→ℂ→H.space, (∀ i,Continuous (p i) ∧ Continuous (q i)) ∧
   (∀ i,AnalyticOnNhd ℂ (p i) inside ∧ AnalyticOnNhd ℂ (q i) inside) ∧
    ∃ m n:ι→ℕ,(∀ i,p i 1=P i ∧ q i 1=Q i) ∧
     (∀ (z:ℂ),0≤z.re →∀ i, Tendsto (fun t:ℝ=> z^(m i) • fareR S (-1) f (Y i t) z) (𝓝[>] 0) (𝓝 (p i z)) ∧ Tendsto (fun t:ℝ=> z^(n i) • fareR S 1 g (Y i t) z) (𝓝[>] 0) (𝓝 (q i z))) ∧
     ∀ r:ℝˣ,∀ i, p i (star (sideways r))= (star (sideways r)^(m i)) • W i (inFlow r f) ∧
                  q i (sideways r)=(sideways r ^(n i)) • W i (inFlow r g)
variable (f g:Probe E4)
abbrev latePoint (S:OS.Semigroup H timeAxis) (F:ℝ→H.space) (f:Probe E4)(σ:ℝ):H:=
    ∫ x:E4,f x • S.U (SEP timeAxis x) (F (σ * x timeAxis))
omit [DecidableEq ι] [Fintype ι] in
lemma WickLeg.earn (u:HasCompactSupport ⇑f)(v: HasCompactSupport ⇑g)
    (a:charges timeAxis (-1) f)(b:charges timeAxis 1 g)(h:∀ i,Rim S (Y i) (W i))(p:∀ i, VacuumPower (M:=H) (Y i))(k:∀ i,Positive S (Y i)):
    WickLeg (S:=S) (Y:=Y) W (fun i=>latePoint S (Y i) f (-1)) (fun i=>latePoint S (Y i) g 1) f g:=by
 choose m P hc he hm pg ht using fun i=> awarded S f (-1) u a (p i) (k i) (h i)
 choose n Q hd hf hn qg hv using fun i=> awarded S g 1 v b (p i) (k i) (h i)
 let A(i:ι):ℂ:= (-1:ℂ)^m i
 have hp(i): A i ≠ 0:= by unfold A; positivity
 refine ⟨⟨fun i z=> (A i)⁻¹ • P i z,Q,fun i=>⟨(hc i).const_smul _,hd i⟩,fun i=>⟨analyticOnNhd_const.smul (he i),hf i⟩,m,n,?_,?_,?_⟩⟩
 · intro i; simp only [hm,hn, ofReal_neg,ofReal_one,one_pow,one_smul]; exact ⟨inv_smul_smul₀ (hp i) _,trivial⟩
 · intro z Z i; constructor
   · apply ((pg i z Z).const_smul (A i)⁻¹).congr
     intro t; rw [mul_pow,ofReal_neg,ofReal_one,mul_comm _ ((-1:ℂ)^(m i)),mul_smul,inv_smul_smul₀ (hp i)]
   simpa only [ofReal_one,mul_one] using qg i z Z
 intro r i; refine ⟨?_,?_⟩
 · have hb: (star (sideways r))=sideways (-(r:ℝ)):= by simp [sideways]
   dsimp only; rw [hb,ht i (-(r:ℝ)) r (by ring), mul_pow,ofReal_neg,ofReal_one,mul_comm _ ((-1:ℂ)^(m i)),mul_smul,inv_smul_smul₀ (hp i)]
 rw [hv i (r:ℝ) r (by ring),ofReal_one,mul_one]

lemma WickLeg.sights {P Q:ι→H}(H':WickLeg (S:=S) (Y:=Y) W P Q f g)
    (p:(desk (H:=H) P Q).det ≠0)(x:∀ i, inner ℂ (P i) (Q i) ≠0){a b:ℝ}(t:a<b)(u:0≤a):
    ∃ s:ℝˣ,(s:ℝ)∈ Set.Ioo a b ∧
      let A(s:ℝˣ):=desk (H:=H) (fun i=> W i (inFlow s f)) (fun i=> W i (inFlow s g)); (A s).det≠0 ∧ ∀ i,A s i i ≠0:=by
 obtain ⟨q,r,h,h',m,n,h0,_,T⟩:= H'.legs
 let F(z:ℂ):= desk (H:=H) (fun i=> q i (star z)) (fun i=> r i z)
 have ht:F 1= desk (H:=H) P Q:=by simp_rw [F,star_one,fun i=> (h0 i).1,fun i=> (h0 i).2]
 have he(i j:ι) : AnalyticOnNhd ℂ (fun z=> F z i j) inside:=by
   apply DifferentiableOn.analyticOnNhd _ open_inside; intro y p
   exact (fromInner (D:=H) (((h' i).1 (star y) p).differentiableAt) (((h' j).2 y p).differentiableAt)).differentiableWithinAt
 have hx : ∀ i,F 1 i i≠0:=by rw [ht]; exact x
 obtain ⟨s,hS,d,g0⟩:= coined F (fun i j=> ((h i).1.comp continuous_star).inner (h j).2) he (show _ from (by rw [ht]; exact p)) hx t
 let w:=Units.mk0 s (show s ≠ 0 from (u.trans_lt hS.1).ne'); let E:= desk (H:=H) (fun i=> W i (inFlow w f)) (fun i=> W i (inFlow w g))
 let D(i:ι):= star (sideways s)^(m i); let J(i:ι):=sideways s^(n i); have ha: F (sideways s)=Matrix.diagonal (fun i=>star (D i))*E*Matrix.diagonal J:=by
    unfold F; simp_rw [show s=(w:ℝ) from rfl,fun i=> (T w i).1,fun i=> (T w i).2]; exact desk_c D J _ _
 rw [ha,Matrix.det_mul, Matrix.det_mul] at d
 simp_rw [ha,Matrix.mul_diagonal,Matrix.diagonal_mul] at g0
 exact ⟨w,hS, (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp d).1).2, fun i=> (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (g0 i)).1).2⟩
end YM.SatinJets
