/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SU5.Registration.LineUp.Sunkist
import YM.SU5.Registration.LineUp.Pocket
/-!
 # Testing Ward identity even before Euclidean smoothness is established.
 via compact cutoffs & local estimates in M10 helio_cont+charges & smoothing.
 Adapts YM/Work/C07 chain. ONLY need boost derivative real on finite path spendings.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinWFixed
open Set Boundary Mink Function Filter MeasureTheory
open Work.C07 (scaled_imag test_one testField test_imag integral_orbit fold_derivative fold_smooth orbit_image orbit scaledTimes stretchY foldE scaled_strict_imag)
open scoped Topology ContDiff Convolution Matrix.Norms.Frobenius BigOperators
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
namespace HelioRoof
open Complex Courts Ortho
private def actionOnTuple {n : ℕ} (p : Points n) : M4 →L[ℝ] Points n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => points fun i => M4.move A (p i)
      map_add' := fun A B => PiLp.ext fun i => by
        change Matrix.toEuclideanLin (A+B) (p i) =
          Matrix.toEuclideanLin A (p i) + Matrix.toEuclideanLin B (p i)
        rw [map_add]; rfl
      map_smul' := fun c A => PiLp.ext fun i => by
        change Matrix.toEuclideanLin (c • A) (p i) = c • Matrix.toEuclideanLin A (p i)
        rw [map_smul]; rfl }

private lemma turnsTuple {n : ℕ} (x : Points n) (Ω : Ortho.Skew) :
    HasDerivAt (fun t : ℝ => Points.move (Ortho.oneParameter Ω t) x)
      (points fun i => M4.move Ω.val (x i)) 0 := by
  have hA : HasDerivAt (fun t => NormedSpace.exp (t • Ω.val)) Ω.val (0 : ℝ) := by
    simpa using! (hasDerivAt_exp_smul_const Ω.val (0 : ℝ))
  exact (actionOnTuple x).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hA

abbrev easter (a:SpaceAxis) := Ortho.plane timeAxis a.castSucc
-- coordinate identity at cost
variable {T : EuLeaflet V}(R:Courts V)
section flow
variable (h : ∀ (x:Points n)(v:Fin n→V), ContDiffAt ℝ 1 (fun x=> T n x v) x) (e : ∀ (a:SpaceAxis)(r:ℝ)(x:Points n)(v: Fin n→V), T n (Points.move (Ortho.oneParameter (easter a) r) x) (R.eu (Ortho.oneParameter (easter a) r) ∘ v)=T n x v)
include h e
abbrev Cosm (R:Courts V)(a:SpaceAxis) (v:Fin n→V)(i:Fin n) := update v i ((-I) • R.planeDuty a (v i))
abbrev Upper (R:Courts V)(a:SpaceAxis) (v:Fin n→V)(i:Fin n) := update v i (R.planeDuty a (v i))
lemma along_ramp (x:Points n)(a:SpaceAxis)(v:Fin n→V) : fderiv ℝ (fun x=> T n x v) x (points (fun i=> M4.move (easter a).val (x i))) = -(∑ i,T n x (Upper R a v i)):=by
 let Ω:= easter a; let Q (t:ℝ):= oneParameter Ω t; let p:=fun t:ℝ=> R.eu (Q (-t)) ∘ v
 have he (t:ℝ): T n (Points.move (Q t) x) v=T n x (p t):=by
    have hx: (R.eu (Q t)) ∘ p t=v:=by
       funext i; simp_rw [p, Function.comp_apply, Q,← R.euMul _ _ (proper_param Ω _) (proper_param Ω _), ← parameter_add, add_neg_cancel, oneParameter_zero, R.eu1]
    nth_rw 1 [← hx]; exact e ..
 have hv: p 0=v:= funext fun i=> by simp [p,Q,R.eu1,oneParameter_zero]
 let f(i):= -(R.planeDuty a (v i)); have hu:= GearDeriv.charge (T n x) p f (fun i=> GearDeriv.back (R.euD a (v i)))
 have hg := (((h x v).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 (turnsTuple x Ω) (show x=Points.move (oneParameter Ω 0) x from PiLp.ext (fun i=> by simp [oneParameter_zero])))
 change HasDerivAt (fun t=> T n (Points.move (Q t) x) v) _ _ at hg; rw [hv] at hu
 simp_rw [he] at hg; simp_rw [f, MultilinearMap.map_update_neg, Finset.sum_neg_distrib] at hu
 exact HasDerivAt.unique hg hu
private lemma paint_flow (x:Points n)(a:SpaceAxis)(y:Heights n)(v:Fin n→V)(w:ℝ) :
  fderiv ℝ (fun p=> T n (foldE y w p) v) x (orbit a y w x)= -(((w:ℂ)*I) * ∑ i, T n (foldE y w x) (Cosm R a v i)):= by
  let q := foldE y w x
  let Ω := Ortho.plane timeAxis a.castSucc
  have hd := (h q v).differentiableAt (by simp)
  have H := ((hd.hasFDerivAt).comp x (fold_derivative y w x)).fderiv
  change fderiv ℝ ((fun x => T n x v) ∘ foldE y w) x _ = _
  rw [H, ContinuousLinearMap.comp_apply, orbit_image, map_smul,show fderiv ℝ _ _ (points _) = _ from along_ramp R h e q a v] -- rfl coords
  simp_rw [Cosm, MultilinearMap.map_update_smul, smul_eq_mul, ← Finset.mul_sum, real_smul]
  have he (z b : ℂ) : -(z*I*(-I*b)) = z * -b := by
    calc
      _ = z * (I*I) * b := by ring
      _ = _ := by rw [I_mul_I]; ring
  exact (he _ _).symm
def foldedΩ (T: EuLeaflet V)(a:SpaceAxis)(y:Heights n)(v:Fin n→V)(f:Joint n)(w:ℝ)(x:Points n):=
 T n (foldE y w x) v * testField a y ((w:ℂ)*I) f x - ((w:ℂ)*I) * (∑ i,T n (foldE y w x) (Cosm R a v i)) * f x
lemma pressed (a:SpaceAxis)(y:Heights n)(v:Fin n→V)(f:Joint n)(w:ℝ)(hK:HasCompactSupport ⇑f) : (∫ p in tsupport f, foldedΩ R T a y v f w p)=0:=by
 let u (p : Points n) := T n (foldE y w p) v
 have hU (p) : ContDiffAt ℝ 1 u p := (h _ v).comp p ((fold_smooth y w).of_le (by simp)).contDiffAt
 let g (p : Points n) := u p * f p
 have hG : tsupport g ⊆ tsupport f := tsupport_mul_subset_right
 have hc : HasCompactSupport g := hK.of_isClosed_subset (isClosed_tsupport _) hG
 have hg : ContDiff ℝ 1 g := (contDiff_iff_contDiffAt.mpr hU).mul (f.smooth 1)
 calc
   _ = ∫ p in tsupport f, fderiv ℝ g p (orbit a y w p) := by
      apply setIntegral_congr_fun (isClosed_tsupport _).measurableSet; intro p hp
      rw [foldedΩ, test_imag]; change u p * _-_ = fderiv ℝ (fun z => u z * f z) p (orbit a y w p)
      have hVp : fderiv ℝ u p (orbit a y w p) = _ := paint_flow R h e p a y v w
      rw [fderiv_fun_mul ((hU p).differentiableAt (by simp)) f.differentiableAt]; simp [hVp]; ring
   _ = (∫ p, fderiv ℝ g p (orbit a y w p)) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero; intro p hp; rw [fderiv_of_notMem_tsupport ℝ (fun h => hp (hG h))]; rfl
   _ = 0 := integral_orbit a y w hg hc
end flow
-- pass to `foldedΩ` of unsmoothed in norm. compact costs at this test.
private lemma follows_integ {X:Type*} {u:X→Points n→ℂ}{v:Points n→ℂ}{K:Set (Points n)}(hK:IsCompact K){F:Filter X}(h: ∀ x x',ContinuousAt (u x) x')(p: Continuous v)(q: ∀ x∈ K,Tendsto (Function.uncurry u) (F ×ˢ 𝓝 x) (𝓝 (v x))) : Tendsto (fun x=>∫ y in K,u x y) F (𝓝 (∫ y in K,v y)):=by
 refine Metric.tendsto_nhds.mpr (fun ε he=>?_); let m:=volume.real K; have hm:0≤ m:= ENNReal.toReal_nonneg;
 let e:= ε/(m+1); have hx:0<m+1:=by linarith
 have hu:0<e:=div_pos he hx
 have ht:∀ᶠ z:X × (Points n) in F ×ˢ 𝓝ˢ K, ‖u z.1 z.2-v z.2‖≤ e:=by
    refine hK.mem_prod_nhdsSet_of_forall (fun x w=>?_); apply (((q x w).sub ((p.tendsto x).comp (tendsto_snd (f:=F)))).norm).eventually (show ∀ᶠ x in 𝓝 ‖v x-v x‖, x≤e from ge_mem_nhds (by simpa using hu)) -- tune
 have hp:=ht.curry; filter_upwards [hp] with x v'; rw [dist_eq_norm, ← integral_sub ((continuous_iff_continuousAt.mpr (h x)).continuousOn.integrableOn_compact hK) (p.continuousOn.integrableOn_compact hK)]; refine (norm_setIntegral_le_of_norm_le_const hK.measure_lt_top (fun z hz=> v'.self_of_nhdsSet z hz)).trans_lt ?_
 change e*m<ε; linarith [show e*(m+1)=ε from div_mul_cancel₀ _ hx.ne']
variable {F: InkWaves V}(p:R.Carriage F)(t:F.Region)
def seenF (F:InkWaves V)(q:Fin n→V)(y:Heights n)(z:ℂ)(x:Points n):= F.F n (scaledTimes y z x) (Boundary.trace x) q
def errorF (F:InkWaves V)(R:Courts V)(a:SpaceAxis)(y:Heights n)(v:Fin n→V)(f:Joint n) (z:ℂ)(p:Points n):=
 seenF F v y z p*testField a y z f p-z*(∑ i, seenF F (Cosm R a v i) y z p)*f p
lemma test_cont (a:SpaceAxis)(y:Heights n)(z:ℂ)(f:Joint n) : Continuous (testField a y z f) := by
 unfold testField scaledTimes; refine continuous_finsetSum _ (fun i _=>Continuous.add (Continuous.mul ?_ (Bid.realTerm i timeAxis f).continuous) (Continuous.mul ?_ (Bid.realTerm i a.castSucc f).continuous)) <;> fun_prop
include p t
lemma error_imag (a:SpaceAxis)(y:Heights n)(v:Fin n→V)(f:Joint n)(w:ℝ)(hK:HasCompactSupport ⇑f) (h:∀ p∈tsupport f, scaledTimes y ((w:ℂ)*I) p ∈ strict n):
 (∫ p in tsupport f, errorF F R a y v f ((w:ℂ)*I) p)=0:=by
 let K:= tsupport f; let K':= foldE y w '' K; have he:IsCompact K':= IsCompact.image hK (fold_smooth y w).continuous; have hx(p)(h':p∈K): foldE y w p ∈ Wheeled n:=by
    rw [Wheeled, Set.mem_preimage,foldE,line_place']; exact (scaled_strict_imag y w p).mp (h _ h')
 have hc:K' ⊆ conf n:=by rintro x ⟨r,u,rfl⟩; exact wheel_at (hx r u)
 obtain ⟨r,hr,u⟩: ∃ r:ℝ,0<r ∧ ∀ x∈ K',faceRoof r x=1:=(Eventually.and (f:=𝓝[>] (0:ℝ)) self_mem_nhdsWithin (roof_enough he hc)).exists
 have hk (q:Fin n→V)(x:Points n)(h':x∈ K) : seenF F q y ((w:ℂ)*I) x=awning r R F n (foldE y w x) q:=by
    rw [seenF,awning, u _ ⟨x,h',rfl⟩, ofReal_one, one_smul, helio_local p t _ (hx x h'),scaled_imag,InkWaves.entrance]; simp_rw [foldE, line_place',trace_place'] -- order
 let V₀(k:ℕ):ℝ:=(1/2)^k; have t₀(k):0<V₀ k:=by positivity
 have hV:Tendsto V₀ atTop (𝓝 0):=tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num); let Tu:=awning r R F; let T (k):=pigment (t₀ k) p t r hr; let Y(T:EuLeaflet V):=foldedΩ R T a y v f w; let Y₀(k):= Y (T k)
 have Eq:(∫ p in K, Y Tu p)=∫ p in K,errorF F R a y v f ((w:ℂ)*I) p:=by
    apply setIntegral_congr_fun (isClosed_tsupport _).measurableSet; intro x h'; simp_rw [errorF,hk _ x h']; rfl
 rw [← Eq]; have H (T:EuLeaflet V)(h:∀ v:Fin n→V,Continuous (fun x=> T n x v)):Continuous (Y T):=by
    unfold Y foldedΩ; refine (( (h v).comp (fold_smooth y w).continuous).mul ?_).sub (( (continuous_finsetSum _ (fun i _=> (h (Cosm R a v i)).comp (fold_smooth y w).continuous)).const_mul _).mul (f.continuous)); exact test_cont a y _ f
 have hY (x:Points n): Tendsto (fun p:ℕ×Points n=> Y₀ p.1 p.2) (atTop ×ˢ 𝓝 x) (𝓝 (Y Tu x)):=by
    have hu(v:Fin n→V): Tendsto (fun p:ℕ×Points n=> T p.1 n (foldE y w p.2) v) (atTop ×ˢ 𝓝 x) (𝓝 (Tu n (foldE y w x) v)):= pigment_gain p t (V₀ ∘ Prod.fst) (fun z=>t₀ z.1) _ (hV.comp tendsto_fst) _ (((fold_smooth y w).continuous.tendsto x).comp tendsto_snd) r hr v
    let A:= testField a y ((w:ℂ)*I) f; have hm:Continuous A:=test_cont a y _ f
    exact ((hu v).mul ((hm.tendsto _).comp tendsto_snd)).sub (( (tendsto_finsetSum _ (fun i _=> hu (Cosm R a v i))).const_mul _).mul ((f.continuous.tendsto _).comp tendsto_snd))
 have hy := follows_integ (u:=Y₀) (v:=Y Tu) hK (F:=atTop) (fun k x=> (H (T k) (fun i=> (pigment_smooth (t₀ k) p t i r hr).continuous)).continuousAt) (H Tu (fun i=> awning_cont hr p t i)) (fun x _=> hY x)
 apply tendsto_nhds_unique hy; refine tendsto_const_nhds.congr (fun k=>?_); exact (pressed R (T:=T k) (fun x i=> ((pigment_smooth (t₀ k) p t i r hr).of_le (by simp)).contDiffAt) (fun a r' x v=> pigment_turn (t₀ k) p t x _ (proper_param ..) v r hr) a y v f w hK).symm
end HelioRoof
end YM.SatinWFixed
open YM.SatinWFixed HelioRoof
#print axioms error_imag
