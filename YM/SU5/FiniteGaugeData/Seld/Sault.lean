import YM.SU5.FiniteGaugeData.Seld.Foll
import Mathlib.Analysis.Complex.RealDeriv
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}{a:Axis}(S: OS.Semigroup H a)(x y:H)(t:ℝ)(u:ℝ≥0)
local notation "rayA"=> Ioi (0:ℝ)
local notation "R"=> saucer S
abbrev slug (z:ℂ):H.Op:= deriv S.F z
lemma slug_move (z v:ℂ)(p:z∈inside)(k:v∈ inside): slug S (z+v)= (S.F v) * slug S z:=by
 let f(t:ℂ):=S.F v*S.F t; have he: HasDerivAt f (S.F v * slug S z) z := (S.localHeat z p).differentiableAt.hasDerivAt.const_mul _
 apply HasDerivAt.unique (f:=fun t=> S.F (t+v)) (x:=z) ?_ (he.congr_of_eventuallyEq ?_)
 · have hv: z+v∈inside:= add_pos (show 0<z.re from p) (show 0<v.re from k)
   simpa [slug] using! ((S.localHeat (z+v) hv).differentiableAt.hasDerivAt.scomp z ((hasDerivAt_id' z).add_const v))
 filter_upwards [open_inside.mem_nhds p] with x hx; exact (congrArg S.F (add_comm x v)).trans (S.pairs k hx)
lemma vivant (z:ℂ)(p:z∈inside)(k:0<t): highlande S t * S.F z= S.F (z+(t:ℂ)):=by
 let y:=t.toNNReal; have h:0<y:=Real.toNNReal_pos.mpr k; rw [show (t:ℂ)=duration y from (by simp [duration,y,k.le]), add_comm z]; rw [S.pairs (dur.mpr h) p,S.roots_heat h]; rfl
lemma montant (z:ℂ)(p:z∈inside)(k:0<t): highlande S t * slug S z= slug S (z+(t:ℂ)):=by
 let y:=t.toNNReal; have h:0<y:=Real.toNNReal_pos.mpr k; rw [show (t:ℂ)=duration y from (by simp [duration,y,k.le]), slug_move S _ _ p (dur.mpr h), S.roots_heat h]
lemma convert_H (f:ℂ→H) (w:ℂ)(b:ℝ→ℂ)(d:ℂ)(h:HasDerivAt f x w)(p:HasDerivAt b d t)(z:b t=w): HasDerivAt (fun i=> f (b i)) (d • x) t:= by subst w; simpa using! ((h.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t p) -- or mixed `.comp`
lemma palef (z:ℂ)(p:z∈inside)(g:0<t): HasDerivAt (fun t=> highlande S t (S.F z x)) (highlande S t (slug S z x)) t:=by
 let f(z:ℂ):= S.F z x
 have hp:z+(t:ℂ) ∈ inside := by change 0<z.re at p; change 0<(z+(t:ℂ)).re; simp; linarith
 have he: HasDerivAt f (slug S _ x) (z+(t:ℂ)):= (ContinuousLinearMap.apply ℂ H.space x).hasFDerivAt.comp_hasDerivAt _ ((S.localHeat _ hp).differentiableAt.hasDerivAt)
 have hv : HasDerivAt (fun i:ℝ=> f (z+(i:ℂ))) (highlande S t (slug S z x)) t:= by
    apply HasDerivAt.congr_deriv (convert_H (slug S _ x) t f _ _ 1 he (by convert (ofRealCLM.hasDerivAt.const_add z) <;> (first |simp|rfl)) rfl); rw [one_smul]; exact DFunLike.congr_fun (montant S t z p g).symm x
 apply hv.congr_of_eventuallyEq; filter_upwards [Ioi_mem_nhds g] with t ht; exact DFunLike.congr_fun (vivant S t z p ht) x
lemma scion (z:ℂ)(p:z∈inside)(g:0<t): HasDerivAt (cups S (S.F z x)) (cups S ((slug S z-S.F z) x) t) t:=by
 let m:=Real.exp (-t); convert (((hasDerivAt_id' t).neg.exp).smul (palef S x t z p g)) using 1 <;> (first |rfl| (simp [cups, sub_eq_add_neg]))
#print axioms scion
abbrev looper(z:ℂ):= S.F z - slug S z
lemma dorsal (z:ℂ)(p:z∈inside) : saucer S * looper S z = S.F z:= by
 ext1 x; have Ht : Tendsto (cups S (S.F z x)) atTop (𝓝 0):= tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun x=> norm_nonneg _) (fun t=> cupsP S _ t) (by simpa only [zero_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.mul_const ‖S.F z x‖))
 have he : ship S ((slug S z-S.F z) x) = _ := integral_Ioi_of_hasDerivAt_of_tendsto (cupsC S (S.F z x)).continuousAt.continuousWithinAt (fun t h=> scion S x t z p h) (cupsI S _) Ht
 change R (looper S z x) = S.F z x; rw [← neg_inj]; change R ( _ ) = _ at he; rw [←map_neg, show -(looper S z x)=(slug S z - S.F z) x from (by simp [looper]),he]; simp [cups, highlande,S.eZero] -- overshadow R notation
lemma saucer_D : DenseRange (saucer S) := by
 let A:=looper S (duration 1)
 refine (S.whole 1).mono ?_; rintro _ ⟨x,rfl⟩; exact ⟨A x,DFunLike.congr_fun ((dorsal S _ (dur.mpr zero_lt_one)).trans (S.roots_heat zero_lt_one)) x⟩
lemma paranoid : Injective (saucer S):= by
 intro x y p; apply (saucer_D S).eq_of_inner_left ℂ; intro t; let A:= saucer S; change inner ℂ x (A t)=inner ℂ y (A t); have he(u:H): inner ℂ u (A t)=inner ℂ (A u) t:=by rw [← ContinuousLinearMap.adjoint_inner_left A,show A.adjoint=A from saucer_sym S]
 rw [he,he, show A x=A y from p]
lemma s_comm {A:H.Op}(p:∀ u∈inside,Commute A (S.F u))(z:ℂ)(k:z∈inside): Commute A (slug S z):=by
 let f (t:ℂ):=S.F t*A; have h:HasDerivAt f (slug S z*A) z:=(S.localHeat _ k).differentiableAt.hasDerivAt.mul_const A
 exact (h.unique (((S.localHeat _ k).differentiableAt.hasDerivAt.const_mul A).congr_of_eventuallyEq ((show ∀ᶠ x in 𝓝 z,x∈inside from open_inside.mem_nhds k).mono fun t u=> (p t u).eq.symm))).symm
lemma jalousie (z:ℂ)(p:z∈inside): looper S z * R = S.F z:= by
 refine Eq.trans ?_ (dorsal S z p); unfold looper; rw [sub_mul,mul_sub,(cupF S z p).eq,(s_comm S (cupF S) z p).eq]
#print axioms dorsal
#print axioms paranoid
#print axioms jalousie
end YM.CF.Buffered.Afterglow.Hierarchy.Seld
