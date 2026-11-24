import YM.SU5.Reconstruction.Trap.Ray
/-!
# Geometric spectra continuation: build at one crossing
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Picket
open Function Set Filter MeasureTheory Spectral Analysis Metric
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
open YM.Multiplier Chirp CrossedFrame OS Semigroup Boundary Probe
open Complex
variable {H D K:Hilbert} {a b : Axis} (r:b≠a) (S:OS.Semigroup H a) (Q:OS.Semigroup D b) (C:Clasp K H D)
local notation "X"=> cross a b r
local notation "Y"=> cross b a (Ne.symm r)
-- forward Eu motions
abbrev Beam : Prop := ∀ t s:ℝ≥0,C.Pass (S.U ((s:ℝ) • cross a b r) * S.E t) (Q.U ((t:ℝ) • cross b a r.symm)*Q.E s)
variable (e:ℝ)(g:e=1∨e=-1) (x:ℝ)(p:0<x)
private def wind (z:ℂ):= (x:ℂ)*(1-(e:ℂ)*z)
local notation "U"=> wind e x
local notation "V"=> wind (-e) x
local notation "W" z:max f:max=> stroke f (wind e x z) (wind (-e) x z)
private def optics : Set ℂ:= {x| |x.re|+|x.im|<1}
private lemma optic_open : IsOpen optics:= isOpen_lt (by fun_prop) continuous_const
private lemma optic_conn : IsPreconnected optics:= by
  refine Convex.isPreconnected (s:=optics) ?_; intro y u z v l k b c t
  change |(_+_ : ℂ).re|+|(_+_ : ℂ).im|<_
  simp only [Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,smul_eq_mul]
  have hp := add_lt_add_of_le_of_lt -- tune use `ConvexOn` or nlinarith positive handles.
    (le_refl (0:ℝ)) (show |y.re|+|y.im|<_ from u)
  refine (add_le_add (abs_add_le ..) (abs_add_le ..)).trans_lt ?_
  simp only [abs_mul,abs_of_nonneg b, abs_of_nonneg c]; have ht: |z.re|+|z.im|<1:=v; rcases c.eq_or_lt with h|h
  · rw [←h, show l=1 from by linarith]; linarith
  nlinarith
@[simp] private lemma optic0:(0:ℂ)∈ optics:= by simp [optics]
include p g
private lemma optic_price {z:ℂ}(h:z∈optics):0<(W z e).re ∧ 0<(W z (-e)).re:= by
 change |z.re|+|z.im|<1 at h
 obtain ⟨hr,k⟩:= abs_le.mp (le_refl |z.re|); obtain ⟨hi,h1⟩:= abs_le.mp (le_refl |z.im|)
 rcases g with g|g<;> rw [g] <;> simp [stroke,wind,mul_re,mul_im] <;> constructor <;> nlinarith
omit g p in
lemma dawn_prod {ι:Type*}(A:Filter ι){F N:ι→H.Op}{x y:H.Op}(a:ℝ)(p1:∀ᶠ i in A,‖F i‖≤ a)
    (p:∀ v:H,Tendsto (fun i=> F i v) A (𝓝 (x v)))(k:∀ v:H,Tendsto (fun i=> N i v) A (𝓝 (y v)))(v:H): Tendsto (fun i=> F i (N i v)) A (𝓝 (x (y v))) := by
 suffices h:Tendsto (fun i=> F i (N i v)-F i (y v)) A (𝓝 0) by
    simpa only [sub_add_cancel, zero_add] using h.add (p (y v))
 refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
 simp_rw [sub_zero,← map_sub]; refine squeeze_zero' (Eventually.of_forall fun i=> norm_nonneg _) ?_ (g:=fun i=> a*‖N i v-y v‖) ?_
 · exact p1.mono (fun i h=> ((F i).le_opNorm _).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _)))
 simpa using ((k v).sub (tendsto_const_nhds (x:=y v))).norm.const_mul a
local notation "f" z:max=> column S b e (W z e)
local notation "g₋" z:max=> column S b (-e) (W z (-e))
-- endpoint I zone
private def crosses (S:OS.Semigroup H a)(b:Axis)(e x:ℝ) (z:ℂ): H.Op:= column S b e (stroke e (wind e x z) (wind (-e) x z))*column S b (-e) (stroke (-e) (wind e x z) (wind (-e) x z))
private lemma hot : AnalyticOnNhd ℂ (crosses S b e x) optics:= by
 have h(a:ℝ)(x' : ℂ):AnalyticAt ℂ (fun z=> W z a) x':= by unfold wind stroke; fun_prop
 exact fun z u=> (((columns_hol b e S) _ (optic_price e g x p u).1).comp («f»:=fun z=> W z e) (h e z)).mul (((columns_hol b (-e) S) _ (optic_price e g x p u).2).comp («f»:=fun z=> W z (-e)) (h (-e) z))
private lemma hits : crosses S b e x I= order S.ℚmeasure (slopeRay (sail e) (ticket a b e) x):=by
 have ht: W I e = sail e * x ∧ W I (-e)=0:=by rcases g with g|g <;> rw [g] <;> simp [stroke,wind,sail] <;> constructor <;> ring_nf<;> simp <;> ring
 unfold crosses; rw [ht.1,ht.2,column_zero,mul_one,column_misc]
private lemma optic_ray (u:ℝ)(v:|u|<1):0<x*(1-e*u) ∧0<x*(1-(-e)*u):=by
 obtain ⟨h,y⟩:=abs_lt.mp v; rcases g with g|g <;> rw [g] <;> constructor <;> nlinarith
private def fare (u:ℝ):ℝ≥0 := (x*(1-e*u)).toNNReal
local notation "P"=> fare e x
local notation "Q₀"=> fare (-e) x
variable (w:Paces b S) (h:Paces a Q) (δ: Beam r S Q C)
include w
lemma scene (u:ℝ)(v:|u|<1) : crosses S b e x (u:ℂ)= S.U ((fare (-e) x u:ℝ) • X)*S.E (fare e x u):= by
  rw [eu_exp b _ _ S w _ r g]
  unfold crosses wind fare; rw [Real.coe_toNNReal _ (optic_ray e g x p u v).2.le, Real.coe_toNNReal _ (optic_ray e g x p u v).1.le]; push_cast; rfl
omit w
set_option maxHeartbeats 250000 in
private lemma moment (v:H): Tendsto (fun u:ℝ=> crosses S b e x ((u:ℂ)*I) v) (𝓝[<] 1) (𝓝 (crosses S b e x I v)):= by
 let l:=(𝓝[<] (1:ℝ)); let W':= fun t:ℝ=> (t:ℂ)*I
 have he : Tendsto W' l (𝓝 I):=by unfold W' l; simpa using ((show Continuous (fun t:ℝ=> (t:ℂ)*I) by fun_prop).tendsto' 1 I (by simp)).mono_left (nhdsWithin_le_nhds (s:=Set.Iio _))
 have z (c:ℝ): Continuous fun x=> W x c:= by unfold wind stroke;fun_prop
 have t:∀ᶠ i in l,W' i∈optics:= by
   filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show (0:ℝ)<1 from zero_lt_one))] with i p q; unfold W' optics; have h:0 < i:=q; have k:i<1:=p; simpa [abs_of_pos h]
 have hy:= t.mono (fun i p' => (optic_price e g x p p').1.le); have hv:= t.mono (fun i p' => (optic_price e g x p p').2.le)
 have hx (c:ℝ)(p:∀ᶠ i in l,0≤ (W (W' i) c).re): 0≤ (W I c).re:= ge_of_tendsto ((continuous_re.tendsto _).comp (((z c).tendsto _).comp he)) p
 apply dawn_prod l (F:=fun z=> f (W' z)) (N:=fun z=> g₋ (W' z)) 1 (hy.mono (fun v e'=> column_size b e S _ e')) (column_dawn b e S l _ hy (hx e hy) (((z _).tendsto _).comp he)) (column_dawn b (-e) S l _ hv (hx (-e) hv) (((z _).tendsto _).comp he)) -- tune
include h w δ
omit p in
lemma crosses_at : Clasp.Tide (C:=C) (ticket a b e) (ticket b a (-e)) e S.ℚmeasure Q.ℚmeasure:=by
 intro x x0
 have r0:-e=1∨ -e=-1:=by rcases g with g|g<;>rw [g]<;>simp
 have hx:= hot (b:=b) S e g x x0; let M(z:ℂ):= crosses Q a (-e) x z
 have hm:= hot (b:=a) Q (-e) r0 x x0
 rw [←hits S e g x x0,← hits Q (-e) r0 x x0] -- shadow P included p x
 have k(z:ℂ)(p:z∈optics):C.Pass (crosses S b e x z) (M z):= C.holPass _ M optic_conn hx hm 0 optic0 ?_ z p
 · apply Clasp.passLimit C (𝓝[<] (1:ℝ)) (moment S e g x x0) (moment Q (-e) r0 x x0) ?_; filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show (0:ℝ)<1 from zero_lt_one))] with i p q; exact k _ (by simp [optics,abs_of_pos (show 0 < i from q), (show i<1 from p)])
 intro d -- frequently
 have ht:Tendsto (fun t:ℝ=>(t:ℂ)) (𝓝[>] 0) (𝓝[≠] 0):= tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ((continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds) (Eventually.mono self_mem_nhdsWithin fun i h=>show (i:ℂ)≠0 from by exact_mod_cast (show 0 < i from h).ne')
 obtain ⟨u,t,v,w'⟩:= ((ht.eventually d).and ((show ∀ᶠ i:ℝ in 𝓝[>] 0,0 < i from self_mem_nhdsWithin).and (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0:ℝ)<1 from zero_lt_one))))).exists
 apply t; unfold M; rw [scene r S e g x x0 w u (by rwa [abs_of_pos v]), scene r.symm Q _ r0 x x0 h u (by rwa [abs_of_pos v]),neg_neg]; exact δ _ _
end YM.Picket
