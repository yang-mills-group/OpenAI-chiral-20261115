import HectorA.InShift
import Acacia.Rill
import Acacia.Smith
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 300000
set_option quotPrecheck false
noncomputable section
namespace Acacia
open Filter Function Finset Set YM.OS YM Yoland
open scoped Topology NNReal BigOperators Classical InnerProductSpace
attribute [local instance] InnerProductSpace.complexToReal
-- pay for delta.F
variable{H:Hilbert}{a:Axis}(S:OS.Semigroup H a){h:ℕ→ℝ}(p:∀i,0<h i)
include p
lemma amen_step (y:ℝ)(hy:0<y)(q:Tendsto h atTop (𝓝 0)): ∃ C:ℝ,0<C∧∀ᶠ i:ℕ in atTop,
 ‖(noon S (h i)).comp (dawn S y)- (pay S 1 y)‖ ≤ h i*C:=by
 obtain ⟨C,v,t⟩:= rate2 (dawn S) y (dawnRise S y hy) q p; exact ⟨C,v,t.mono fun i k=> (stride_single S hy (p i).le).symm ▸ k⟩
omit p
lemma delta_cpuS (n:ℕ)(h t:ℝ)(p:0≤h)(v:0≤t): delta h n (dawn S) t= frame S n h (dawn S t):=by
 induction n generalizing t with
 | zero=>rfl
 | succ n ih=>
    rw [delta_s,ih _ (add_nonneg v p),ih _ v]
    change h⁻¹ • (frame S n _ _-frame S n _ _)= (noon S _).comp (frame S n _ _)
    rw [add_comm t h,dawn_add S p v]; unfold noon; rw [ContinuousLinearMap.smul_comp,ContinuousLinearMap.sub_comp,ContinuousLinearMap.id_comp]
    apply congrArg (fun z:H.Op=>h⁻¹ • (z-frame S n h (dawn S t)))
    exact consul S p p n _
where
 consul{H:Hilbert}{i:Axis}(S:OS.Semigroup H i){h:ℝ}(p:0 ≤h){u:ℝ}(v:0 ≤ u)(n:ℕ)(z:H.Op): frame S n h ((dawn S u).comp z)=(dawn S u).comp (frame S n h z):=by
    induction n generalizing z with
    | zero=>rfl
    | succ n hn=>
       change (noon S _).comp (frame S n _ _)=(dawn S u).comp ((noon S h).comp (frame S n _ z)); rw [hn, ← ContinuousLinearMap.comp_assoc,← ContinuousLinearMap.comp_assoc,show (noon S h).comp _=(dawn S u).comp (noon S h) from ?_]
       unfold noon; rw [ContinuousLinearMap.smul_comp,ContinuousLinearMap.comp_smul,ContinuousLinearMap.sub_comp,ContinuousLinearMap.comp_sub,←dawn_add S p v,←dawn_add S v p,add_comm h]; simp
-- applied arguments tune p n. consul S p p n z
#print axioms delta_cpuS
variable(t:ℝ) (g:0<t)(v:Tendsto h atTop (𝓝 0))
include p g v
private lemma product_pay (T:ℕ→H.Op)(Q:H.Op)(hp:∃ C:ℝ,0<C∧∀ᶠ i in atTop,‖T i-Q‖≤h i*C)(A:ℕ→H.Op)(A':H.Op)(hq:∃d:ℝ,0<d∧∀ᶠ i in atTop,‖A i-A'‖ ≤ h i*d):∃ e:ℝ,0<e∧∀ᶠ i in atTop,‖(T i).comp (A i)-Q.comp A'‖ ≤ h i*e:=by
 obtain ⟨c,w,h₀⟩:=hp; obtain ⟨d,d',q'⟩:=hq
 let n:=d+‖A'‖; let K:= c*n+‖Q‖*d
 refine ⟨K,by unfold K n; positivity,?_⟩
 filter_upwards [h₀,q',v.eventually (ge_mem_nhds zero_lt_one)] with i e' g' u
 have hv:0<h i:=p i
 have hA:‖A i‖ ≤ n:=by
    have hu:= norm_sub_norm_le (A i) A'; unfold n; nlinarith
 rw [show (T i).comp (A i)-Q.comp A'=(T i-Q).comp (A i)+ Q.comp (A i-A') from (by rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]; abel)]
 apply le_trans (norm_add_le ..); refine (add_le_add (ContinuousLinearMap.opNorm_comp_le ..) (ContinuousLinearMap.opNorm_comp_le ..)).trans ?_
 unfold K; nlinarith [mul_le_mul e' hA (norm_nonneg _) (by positivity:0≤h i*c),mul_le_mul_of_nonneg_left g' (norm_nonneg Q)]
lemma arn (n:ℕ):∃ C:ℝ, 0<C∧∀ᶠ i:ℕ in atTop,
 ‖frame S n (h i) (dawn S (n*t))-pay S n (n*t)‖ ≤ h i*C:=by
 induction n with
 | zero=> exact ⟨1,zero_lt_one, Eventually.of_forall fun i=>by simpa [pay,frame] using (p i).le⟩
 | succ n ih=>
    let T (i):=(noon S (h i)).comp (dawn S t); let Y(i):= frame S n (h i) (dawn S (n*t)); let Q:=pay S n (n*t)
    obtain ⟨C,k,e⟩:=product_pay (H:=H) p t g v T (pay S 1 t) (amen_step S p _ g v) Y Q ih -- arg order t p
    refine ⟨C,k,e.mono fun i q=> ?_⟩
    have hp:(T i).comp (Y i)=frame S (n+1) (h i) (dawn S ((n+1:ℕ)*t)):=by
       unfold T Y; push_cast
       change ((noon S _).comp (dawn S _)).comp _=(noon S (h i)).comp (frame S n _ (dawn S _))
       rw [add_mul,one_mul, add_comm (_*t) t,dawn_add S g.le (mul_nonneg (Nat.cast_nonneg _) g.le),delta_cpuS.consul S (p i).le g.le, ContinuousLinearMap.comp_assoc]
    have hq:(pay S 1 t).comp Q=pay S (n+1) ((n+1:ℕ)*t):=by
       by_cases he:n=0; · unfold Q; rw [he]; unfold pay; push_cast; rw [iteratedDeriv_zero]; simp [dawn,S.eZero]
       rw [show Q=pay S n (n*t) from rfl, earns_asset S n 1 _ t (by exact mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero he)) g) g]; push_cast; rw [add_mul,one_mul,add_comm 1 n]
    rwa [←hp,←hq]
#print axioms arn
lemma way(t₀:ℝ)(n:ℕ)(u:(n:ℝ)*t ≤t₀): ∃ C:ℝ, 0<C ∧∀ᶠ i:ℕ in atTop, ‖delta (h i) n (dawn S) t₀-pay S n t₀‖ ≤ h i * C :=by
 obtain ⟨A,e,k⟩:= arn S p t g v n
 let u':=(n:ℝ)*t; have hu:0≤u':=mul_nonneg (Nat.cast_nonneg _) g.le
 let y:=t₀-u'; let T:=dawn S y; have hr:0 ≤ y:=sub_nonneg.mpr u; have he:u'+y=t₀:=add_sub_cancel .. -- maybe add_sub_of_le
 have hp:pay S n t₀=(pay S n u').comp (dawn S y):=by
    by_cases hz:y=0; · rw [←he,hz,add_zero,dawn,Real.toNNReal_zero,S.eZero,ContinuousLinearMap.comp_id]
    by_cases hx:n=0; · rw [hx]; unfold pay; rw [iteratedDeriv_zero,←he,dawn_add S hu hr]
    have t₁:0<u':=mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hx)) g
    have hY:0<y:=lt_of_le_of_ne hr (Ne.symm hz)
    have hx':= earns_asset S 0 n y u' hY t₁; simpa only [add_comm y u',he,Nat.add_zero,pay,iteratedDeriv_zero] using hx'.symm
 refine ⟨A,e,k.mono fun i q=>?_⟩
 rw [delta_cpuS S _ _ _ (p i).le (hu.trans u),hp,show dawn S t₀= _ from ((congrArg (dawn S) he.symm).trans (dawn_add S hu hr): _= (dawn S u').comp T),framed,← ContinuousLinearMap.sub_comp]
 exact (ContinuousLinearMap.opNorm_comp_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (S.shrinks ..)).trans q)
#print axioms way
end Acacia
