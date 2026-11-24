import YM.SU5.FiniteGaugeData.Seld.WildCat
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}{a:Axis}(S: OS.Semigroup H a)(x y:H)(t:ℝ)(u:ℝ≥0)
local notation "rayA"=> Ioi (0:ℝ)
local notation "R"=> saucer S
open Spectral Boundary Probe
local notation "V"=> S.unit
local notation "U"=> M S
variable (A B: H.Op)(p:E4)(g h: Test4)(c:ℂ)
local notation "W" => Bench S
local notation "□" => W →ₗ[ℂ] W
local notation "D"=> hill S
variable (X Y:Bench S)(n m:ℕ)
def usher : W →ₗ[ℂ] W := park S (M S p) (autumn S _ (tread S p).symm)
def stove : W →ₗ[ℂ] W := park S (S.E u) (autumn S _ (cupE S u).symm)
def ℑ₀ : W →ₗ[ℂ] W := park S (valise S A g) (initialized S A g)
def ℑ : W →ₗ[ℂ] W := (hill S n).comp ((ℑ₀ S A g).comp (hill S n))
-- operator housing
local notation "Ψ"=> ℑ S A
local notation "Ψ₀"=> ℑ₀ S A
local notation "K"=> Cache S
@[simp] lemma native : Cache S n (ℑ S A g n X).val= valise S A g (hall S n X):=releases S n _
lemma graphN : hall S m (Ψ g n X)= brochure S A (n+m) g (hall S (n+(n+m)) X):=by
 change hall S m (hill S n (Ψ₀ g (hill S n X)))=_; rw [hill_comb, ℑ₀,park_κ S (n+m) _ _ _ _ (brochure_eq ..),hill_comb]
-- ↑ unary/multi-field systems
lemma anyB : ℑ S (A+B) g n= ℑ S A g n+ℑ S B g n:= by
 ext1 x; apply Subtype.ext; change ↑(_) = (ℑ S A g n x).val + (ℑ S B g n x).val; apply cache_I S n; rw [map_add,native,native,native,vadd,_root_.add_apply]
lemma anyC : ℑ S (c • A) g n=c • ℑ S A g n:= by
 ext1 x; apply Subtype.ext; change ↑(_) = c • (ℑ S A g n x).val; apply cache_I S n; rw [map_smul,native,native,vscale,_root_.smul_apply]
def σV(n:ℕ): Test4→ₗ[ℂ] (W →ₗ[ℂ] W) where
 toFun g:=Ψ g n
 map_add' g h:= by ext1 x; apply Subtype.ext; change ↑(_) = (Ψ g n x).val+(Ψ h n x).val; apply cache_I S n; rw [map_add,native,native,native,show valise S A (g+h)=_ from map_add (barren S A) g h]; rfl
 map_smul' c v:=by ext1 x; apply Subtype.ext; change ↑(_) = c • (Ψ v n x).val; apply cache_I S n; rw [map_smul,native,native,show valise S A (c • v)=_ from map_smul (barren S A) c v]; rfl
lemma sees_κ : inner ℂ (Ψ g n X).val Y.val= inner ℂ X.val (ℑ S (star A) (bar g) n Y).val := by
 have he (f:W)(x:H): inner ℂ f.val x= inner ℂ (hall S n f) (K n x):=by rw [← ContinuousLinearMap.adjoint_inner_left (K n), show (K n).adjoint=K n from (saucer_sym S).pow n, releases] -- rewriting L or R danger
 have hh(f:W)(x:H): inner ℂ x f.val=inner ℂ (K n x) (hall S n f):=by rw [← inner_conj_symm x,he, inner_conj_symm]
 rw [hh Y,he X,native,native,scenery]; exact (ContinuousLinearMap.adjoint_inner_right ..).symm
lemma assizes : inner ℂ X.val (Ψ g n Y).val= ∫ p,g p* lucent S (hall S n X) (hall S n Y) A p:=by
 rw [sell_in]; generalize hs: Ψ g n Y = v; rw [← native, hs]; let x:= hall S n X; rw [← ContinuousLinearMap.adjoint_inner_left (K n), show (K n).adjoint=K n from (saucer_sym S).pow n,releases]
lemma attends : usher S p (Ψ g n X)= Ψ (ahead p g) n (usher S p X):=by
 apply Subtype.ext; apply cache_I S n; change K n (U p (Ψ g n X).val) = K n (Ψ (ahead p g) n _).val; have he(z:H): K n (U p z)=U p (K n z):= DFunLike.congr_fun ((tread S p).pow_left n).eq z
 rw [he, native, native, ← precursor, usher, park_κ S _ _ _ _ _ ((tread S p).symm.pow_right n)]; unfold optx; let v:=hall S n X; change _=U p (valise S A g (U (-p) (U p v))); rw [show U (-p) (U p v) = v from DFunLike.congr_fun (Eq.trans (tgo S (-p) p) (by rw [neg_add_cancel,tini] : U (-p+p)=1)) v]
lemma ℑNorm : ‖hall S m (Ψ g n X)‖≤ dollycoin a (n+m) g * ‖A‖ * ‖hall S (n+(n+m)) X‖:= by rw [graphN]; exact ((brochure S A _ g).le_opNorm _).trans (mul_le_mul_of_nonneg_right (dollyP S A g _) (norm_nonneg _))
variable {C:Type*}(ℱ:Filter C)(Yp:C→ Bench S)
lemma ℑLim₁(G:C→Test4)(p:Tendsto G ℱ (𝓝 g))(k:pays_to S ℱ Yp X): pays_to S ℱ (fun t=> Ψ (G t) n (Yp t)) (Ψ g n X) := by
 intro m; simp_rw [graphN]; exact (show Continuous (fun i:H.Op×H=>i.1 i.2) from continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp ((((BroCt S A (n+m)).tendsto g).comp p).prodMk_nhds (k _))
-- continuity in field alone (Wightman)
lemma singular : Continuous (fun g=>(ℑ S A g n X).val) := continuous_iff_continuousAt.mpr fun g=> tune_in S _ _ _ (ℑLim₁ S A g X n _ _ id tendsto_id (fun _=>tendsto_const_nhds)) -- tune binder
#print axioms singular
lemma duet : Continuous (fun p:H×ℝ≥0=> S.E p.2 p.1):= continuous_prod_of_continuous_lipschitzWith _ 1 S.continuousE fun t=> lipschitzWith_iff_dist_le_mul.mpr (fun x y=>by change dist (S.E t x) _ ≤ _; simp only [NNReal.coe_one,one_mul]; rw [dist_eq_norm, ← map_sub,dist_eq_norm]; exact ((S.E t).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (S.shrinks _))) -- K'
lemma stoveLim(V':C→ℝ≥0)(t:Tendsto V' ℱ (𝓝 u))(h:pays_to S ℱ Yp X): pays_to S ℱ (fun i=> stove S (V' i) (Yp i)) (stove S u X) := by
 intro n; have he (u:ℝ≥0)(X:Bench S) : hall S n (stove S u X)= S.E u (hall S n X):= park_κ S n _ _ _ _ ((cupE S u).symm.pow_right n)
 simp_rw [he]; let x:= hall S n X; let Z (y:H×ℝ≥0):= S.E y.2 y.1; exact ((duet S).tendsto (x,u)).comp ((h n).prodMk_nhds t)
lemma usherLim(Q:C→E4)(t:Tendsto Q ℱ (𝓝 p))(h:pays_to S ℱ Yp X): pays_to S ℱ (fun i=> usher S (Q i) (Yp i)) (usher S p X):=by
 intro n; have he(t:E4)(X:Bench S): hall S n (usher S t X)=M S t (hall S n X):= park_κ S n _ _ _ _ ((tread S t).symm.pow_right n)
 simp_rw [he]; change Tendsto (fun i => S.unit.translation (Q i) (hall S n (Yp i))) ℱ _; let v:= S.unit.translation; have hv := ((step_c S).tendsto (hall S n X,p)).comp ((h n).prodMk_nhds t); dsimp only [Function.comp_apply, Function.comp_def] at hv; exact hv
lemma ushe (q:E4): usher S p (usher S q X)=usher S (p+q) X:=Subtype.ext (DFunLike.congr_fun (tgo S p q) X.val)
@[simp] lemma uh_zero : usher S 0 X=X:= Subtype.ext (DFunLike.congr_fun (tini S) X.val)
@[simp] lemma stove_zero : stove S 0 X=X:= Subtype.ext (DFunLike.congr_fun S.eZero X.val)
#print axioms stoveLim
end YM.CF.Buffered.Afterglow.Hierarchy.Seld
