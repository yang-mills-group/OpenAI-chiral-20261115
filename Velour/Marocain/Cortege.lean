
import Velour.Organza.Welcoming
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 1100
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S:Semigroup H a)

open Boundary Probe

variable {n:ℕ}


abbrev filepast {A:Type*}[Monoid A] (v:Fin n→A):A:=(List.ofFn v).prod
lemma filepast_cons {A:Type*}[Monoid A] (v:Fin (n+1)→A):
  filepast v=v 0 * filepast (Fin.tail v) :=by rw [filepast,List.ofFn_succ,List.prod_cons];rfl


local notation "U" => S.unit.translation
local notation "R" => S.gauze
local notation "D" => S.muslin
local notation "B" => S.weight
local notation "𝓧" => Fin n → H.Op
local notation "𝒦" => Fin n → ℕ
local notation "𝓕" => Fin n → Test4
local notation "𝓑" => Module.End ℂ D
local notation "𝓗" => H.space

def parade (X:𝓧)(x:Points n): H.Op:=
  filepast fun i => S.dangle (x i) (X i)
lemma parade_next (X:Fin (n+1)→H.Op)(x:Points (n+1)):
  S.parade X x= S.dangle (x 0) (X 0)*S.parade (Fin.tail X) (Points.tail x):= filepast_cons ..

lemma parade_zero (X:Fin 0→H.Op)(x:Points 0): S.parade X x=1:=by
 simp [parade,filepast]

lemma dangle_joint {T:Type*}[TopologicalSpace T]{b:T→E4}{y:T→𝓗}
   (W:H.Op)(s:Continuous b)(u:Continuous y):
  Continuous fun t=> S.dangle (b t) W (y t):=by
  have h {b:T→E4}{y:T→𝓗}(s:Continuous b)(u:Continuous y):
      Continuous fun t=> U (b t) (y t):=
    S.cont_edge _ _ (S.cont_cross _ _ u ((SEP a).continuous.comp s)) (by fun_prop)
  exact h s (W.continuous.comp (h s.neg u))

lemma parade_cont (X:𝓧)(v:𝓗): Continuous fun x=> S.parade X x v:=by
  induction n with
  | zero=>simp [S.parade_zero,continuous_const]
  | succ n ih =>
    simp_rw [S.parade_next,mul_apply_eq_comp]
    have u: Continuous (@Points.tail n):=continuous_snd.comp Joint.breakAt.continuous
    exact S.dangle_joint _ (by fun_prop) ((ih _).comp u)

lemma parade_price (X:𝓧)(v:𝓗)(x:Points n):
    ‖S.parade X x v‖ ≤ (∏ i,‖X i‖)*‖v‖:=by
  induction n with
  | zero=> simp [S.parade_zero]
  | succ n ih =>
    rw [Fin.prod_univ_succ,parade_next,mul_apply_eq_comp,mul_assoc]
    exact (S.dangle_bill ..).trans (mul_le_mul_of_nonneg_left (ih ..) (norm_nonneg _))
lemma p_available (T:𝓧)(f:Joint n)(x:H.space): Integrable fun b=>f b • S.parade T b x:= by
  have p: Integrable (fun b:Points n=>‖f b‖ * ((∏ i,‖T i‖)*‖x‖)) volume:=
    f.integrable.norm.mul_const _
  exact p.mono' ((f.continuous.smul (S.parade_cont ..)).aestronglyMeasurable)
    (ae_of_all _ fun b=>(norm_smul ..).trans_le
      (mul_le_mul_of_nonneg_left (S.parade_price T _ b) (norm_nonneg _)))

/-- our basic bill. -/
def P₁ (f:Joint n) :ℝ:=‖f.toLp 1 volume‖
lemma real_P₁ (f:Joint n): P₁ f=∫b,‖f b‖:=SchwartzMap.norm_toLp_one
lemma P₁_cont : Continuous (@P₁ n) := SchwartzMap.continuous_toLp.norm


private lemma wash_bound_aux (T:𝓧)(f:Joint n)(x:H.space):
 ‖∫ b, f b • S.parade T b x‖ ≤ (P₁ f * (∏ i,‖T i‖)) * ‖x‖ := by
 rw [real_P₁,mul_assoc,←integral_mul_const]
 refine norm_integral_le_of_norm_le (f.integrable.norm.mul_const _) ?_
 exact ae_of_all _ fun b=>(norm_smul ..).trans_le
      (mul_le_mul_of_nonneg_left (S.parade_price T _ b) (norm_nonneg _))

private noncomputable def wash (T:𝓧)(f: Joint n): H.Op:= LinearMap.mkContinuous (σ:=RingHom.id ℂ)
 { toFun:= fun x=>∫ b, f b • S.parade T b x
   map_add' x y:= by simp only [map_add,smul_add]; rw [integral_add (S.p_available ..) (S.p_available ..)]
   map_smul' c x:= by simp only [map_smul]; simp_rw [smul_comm _ c]; rw [integral_smul];rfl
 } _ (S.wash_bound_aux T f)

private noncomputable def washes (T:𝓧): Joint n →ₗ[ℂ] H.Op where
 toFun:=wash S T
 map_add' f g:= by
  ext1 x
  change (∫ b, (f+g) b • S.parade T b x)= (∫ b, f b • S.parade T b x)+∫ b, g b • S.parade T b x
  simp_rw [_root_.add_apply,add_smul, integral_add (S.p_available ..) (S.p_available ..)]
 map_smul' c f:=by
  ext1 x
  change (∫ b, (c • f) b • S.parade T b x)= c • ∫ b, f b • S.parade T b x
  simp_rw [_root_.smul_apply,smul_eq_mul, mul_smul,integral_smul]


lemma zero_P₁ : P₁ (0:Joint n)=0:=by rw [real_P₁]; simp
lemma P₁_nonneg (f:Joint n): 0≤P₁ f:=norm_nonneg _

private lemma washes_bound (T:𝓧)(f:Joint n) : ‖S.washes T f‖≤ P₁ f * (∏ i,‖T i‖) :=
 ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (P₁_nonneg _) (by positivity))
     (S.wash_bound_aux T f)

/-- Minkowski translation smear. -/
def procession (T:𝓧): Joint n →L[ℂ] H.Op where
 toLinearMap:=S.washes T
 cont:=by
  change Continuous (S.washes T)
  apply continuous_of_continuousAt_zero (S.washes T)
  have p:Tendsto (fun f:Joint n=> P₁ f * (∏ i,‖T i‖)) (𝓝 0) (𝓝 0):=by
    have k: P₁ (0:Joint n) * (∏ i,‖T i‖) =0:=by rw [zero_P₁,zero_mul]
    exact k ▸ ((P₁_cont.mul (g:=fun _=>(∏ i,‖T i‖)) continuous_const).tendsto 0)
  change Tendsto _ _ _
  rw [map_zero]
  exact squeeze_zero_norm (S.washes_bound T) p

lemma procession_apply (T:𝓧)(f:Joint n)(x:H.space):
 S.procession T f x=∫ b, f b • S.parade T b x:=rfl
lemma procession_bill (T:𝓧)(f:Joint n) : ‖S.procession T f‖ ≤ P₁ f * (∏ i,‖T i‖):=S.washes_bound ..




#print axioms procession
#print axioms procession_bill
