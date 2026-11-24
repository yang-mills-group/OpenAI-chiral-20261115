import YM.SU5.Reconstruction.Trap.Lantern
import Mathlib.Analysis.VonNeumannAlgebra.Basic
/-!
# Right angle registration. Keep anti involution explicit.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.BridgeClub
open Function Set Filter MeasureTheory Spectral Analysis Metric ContinuousLinearMap
open scoped BigOperators Topology InnerProductSpace ComplexOrder
variable {H:Hilbert}
-- Hilbert on space tested
structure Flash (H:Hilbert) where
 f : H →L⋆[ℂ] H
 twice (x:H):f (f x)=x
 light (x y:H): inner ℂ (f x) (f y) = inner ℂ y x
namespace Flash
variable (G:Flash H)
def shade (x:H.Op): H.Op:= ContinuousLinearMap.comp (ContinuousLinearMap.comp G.f x) G.f
lemma shade_at (x:H.Op)(y:H): G.shade x y = G.f (x (G.f y)):= rfl
lemma shade_light (x:H.Op)(y:H): G.shade x (G.f y) = G.f (x y):= by rw [shade_at,G.twice]
lemma bill (v:H): ‖G.f v‖=‖v‖:= by rw [@norm_eq_sqrt_re_inner ℂ,@norm_eq_sqrt_re_inner ℂ,G.light]
lemma cor (x y:H): inner ℂ (G.f x) y = inner ℂ (G.f y) x:= by
 conv_lhs=> rhs; rw [← G.twice y]
 exact G.light .. -- tactic layout
lemma back (A:H.Op):G.shade (G.shade A)=A:= by ext1 v; rw [shade_at,shade_light,G.twice]
lemma shade_mul (A B:H.Op):G.shade (A*B)=G.shade A* G.shade B:= by
 ext1 v
 conv_rhs=> rw [mul_apply_eq_comp,G.shade_at B,shade_light]
 rfl
lemma shade_near (x:H.Op): ‖G.shade x‖≤‖x‖:= by
 apply (G.shade x).opNorm_le_bound (norm_nonneg _); intro y; rw [shade_at,bill]; simpa only [G.bill] using x.le_opNorm (G.f y)
lemma shade_cost (x:H.Op): ‖G.shade x‖= ‖x‖:= le_antisymm (shade_near ..) (by simpa only [G.back] using (G.shade_near (G.shade x)))
lemma shade_star (x:H.Op): (G.shade (star x))=star (G.shade x):=by
 ext1 v; apply ext_inner_right ℂ; intro y; rw [G.shade_at, G.cor, show star x=x.adjoint from rfl, show star (G.shade x)=(G.shade x).adjoint from rfl,adjoint_inner_left, adjoint_inner_right]; -- check orient
 rw [shade_at]
 conv_rhs=> lhs; rw [← G.twice v]
 rw [G.light]
section
variable {X:Type*}[AddCommGroup X][Module ℂ X] {f:X→ₗ[ℂ] H} (g:X →ₗ⋆[ℂ] X)
lemma cycle (t:Involutive g)(p:∀ x y, inner ℂ (f (g x)) (f (g y)) = inner ℂ (f y) (f x))(b:DenseRange f) : ∃ A:Flash H,∀ x, A.f (f x)=f (g x):=by
 let A:X →ₗ⋆[ℂ] H:= f.comp g; let B:= LinearMap.extendOfNorm A f
 have h (x:X): B (f x)= f (g x):= by
    apply LinearMap.extendOfNorm_eq b (show ∃ c, ∀ y:X,‖A y‖≤ c*‖f y‖ from ⟨1,fun y=>?_⟩) x -- reducibility?
    change ‖f (g y)‖ ≤ _; rw [@norm_eq_sqrt_re_inner ℂ H _ _ _ (f (g y)),one_mul,@norm_eq_sqrt_re_inner ℂ H _ _ _ (f y)]; rw [p]
 have hp(x:H): B (B x)=x:=by
   apply congrFun (a:=x) (b.equalizer (Continuous.comp B.continuous B.continuous) continuous_id ?_)
   funext y; change B (B (f y))=_; rw [h,h,t]; rfl
 have hx(x y:H):inner ℂ (B x) (B y)= inner ℂ y x:= by
   have hz(x:X)(y:H):inner ℂ (B (f x)) (B y)=inner ℂ y (f x):= by
     refine congrFun (a:=y) (b.equalizer (continuous_const.inner B.continuous) (continuous_id.inner continuous_const) (funext fun y=>?_))
     change inner ℂ (B (f x)) (B (f y))= _; rw [h,h]; exact p x y
   exact congrFun (a:=x) (b.equalizer (B.continuous.inner continuous_const) (continuous_const.inner continuous_id) (funext fun x=>hz x y))
 exact ⟨⟨B,hp,hx⟩,h⟩
end
end Flash
end YM.BridgeClub
