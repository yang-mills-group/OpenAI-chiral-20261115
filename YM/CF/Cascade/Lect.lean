import YM.CF.Cascade.Ram
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cascade
open Function Filter Metric Finset Lattice Wilson Next.Free Bloch Laurent Scroll Precision Exterior Lat Ember Aroma
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker
variable {j t:ℕ}{n c f:Side}{k a b:ℝ}
open Tree SU Font Cube Extra.Iteration Nacre
-- only Air orbit
abbrev Heat(n:Side):= Air n →ₗ[ℝ] Air n→ₗ[ℝ]ℝ
abbrev grove (n:Side):= groan (n:=n) Complex.reCLM
abbrev waveL (n:Side):= groan (n:=n) Complex.imCLM
def syl (H:Heat n)(x y:Ail n):ℂ:= let X:=grove n; let Y:=waveL n
 ⟨H (X x) (X y)+H (Y x) (Y y), H (Y x) (X y)-H (X x) (Y y)⟩
def rye (n:Side)(t:Cover)(x:Ail n):= fun i:Site (More n)=> x (i+wrap _ (2 • t))
def Gird (H:Heat n):Prop:=∀ t:Cover,∀ x y,H (rake t x) (rake t y)=H x y
lemma syl_g {H:Heat n}(p:Gird H)(x y:Ail n)(t:Cover): syl H (rye n t x) (rye n t y)= syl H x y:=by
 unfold syl; dsimp only; have hx(x):grove n (rye n t x)=rake t (grove n x):=rfl; have hy(x):waveL n (rye n t x)=rake t (waveL n x):=rfl; rw [hx,hx,hy,hy,p,p,p,p]
lemma syl_a (H:Heat n)(x y:Ail n)(c d:ℂ): syl H (c • x) (d • y)=(c*star d)*syl H x y:=by
 let X:=grove n; let Y:=waveL n; have ht(x:Ail n)(c:ℂ): grove n (c • x)=c.re • X x - c.im • Y x:=funext fun i=> rfl
 have hx(x:Ail n)(c:ℂ):waveL n (c • x)=c.re • Y x + c.im • X x:=funext fun i=>rfl
 unfold syl; dsimp only; rw [ht,ht,hx,hx]; apply Complex.ext <;> simp only [map_add,map_sub,map_smul, LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,Complex.mul_re,Complex.mul_im,Complex.star_def,Complex.conj_im,Complex.conj_re, smul_eq_mul] <;> first|rfl| (unfold X Y; ring)
lemma syl_orth(G:Ratio (More c) (More n))(p:Odd G.count.val){H:Heat n}(h:Gird H)(x:Site (More c))(u v: Site G.count)(l:u≠v):syl H (hike (aliasAt (mon x) u)) (hike (aliasAt (mon x) v))=0:=by
 obtain ⟨s,he⟩:= apart G p x _ _ l; let X(i:Site G.count):= hike (n:=More n) (aliasAt (mon x) i); let V(i:Site G.count):=mode (aliasAt (mon x) i) (2 • s); have ht(i:Site G.count): rye n s (X i)=V i • X i:=funext fun j=> (singI _ j _ (2 • s) rfl (winds G x i)).trans (mul_comm ..); have hz:= syl_g h (X u) (X v) s; rw [ht,ht,syl_a] at hz; let T:=syl H (X u) (X v); by_contra hy; have hp: V u*star (V v)=1:= mul_right_cancel₀ hy (hz.trans (one_mul T).symm)
 have hw:‖V v‖=1:= mode_real _ _ (alias_real (real_frequency x) v); have hh:star (V v)*V v=1:= by have hh:=inner_self_eq_norm_sq_to_K (𝕜:=ℂ) (x:=V v); rw [hw] at hh; rw [mul_comm]; exact hh.trans (by simp)
 exact he (show V u= _ from (mul_right_cancel₀ (show star (V v)≠0 from by rw [star_ne_zero]; exact norm_pos_iff.mp (zero_lt_one.trans_eq hw.symm)) (hp.trans (mul_comm (V v) _|>.trans hh).symm)))
lemma syl_r (H:Heat n)(x:Ail n)(u:ℂ): (syl H (u • x) (u • x)).re= ‖u‖^2*(syl H x x).re:=by rw [syl_a]; rw [show u*star u= ↑(‖u‖^2) by rw [Complex.ofReal_pow]; exact inner_self_eq_norm_sq_to_K (𝕜:=ℂ) (x:=u)]; rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,zero_mul,sub_zero]
lemma syl_b(G:Ratio (More c) (More n))(p:Odd G.count.val){H:Heat n}(h:Gird H)(x:Site (More c))(f:Site G.count→ℂ):let X(i):= hike (n:=More n) (aliasAt (mon x) (i:Site G.count)); let Z:= ∑ i,f i • X i; (syl H Z Z).re= ∑ i, ‖f i‖^2 * (syl H (X i) (X i)).re:=by
 intro X Z
 let P(i):= f i • X i; have he : (syl H Z Z).re= ∑ i,∑ j,(syl H (P i) (P j)).re:=by unfold P Z syl; dsimp only; simp only [map_sum, LinearMap.sum_apply,sum_add_distrib]; apply congrArg₂ (· + ·) <;> rw [sum_comm]
 rw [he]; refine sum_congr rfl fun i _=>?_ ; rw [sum_eq_single i]; exact syl_r ..; intro j _ q; rw [show syl H (P i) (P j)= _ from syl_a _ _ _ _ _, show syl H (X i) (X j)=0 from syl_orth G p h x _ _ (Ne.symm q),mul_zero]; rfl; simp
end YM.CF.Cascade
