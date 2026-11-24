import YM.CF.Cadre.Vast
import YM.CF.Cadre.Rone
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Cadre
open Function Filter Topology Lattice Finset Palot
open scoped Classical
variable {A:Type*}[Fintype A][DecidableEq A]
local notation "ΣA"=> Palot.leaf A
local notation "ΣG"=> hook A
variable (Y:Palot.leaf A)(D O:Finset A)(F:hook A)
-- P supports meeting kernel leaf Y
open PowerSeries
variable (V: leaf A→ Finset A→PS)(v:∀ X:Palot.leaf A,∀ D ⊆ X.val,cent (V X D))(Q: leaf A→ℝ)(q:0≤Q)(κ:ℝ)(m:1≤κ)(L w:ℝ)(b:leaf A→ℝ)
-- Width valuation on any leaf. Card bound & subadd across contacts.Bound at fixed exponential.Clock
structure Tour {A:Type*}[Fintype A][DecidableEq A](b:leaf A→ℝ)(s:ℝ):Prop where
 pos :∀ i, 1≤b i
 rate: ∀ i:leaf A,(i.val.card:ℝ) ≤ s*b i
 loom:∀ (X Y:leaf A)(G:Finset (leaf A)), G∈drum X Y ∅→ b X ≤ b Y+∑ i∈G,b i
variable {x s:ℝ}(T:Tour b s) (γ c d e h:ℝ)(g:h≥0)(k:∀ o:A,serif V κ L w b o 0 0<γ)
local notation "B"=> loom_v L w b
local notation "K_"=> seed_v V κ
local notation "S"=> serif V κ L w b
local notation "P"=> cubL V κ L w b
local notation "Θ"=> foe V κ L w b
variable (p:0 ≤ L-w*h) (r:0 ≤ w)(mQ:0 ≤ γ)(z:Palot.leaf A→ℝ)(z₁:0 ≤ z)
variable {R:leaf A→ Finset A→PS}(ϑ:flowZ V Q z R)
include T r p
lemma tier (j:Palot.leaf A)(X:ΣA)(Z:ΣG)(ht:x∈Set.Icc 0 h)(v: Z∈drum j X ∅) : B x j ≤ B x X*tilt (B x) Z:=by
 let l:= L-w*x; have hx:L-w*x≥0:=by nlinarith [ht.2]
 unfold loom_v tilt; rw [←Real.exp_sum, ←Real.exp_add,←mul_sum, ←mul_add]; exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (T.loom _ _ _ v) hx)
omit p
lemma tap (t:0≤x): B x ≤ B 0:=fun i=>Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (sub_le_sub_left (mul_le_mul_of_nonneg_left t r) L) (zero_le_one.trans (T.pos i)))
omit T r
include m v q
lemma stair (i j:ℕ)(h:i ≤ j)(t:0 ≤ x) : K_ i x ≤ K_ j x:=fun X=> sum_le_sum fun D p=>mul_le_mul_of_nonneg_left ((v X D (mem_powerset.mp p)).kind h t) (zero_le_one.trans (duty_i D m))
lemma stair_k(i j:ℕ)(o:A)(h:i ≤ j)(t:0≤x):S o i x ≤ S o j x:= sum_le_sum (fun Y _=> mul_le_mul_of_nonneg_right (stair V v Q q κ m i j h t Y) (Real.exp_pos ..|>.le))
lemma nook_k (G U:leaf A→ℝ)(h:G≤U)(i:A): nook G i ≤ nook U i:=sum_le_sum fun i _=> h i
omit m v q
variable (hC:∀ i:A, nook (fog (loom_v L w b 0) Q γ) i ≤ c)(hD:∀ i:A,shelfR (fog (loom_v L w b 0) Q γ) i ≤ d)(hI:∀ i:A, nook (z*loom_v L w b 0) i ≤ e)(hm:0 ≤ c)(hw:s*c ≤ w)
include m v q hC hD ϑ T z₁ p mQ r hI
lemma sans(o:A)(t:ℝ)(u:t∈ Set.Icc 0 h)(i:ℕ)(x:∀ j:A,S j i t ≤ γ):
 cubL R κ L w b o i t ≤ e+(d*γ+shelfR (K_ i t * B t) o*c):=by
 let F(X:ΣA):= (∑ Y:ΣA,ode0 Q (K_ i t) X Y)*B t X; let K:=fog (B t) Q γ; let A':=B t
 have ht(X:ΣA):K X ≤ fog (B 0) Q γ X:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (tap L w b T r u.1 X) (q X)) (Real.exp_pos ..|>.le)
 have hk:= vale A' (K_ i t) Q (fun i=>Real.exp_pos ..|>.le) (seed_nn V v Q q κ m _ _ u.1) q γ c d (fun X Y Z q=>tier L w b T h p r X Y Z u q) x (fun i=> (sum_le_sum (s:=spark i) (fun j _=>ht j)).trans (hC i)) (fun i=> (sum_le_sum (s:=spark i) (fun j _=> mul_le_mul_of_nonneg_right (ht j) (show 0≤(j.val.card:ℝ) by positivity))).trans (hD i)) o mQ
 apply le_trans _ (add_le_add (hI o) hk); unfold cubL vaultℜ nook; rw [←sum_add_distrib]; apply sum_le_sum; intro X _; change sched R _ i _ X* B t X≤ z X*B 0 X+F X
 refine (mul_le_mul_of_nonneg_right (roar V v Q q κ m z ϑ i u.1 X) (Real.exp_pos ..|>.le)).trans ?_; rw [add_mul]; exact add_le_add_left (mul_le_mul_of_nonneg_left (tap L w b T r u.1 X) (z₁ X)) _ -- tune orientation left
omit hC hD ϑ z₁ p mQ r hI
lemma height_v (hz:0≤s)(o:A)(i j:ℕ)(qj:i≤j)(t:0≤x): S o j x ≤ Θ o j x∧shelfR (K_ i x * B x) o ≤ s*Θ o j x:=by
 let U(i:ℕ):= K_ i x* B x; have hu(i:ℕ):0 ≤ U i:=fun X=> mul_nonneg (seed_nn V v Q q κ m i x t X) (Real.exp_pos ..|>.le)
 constructor; · exact sum_le_sum fun X _=> le_mul_of_one_le_right (hu j X) (T.pos _)
 unfold foe shelfR nook; rw [mul_sum]; apply sum_le_sum; intro X _; have hX:U i X ≤ U j X:= mul_le_mul_of_nonneg_right ((stair V v Q q κ m _ _ qj t) X) (Real.exp_pos ..|>.le) -- qj infer
 exact (mul_le_mul hX (T.rate _) (by positivity) (hu j X)).trans_eq (by change U j X*_=s*(U j X*b X); ring)
omit T m v q
variable (rV:flowZ V Q z V)(hz:0≤s)(pT: e+d*γ-(w-s*c)*γ < 0)
include pT T m v q hz z₁ p mQ r hI hC hD k rV hw hm
lemma road (i:ℕ)(j:A)(t:ℝ)(x:t∈Set.Icc 0 h) : S j i t < γ:=by
 suffices ∀ i:ℕ,∀ j t,t∈Set.Icc 0 h→ S j (i+1) t < γ from lt_of_le_of_lt (stair_k V v Q q κ m L w b i (i+1) j (by omega) x.1) (this i _ t x)
 intro i j t x
 refine carom h γ (fun o t=>S o (i+1) t) (fun j t=>P j i t -w*Θ j (i+1) t) (fun i' t'=>trek V κ L w b i' i t') ?_ ?_ j t x
 · intro j; rw [show S j (i+1) 0=S j 0 0 from ?_]; exact k j
   have he:K_ (i+1) 0=K_ 0 0:=by unfold seed_v bark; simp_rw [car_k]
   unfold serif; rw [he]
 intro o t' v' y q₀; obtain ⟨u,g₀⟩:= height_v V v Q q κ m L w b T hz o i (i+1) (by omega) v'.1; have he:=sans V v Q q κ m L w b T γ c d e h p r mQ z z₁ rV hC hD hI o t' v' i (fun j=>(stair_k V v Q q κ m L w b i (i+1) _ (by omega) v'.1).trans (q₀ j)); rw [y] at u; apply lt_of_le_of_lt ?_ pT; nlinarith [mul_le_mul_of_nonneg_right g₀ hm, mul_nonneg (sub_nonneg.mpr u) (sub_nonneg.mpr hw)]
end YM.CF.Cadre
