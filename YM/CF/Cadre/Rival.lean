import YM.CF.Cadre.Bezel
import YM.CF.Cadre.Deluge
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
variable {x s:ℝ}(T:Tour b s) (γ c d e h:ℝ)(g:h≥0)(k:∀ o:A,serif V κ L w b o 0 0<γ)
local notation "B"=> loom_v L w b
local notation "K_"=> seed_v V κ
local notation "S"=> serif V κ L w b
variable (p:0 ≤ L-w*h) (r:0 ≤ w)(mQ:0 ≤ γ)(z:Palot.leaf A→ℝ)(z₁:0 ≤ z)
variable (hC:∀ i:A, nook (fog (loom_v L w b 0) Q γ) i ≤ c)(hD:∀ i:A,shelfR (fog (loom_v L w b 0) Q γ) i ≤ d)(hI:∀ i:A, nook (z*loom_v L w b 0) i ≤ e)(hm:0 ≤ c)(hw:s*c ≤ w)
structure Timer (V: leaf A→ Finset A→PS)(Q:leaf A→ℝ)(κ L w:ℝ)(b:leaf A→ℝ)(s γ c d e τ:ℝ)(z:leaf A→ℝ):Prop where
 keep:∀ X:leaf A,∀ D ⊆ X.val,cent (V X D)
 mid:0 ≤ Q
 slope: 1 ≤ κ
 tend:Tour b s
 ever:0 ≤ s
 pos: 0 ≤ c
 ok:0 ≤ τ
 boot:0 ≤ L-w*τ
 hop:0 ≤ w
 fin: 0 ≤ γ
 post:∀ o:A, serif V κ L w b o 0 0 < γ
 tight:∀ i:A, nook (fog (loom_v L w b 0) Q γ) i ≤ c
 win:∀ i:A, shelfR (fog (loom_v L w b 0) Q γ) i ≤ d
 gen:0 ≤ z
 birth:∀ i:A, nook (z*loom_v L w b 0) i ≤ e
 debt:s*c≤w
 share:e+d*γ-(w-s*c)*γ<0
 born:flowZ V Q z V
namespace Timer
variable {V Q κ L w b γ c d e z h}(H:Timer V Q κ L w b s γ c d e h z){α τ ℓ:ℝ}
-- kernel front.Method.L
local notation "N"=> loom_v ℓ 0 b
include H
lemma book(i:A)(t:ℝ)(p:t∈Set.Icc 0 h)(n:ℕ): S i n t ≤ γ:=by exact (road V H.keep Q H.mid κ H.slope L w b H.tend γ c d e h H.post H.boot H.hop H.fin z H.gen H.tight H.win H.birth H.pos H.debt H.born H.ever H.share n i t p).le -- signature g? copy
variable (vα:0<α)(vℓ:0≤ℓ)(qα:ℓ+α ≤ L-w*h)
include qα vα
lemma font(t:ℝ)(x:t ≤ h)(p:0≤t):N t ≤ B t:=by
 intro X; apply Real.exp_le_exp.mpr; have h0:=H.hop; refine mul_le_mul_of_nonneg_right ?_ (zero_le_one.trans (H.tend.pos X)); nlinarith
lemma pay (i:ΣA)(t:ℝ)(x:t∈Set.Icc 0 h):N t i*i.val.card≤ s*α⁻¹*B t i:=by
 have ht:b i ≥ 1:=H.tend.pos i; have hv:=Real.add_one_le_exp (α*b i); have hp:=mul_le_mul_of_nonneg_left (H.tend.rate i) (Real.exp_pos ((ℓ-0*t)*b i)).le; apply hp.trans; push_cast
 suffices hK:N t i*b i≤α⁻¹*B t i by
    change N t i*(s*b i)≤ _; rw [mul_left_comm _ s, mul_assoc s]; exact mul_le_mul_of_nonneg_left hK H.ever
 rw [←one_div, one_div,le_inv_mul_iff₀ vα]; change α*(N t i*b i) ≤ B t i; rw [mul_left_comm,show B t i=N t i*Real.exp ((L-w*t-ℓ)*b i) from ?_]; refine mul_le_mul_of_nonneg_left (le_trans (by linarith : α*b i≤Real.exp (α*b i)) ((Real.exp_le_exp).mpr ?_)) (Real.exp_pos _).le; apply mul_le_mul_of_nonneg_right; have h:=H.hop; nlinarith [x.2]; linarith
 unfold loom_v; rw [←Real.exp_add]; congr 1; ring
include vℓ
lemma subsidy (o:A)(t:ℝ)(q:t∈Set.Icc 0 h)(i:ℕ): nook (K_ i t * N t) o ≤ γ ∧ shelfR (K_ i t * N t) o ≤ s*α⁻¹*γ:=by
 have he:0≤K_ i t:=seed_nn V H.keep Q H.mid κ H.slope _ _ q.1; have ht:=H.book o t q i; constructor; · refine le_trans ?_ ht; exact sum_le_sum fun j _=> mul_le_mul_of_nonneg_left (H.font vα qα t q.2 q.1 j) (he j)
 apply le_trans ?_ (mul_le_mul_of_nonneg_left ht (mul_nonneg H.ever (inv_nonneg.mpr vα.le))); unfold serif nook shelfR; rw [mul_sum]; apply sum_le_sum; intro j _; change K_ i t j * N t j * j.val.card ≤ (s*α⁻¹)*(K_ i t j * B t j); rw [mul_assoc (K_ i t j), mul_left_comm (s*α⁻¹)]; exact mul_le_mul_of_nonneg_left (H.pay vα qα j t q) (he j)
-- R nonempty contribution.Env price via differential bounding.C off.Real.
variable (R:leaf A→Finset A→PS)(kv:∀ X:leaf A,∀ D ⊆ X.val, coeff 0 (R X D)=0)(xG:flowZ V Q 0 R)
include xG
lemma pace (o:A)(i:ℕ)(t:ℝ)(x:t∈Set.Icc 0 h):cubL R κ ℓ 0 b o i t ≤ d*γ+s*α⁻¹*γ*c:=by
 obtain ⟨a',k'⟩:=H.subsidy vα vℓ qα o t x i -- need all
 have he(X:ΣA):fog (N 0) Q γ X≤fog (B 0) Q γ X:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (H.font vα qα 0 H.ok le_rfl X) (H.mid X)) (Real.exp_pos ..|>.le)
 have ha:0 ≤ ℓ - 0*h:=by simp [vℓ]
 have ht:=sans V H.keep Q H.mid κ H.slope ℓ 0 b H.tend γ c d 0 h ha le_rfl H.fin 0 le_rfl xG (fun i'=> (sum_le_sum (s:=spark i') (fun j _=>he j)).trans (H.tight _)) (fun i'=> (sum_le_sum (s:=spark i') (fun j _=>mul_le_mul_of_nonneg_right (he j) (show 0≤(j.val.card:ℝ) by positivity))).trans (H.win _)) (fun i=> by change nook ((0:ΣA→ℝ)*_) _≤0; rw [zero_mul]; simp [nook]) o t x i (fun i'=>(H.subsidy vα vℓ qα i' t x i).1); rw [zero_add] at ht; exact ht.trans (add_le_add_right (mul_le_mul_of_nonneg_right k' H.pos) _)
include kv
lemma worth (o:A)(i:ℕ):serif R κ ℓ 0 b o i h ≤ h*(d*γ+s*α⁻¹*γ*c):=by
 let U(o:A)(i:ℕ)(t:ℝ):= serif R κ ℓ 0 b o i t; have hx(t:ℝ)(i:ℕ): U o (i+1) 0=0∧U o 0 t=0:=by 
    have hm(j:ℕ)(A:ΣA):seed_v R κ j 0 A=0:= by
       apply sum_eq_zero; intro y u; rw [show bark _ _ _ _ _=_ from car_k (R A y) j,kv _ _ (mem_powerset.mp u),mul_zero]
    have hp(t:ℝ)(A:ΣA): seed_v R κ 0 t A=0:=by
       apply sum_eq_zero; intro y u; simp only [bark,mintL,zero_add,sum_range_one,pow_zero,one_mul,kv A _ (mem_powerset.mp u),mul_zero]
    constructor; · exact sum_eq_zero fun j v=> (by simp only [Pi.mul_apply,hm,zero_mul])
    exact sum_eq_zero fun j v=> (by simp only [Pi.mul_apply,hp,zero_mul])
 cases i with
 |zero=>
         change U _ _ _ ≤ _; rw [(hx h 0).2]; have he:= H.win o; have ht:d≥0:=by apply le_trans ?_ he; exact sum_nonneg (fun X _=> by exact mul_nonneg (mul_nonneg (mul_nonneg (H.mid X) (Real.exp_pos ..|>.le)) (Real.exp_pos ..|>.le)) (show 0 ≤ (X.val.card :ℝ) by positivity))
         exact mul_nonneg H.ok (add_nonneg (mul_nonneg ht H.fin) (mul_nonneg (mul_nonneg (mul_nonneg H.ever (inv_nonneg.mpr vα.le)) H.fin) H.pos))
 |succ k=>
    let D:=d*γ+s*α⁻¹*γ*c; let Z(x):= U o (k+1) x-x*D
    have he(t:ℝ) : HasDerivAt Z (cubL R κ ℓ 0 b o k t-D) t:=by unfold Z; convert (trek R κ ℓ 0 b o k t).sub ((hasDerivAt_id' t).mul_const D) using 1 <;> first|rfl|simp
    have hz:= antitoneOn_of_deriv_nonpos (convex_Icc 0 h) ((continuous_iff_continuousAt.mpr fun i=> (he i).continuousAt).continuousOn) (fun x _=>(he x).differentiableAt.differentiableWithinAt) (fun x p=>by rw [(he _).deriv]; exact sub_nonpos.mpr (H.pace vα vℓ qα R xG o k x (interior_subset p))) ⟨le_rfl,H.ok⟩ ⟨H.ok,le_rfl⟩ H.ok
    unfold Z at hz; rw [(hx h k).1] at hz; change U o _ _≤ _; exact sub_nonpos.mp (by simpa using hz)
end Timer
end YM.CF.Cadre
