import YM.SU5.FiniteGaugeData.ArchiveK.Gala
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.ArchiveK
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush Largo WithLp
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
namespace Midway
open Violas Concert LightK Waltz
variable {n uX i N J tX k:ℕ}{F:FilterK}{V v c r θ:ℝ}{D:ℕ}{G:E4≃ₗᵢ[ℝ] E4}(P:ZephyrG G D tX)
abbrev Genre(J:ℕ):=Bool×Fin J
def radix(u:Genre J):= if u.1 then (2*(u.2.val)+1) else 2*u.2.val
lemma radix_in : Injective (radix (J:=J)) :=by rintro ⟨i,x⟩ ⟨j,y⟩ e; unfold radix at e; dsimp only at e; cases i<;> cases j<;> simp only [Bool.false_eq_true,↓reduceIte] at e; exact Prod.ext rfl (Fin.ext (show (x.val)=(y.val) from (by omega))); exfalso; omega; exfalso; omega; exact Prod.ext rfl (Fin.ext (show x.val=y.val from by omega))
-- template assign.
structure MeterC (J:ℕ)(r:ℝ) where
 b : Genre J→ ℕ
 b_pos (x):0< b x
 stake(x): (1280:ℝ) ≤ r*b x
 polar (x y: Genre J)(g:radix x<radix y): 1280*b x ≤ r*b y
lemma taxi (J:ℕ)(t:0<r):Nonempty (MeterC J r):=by
 obtain ⟨k,h⟩:= exists_nat_gt (1280/r); have he: (1280:ℝ) ≤ r*k:=by rw [mul_comm]; exact le_of_lt ((div_lt_iff₀ t).1 h);
 have hp:0<k:=Nat.cast_pos.mp ((show 0<1280/r by positivity).trans h); let f(x:Genre J):= k^(radix x+1); have h1:k≥1:=hp; have hv:= (show 1≤(k:ℝ) from Nat.one_le_cast.mpr hp);
 refine ⟨⟨f,(fun x=> pow_pos hp _),fun x=> le_trans he (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr ?_) t.le), fun x y g=> ?_⟩⟩; · apply Nat.le_self_pow _ _; omega
 have hh: f x*k ≤ f y:= by unfold f; rw [←pow_succ]; exact pow_le_pow_right₀ h1 (by omega)
 calc
    _ ≤ r*k*f x:= by gcongr
    _ = r*(f x*k:ℕ):=by push_cast; ring
    _ ≤ _ := by gcongr
-- choose stride. L_n.E common aperture water.Shore. rank divisor.M.Radii.
variable (X:MeterC J r)
abbrev foot_u (D:ℕ)(i:Genre J):= D* X.b i
def Pod (X:MeterC J r) (D:ℕ)(Q:ℕ) (p:ℕ):= (∏ i:Genre J, foot_u X D i)*Q*p -- def path namespace? X.foot_u require `MeterC.foot_u`. else error.
namespace MeterC
abbrev tall(D:ℕ)(i:Genre J):=foot_u X D i
def knot(D Q:ℕ):= Pod X D Q
local notation "Ω"=> X.tall D
local notation "Y"=>Genre J
variable {Q:ℕ}(t:0<Q)(u:0<D)
def scale(D Q:ℕ)(x:Y)(n:ℕ):= n*Q*(∏ j∈ (@univ Y _).erase x,X.tall D j)
def divKH (D Q:ℕ)(n:ℕ):= X.knot D Q n / Q
include t u
lemma big_b(x:Y):0<X.tall D x:= mul_pos u (X.b_pos _)
lemma scale_q(x:Y)(n:ℕ): X.scale D Q x n * X.tall D x = X.knot D Q n:=by
 unfold scale knot Pod; have he:=Finset.prod_erase_mul _ (f:=X.tall D) (Finset.mem_univ x); rw [mul_assoc, he]; unfold tall; ring
lemma knot_div(n:ℕ) : X.divKH D Q n * Q= X.knot D Q n:=by apply Nat.div_mul_cancel; unfold knot Pod; exact dvd_mul_of_dvd_left (dvd_mul_left ..) _
lemma scaleT(x:Y):Tendsto (X.scale D Q x) atTop atTop:= StrictMono.tendsto_atTop (strictMono_nat_of_lt_succ (fun n=>Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right (Nat.lt_add_one _) t) (Finset.prod_pos (fun i _=>mul_pos u (X.b_pos _)))))
lemma knotT:Tendsto (X.knot D Q) atTop atTop:= StrictMono.tendsto_atTop (strictMono_nat_of_lt_succ (fun x=> Nat.mul_lt_mul_of_pos_left (Nat.lt_add_one _) (mul_pos (Finset.prod_pos fun i _=> (mul_pos u (X.b_pos _))) t)))
omit t u
-- spectrum cutoff independent D.L hire F version. always V bound 2000*max b. need m≥4V. 
lemma cap_l : ∃ V:ℝ,0<V∧∀ D:ℕ,0<D→∀ i:Y,2000*X.tall D i/D≤ V:=by
 obtain ⟨b,k⟩:= Set.finite_range (fun i:Y=>2000*(X.b i:ℝ)) |>.bddAbove; refine ⟨|b|+1,by positivity,fun D h i=> le_trans (le_of_eq (b:=2000*(X.b i:ℝ)) ?_) ((k (Set.mem_range_self i)).trans ((le_abs_self b).trans (le_add_of_nonneg_right zero_le_one)))⟩; unfold tall foot_u; push_cast; field_simp
end MeterC
local notation "Γ"=> emitX
-- radii statements. `RoomW` both.A property. ∀ sphere algebra.Ac. geometric clearance relative L=χ. orient comp signs straight.
def LaneR (b:Bool)(a:Axis)(x:E4):ℝ:= if b then x a else -x a
structure SunK (b:Bool)(r:ℝ)(x:Cover):Prop where
 fence(a:Axis) : r ≤ LaneR b a (Γ x)
 roof : ‖Γ x‖ ≤ 40*r -- bug.Hello tune choose base λ=qD not 5 (r stored qD) adjust fence
namespace SunK
variable {x:Cover}(b':Bool){b c:Bool}{r:ℝ}
lemma shoe (h:SunK b r x): r≤ ‖Γ x‖:=by
 let a:Axis:=0; let Q:= h.fence a; exact Q.trans (le_trans (by unfold LaneR; split; exact le_abs_self _; exact neg_le_abs _) (arm_abs _ a))
abbrev Ulb(x:Cover) :Cover:= if b' then x else -x
lemma mirror (h:SunK b r x): SunK (!b) r (-x) := by
 constructor; · intro i; have hv:= h.fence i; cases b<;> simpa [LaneR,emit_neg] using hv
 rw [emit_neg,norm_neg]; exact h.roof
lemma stirke (h:SunK true r x): SunK b' r (tax b' x):=by cases b'; exact mirror h; exact h
lemma stit (h:SunK false r x): SunK (!b') r (tax b' x):=by cases b'; exact mirror h; exact h
end SunK
section weather
variable {B Q q w:ℕ}(z:0<Q)(u:0<r)
def ray (D Q n:ℕ)(i:Genre J):ℝ:= ((X.scale D Q i n:ℕ):ℝ)*(D:ℝ)
local notation "Y" => Genre J
include z
lemma ph (a:0<D)(i:Y) : ray X D Q n i= X.knot D Q n / (X.b i:ℝ) := by
 have ht:= X.scale_q z a i n; let s:= X.scale D Q i n; let b:= X.b i; have hb:= (show 0<(b:ℝ) from Nat.cast_pos.mpr (X.b_pos _)); apply (eq_div_iff hb.ne').mpr; change _* _= ((X.knot D Q n:ℕ):ℝ); unfold ray; rw [←ht, MeterC.tall, foot_u]; push_cast; ring
lemma RayT(a:0<D)(i:Y):Tendsto (fun n=>ray X D Q n i) atTop atTop:= ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp (X.scaleT z a i)).atTop_mul_const (Nat.cast_pos.mpr a)
lemma pricing (i j:Y)(p:radix i<radix j)(a:0<D) : 1280*ray X D Q n j ≤ r*ray X D Q n i:=by
 rw [ph X z a j,ph X z a i,← mul_div_assoc, ← mul_div_assoc]; have hv(x:Y):0<(X.b x:ℝ):= Nat.cast_pos.mpr (X.b_pos x); rw [div_le_div_iff₀ (hv j) (hv i)]; nlinarith only [mul_le_mul_of_nonneg_right (X.polar _ _ p) (Nat.cast_nonneg (α:=ℝ) (X.knot D Q n))]
lemma ext_pay (a:0<D)(i:Y) : 1280*ray X D Q n i ≤ r * X.knot D Q n:=by
 rw [ph X z a,←mul_div_assoc,div_le_iff₀ (Nat.cast_pos.mpr (X.b_pos _))]; nlinarith only [mul_le_mul_of_nonneg_right (X.stake i) (Nat.cast_nonneg (α:=ℝ) (X.knot D Q n))]
omit z
lemma tan_S (p:w^3≤ q)(j:Stamp q w)(b:Bool)(z:Cover)(u:‖Γ z‖ ≤ (q:ℝ)*D): SunK b ((q:ℝ)*D) (actor P q w j b-z):=by
 let a:= actor P q w j b; let r:= (q:ℝ)*(D:ℝ); have hp: 0 ≤ r:= by unfold r; positivity; -- precedence
 constructor; · intro i; have he:= sign_R P q w j b i; have hh:= abs_le.mp ((arm_abs (Γ z) i).trans u); rw [emit_sub]; change r ≤ LaneR b i _; unfold LaneR; cases b<;> simp only [PiLp.sub_apply,Bool.false_eq_true,↓reduceIte] at * <;> unfold r at * <;> nlinarith only [hp, he,hh.1,hh.2]
 rw [emit_sub]; refine (norm_sub_le ..).trans ((add_le_add (square_R P q w p j b) u).trans ?_); unfold r at *; nlinarith only [hp]
-- disjoint across class via River
variable {x y:Cover}{b b':Bool}{τ₁ τ₂:ℝ}(p:SunK b τ₁ x)(u':SunK b' τ₂ y)(h:0<τ₁)(t1:1280*τ₂ ≤ r*τ₁) (e₁:r≤1)
include p u' h t1 u
lemma RiverR (v:100<τ₁) : River r (emitX x) (emitX y):= ⟨lt_of_lt_of_le v (p.shoe), le_trans (b:=32*(40*τ₂)) (mul_le_mul_of_nonneg_left u'.roof (by norm_num)) (by nlinarith only [t1,mul_le_mul_of_nonneg_left p.shoe u.le])⟩
include e₁
lemma apartK : x≠y:=by intro v; subst y; nlinarith only [p.shoe,u'.roof,t1,mul_le_mul_of_nonneg_right e₁ h.le,h]
end weather
#print axioms apartK
end Midway
end YM.CF.Window.ArchiveK
