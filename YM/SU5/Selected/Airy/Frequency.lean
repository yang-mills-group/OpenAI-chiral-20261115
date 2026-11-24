import YM.SU5.Selected.Airy.Weave
import Mathlib.LinearAlgebra.Vandermonde
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Airy
open Function Filter Metric NormedSpace Lattice Laurent Bloch Next.Free MeasureTheory
open Ember Jill Fir Shore Real Finset
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ComplexOrder
local notation "I"=>Complex.I
local notation "φ" => 2 * π

lemma funding (x:Facet3)(v:FaceL)(u:Bool)(w:ℝ)(c:x∈ grounds): 0<summer u w x v:=by
 unfold summer; dsimp only
 let z:=tempoL x v; let k:=tempoE z
 have hk:0<k:= lt_of_lt_of_le zero_lt_one (backend v c); have hg:0<sponsor k 8:= (mul_pos (div_pos pi_pos hk) (pow_pos (weight_pos hk) 8))
 have h:k>|z 2|:=handy v c (j:=0) (by decide); obtain ⟨a,b⟩:= abs_lt.mp h
 have ht:0<sol z^8:= Even.pow_pos (by decide : Even 8) (roaring v c)
 change 0 < 2 * sol z^8 * (((k+_)*sponsor k 8)*rexp _) -- rexp?
 apply mul_pos (mul_pos (by norm_num) ht) (mul_pos (mul_pos ?_ hg) (Real.exp_pos _)); cases u <;> simp only [Bool.false_eq_true, ↓reduceIte]; all_goals change (0:ℝ)<_ <;> linarith
-- sums use raw unnormalized. later convert to $1/(2π)$ convention.
def thru (x:Facet3)(w:ℤ):= ∫t in deck,surge w t*arc (Ε x t)
def knee (x:Facet3) (u:Bool) (w:ℕ) : ℂ:= if u then thru x w else -(thru x (-w))
lemma spring (x:Facet3)(u:Bool)(w:ℕ)(p:w≥4)(c:x∈grounds): HasSum (fun v=> (summer u w x v:ℂ)) (knee x u w):=by
 cases u
 · simpa only [neg_neg,knee,Bool.false_eq_true,↓reduceIte,thru,Int.cast_neg,Int.cast_natCast] using (minus (a:= (w:ℤ)) c (by exact_mod_cast p)).neg
 simpa only [Int.cast_natCast,knee, ↓reduceIte,thru] using (plus (a:= (w:ℤ)) c (by exact_mod_cast p)) -- unfold target
abbrev node4(i:ℕ) : FaceL:= fun _=> (i:ℤ)
def dollar(x:Facet3)(v:FaceL):=Real.exp (-(tempoE (tempoL x v)))
lemma rises (x:Facet3)(c:x∈grounds) : StrictAnti ((dollar x)∘node4):=by
 intro i j e; let f(u):=tempoL x (node4 u); have hg(a:Fin 3)(s:ℕ): 0<f s a:=by
    unfold f tempoL node4 turn; push_cast; linarith only [(boundsG c a).1, show (0:ℝ)≤2*π*(s:ℝ) by positivity]
 have hp(a:Fin 3): f i a< f j a:= add_lt_add_right (mul_lt_mul_of_pos_left (by exact_mod_cast e) (by positivity)) _ -- add arith
 refine Real.exp_lt_exp.mpr (neg_lt_neg (Real.sqrt_lt_sqrt ?_ ?_))
 · exact sum_nonneg fun i _=>sq_nonneg _
 exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun t _=> pow_lt_pow_left₀ (hp t) (hg t _).le two_ne_zero)

lemma step_b (x:Facet3)(u:Bool)(v:FaceL)(w p:ℕ) : summer u (w+p:ℕ) x v = summer u w x v * dollar x v^p:=by
 unfold summer dollar; dsimp only; rw [Nat.cast_add,mul_add,Real.exp_add,mul_comm (-(tempoE (tempoL x v))) (↑p:ℝ),Real.exp_nat_mul]; ring
lemma pricedR {f : FaceL→ℂ}{k:ℂ}(p: HasSum f k)(t:∀ i,star (f i)=f i): star k=k:= by have h:= p.star; simp_rw [t] at h; exact h.unique p

-- Hermitian-positive Hankel, rank as large as wanted: layered Hankel sampling with grains after $4$ steps
-- offset can be any integer >=4. x in fixed positive Brillouin patch (we use one separated from walls).
variable (x:Facet3)(u:Bool)(n p:ℕ)(e:n≥4)(c:x∈grounds)
local notation "K"=> Op (Fin p)
def trove: Op (Fin p) := Matrix.of fun i j=> knee x u (n+i.val+j.val)
local notation "N"=>trove x u n p
include e c
lemma rankWind : (trove x u n p).PosDef:=by
 let k:= N
 let Y(v:FaceL)(i:Fin p):ℝ:= dollar x v ^ i.val
 let A(v):= summer u n x v
 have he(v:FaceL)(i j:Fin p):↑(A v)*((Y v i:ℂ)*(Y v j:ℂ))= (summer u ((n+i.val+j.val:ℕ):ℝ) x v:ℂ):= by rw [step_b,step_b]; unfold Y A; push_cast; ring
 have h(i j: Fin p): HasSum (fun v=>↑(A v)*((Y v i:ℂ)*(Y v j:ℂ))) (k i j):=by simp_rw [he]; exact spring x u _ (by omega) c
 apply Matrix.posDef_iff_dotProduct_mulVec.mpr; refine ⟨Matrix.IsHermitian.ext (fun i j=> (h j i).star.unique ?_),fun y z=>?_⟩
 · convert h i j using 1; ext v; simp [mul_comm,mul_left_comm,mul_assoc]
 let f(v:FaceL):= ∑ i: Fin p, (Y v i:ℂ) * y i
 let s (i j:Fin p)(v):= star (y i) * (↑(A v)*((Y v i:ℂ)*(Y v j:ℂ)) * y j)
 have hp (v:FaceL): ∑ i, ∑ j,s i j v = (A v * ‖f v‖^2 : ℝ):=by
   rw [Complex.ofReal_mul,←Complex.normSq_eq_norm_sq,← Complex.mul_conj]
   unfold f s; simp_rw [map_sum,Finset.sum_mul, Finset.mul_sum, map_mul]; symm; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; simp [←mul_assoc]; ring -- tune
 have hsum : HasSum (fun v=>(↑(A v*‖f v‖^2:ℝ):ℂ)) (star y ⬝ᵥ (k *ᵥ y)):=by
   have hv(i:Fin p): HasSum (fun v=> ∑ j,s i j v) (∑ j:Fin p, star (y i)*(k i j*y j)):= by
      simpa only [Finset.sum_apply] using hasSum_sum (f:=s i) (s:=Finset.univ) (fun (j:Fin p) _=>( (h i j).mul_right (y j)).mul_left _)
   simp_rw [← hp]; change HasSum _ (∑ i:Fin p, star (y i) * ∑ j:Fin p,k i j*y j); simp_rw [Finset.mul_sum]; simpa only [Finset.sum_apply] using (hasSum_sum (f:=fun i v=> ∑ j,s i j v) (s:=Finset.univ) (fun i _=> hv i)) -- signature tune
 suffices y₀: ∃ v,f v≠0 by
   obtain ⟨v,h₀⟩:=y₀; let g v:= A v*‖f v‖^2; have h (v):0≤(g v:ℂ):=RCLike.ofReal_nonneg.mpr (mul_nonneg (funding x v u n c).le (sq_nonneg _)); exact lt_of_lt_of_le (RCLike.ofReal_pos.mpr (mul_pos (funding x v u n c) (sq_pos_of_ne_zero (norm_pos_iff.mpr h₀).ne'))) (le_hasSum hsum v (fun i _=> h i))
 by_contra! g
 let V(i:Fin p):ℂ:= dollar x (node4 i.val)
 have he:Injective V:= Complex.ofReal_injective.comp ((rises x c).injective.comp Fin.val_injective)
 apply z; apply Matrix.eq_zero_of_mulVec_eq_zero (Matrix.det_vandermonde_ne_zero_iff.mpr he); ext1 i; simpa only [V,f,Y, Matrix.mulVec, dotProduct,Pi.zero_apply, Matrix.vandermonde_apply, ← Complex.ofReal_pow] using g (node4 i.val) -- tune
lemma fit : IsUnit (N) := (rankWind x u n p e c).isUnit
end YM.CF.Crest.Airy
open YM.CF.Crest.Airy
#print axioms rankWind
#print axioms fit
