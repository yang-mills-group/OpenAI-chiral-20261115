import YM.CF.Drapes.Poster
set_option autoImplicit false
noncomputable section
namespace YM.CF.Drapes
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Finset Function Fock Filter Branch
attribute [local instance] opCStarAlgebra
variable {I Y D G : Type*}[Fintype I][Fintype Y][DecidableEq I][DecidableEq Y][TopologicalSpace D]
variable {b: Stage Y I D G}{s t:Tag b}{L:License D}{a d r q:ℝ}{A:Raw D I}
lemma alpine {d:ℝ}(h:0<d)(e:d≤1)(n:ℕ)(x:ℝ)(he:0≤x) : (1+x)^n ≤ ((d/(n+1:ℝ))⁻¹)^n *Real.exp (d*x):=by
  let a:= d/(n+1:ℝ); have ha:0<a:=by unfold a; positivity
  have hh : (n+1:ℝ)*a=d:=by unfold a; field_simp
  have hb : a≤1:= le_trans (div_le_self h.le (by simp)) e
  have hx : 1+x ≤ a⁻¹ * Real.exp (a*x) :=by rw [inv_mul_eq_div, le_div_iff₀ ha]; have ht:=Real.add_one_le_exp (a*x); linarith
  refine (pow_le_pow_left₀ (by positivity) hx n).trans ?_; rw [mul_pow]; apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← Real.exp_nat_mul]; refine Real.exp_monotone ?_; calc
    _ = (n:ℝ)*a*x:=by ring
    _ ≤ _:= mul_le_mul_of_nonneg_right (by linarith) he
lemma deck_adap (h:Crown L s t a r A)(hp:0<d)(hg:d≤1)(he:2*d≤a)(n:ℕ)(x:ℝ)(hx:0≤x)(ht:x≤1) : Street L s t n x d (fun _=> ((d/(n+1:ℝ))⁻¹)^n*r) A:=by
  obtain ⟨F,C,p,q,k⟩:=h; let K:= ((d/(n+1:ℝ))⁻¹)^n
  refine ⟨F,C,p,fun i=>?_,k⟩
  calc
    _ ≤ ∑ j, K* saleM a C i j:=by
      apply Finset.sum_le_sum; intro j _; unfold saleM; simp_rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro S _; let u:=C S i j; by_cases h:u=0; · simp [show C S i j=0 from h]
      obtain ⟨g,v,w⟩:=((p S).expo i j).triggered h; let y:ℝ:=b.F.span (b.home i) (b.home j)
      have hm:y ≤ S.card:= by unfold y; exact_mod_cast (g.lim _ v _ w).le
      have h1:(1+x*y)^n≤ K* Real.exp (d*S.card):=(pow_le_pow_left₀ (by unfold y; positivity) (add_le_add_right (le_trans (mul_le_of_le_one_left (by unfold y; positivity) ht) hm) 1) n).trans (alpine hp hg n _ (by positivity)) -- fix left
      have h2 : Real.exp (d*S.card)* rent d S≤ rent a S:=by unfold rent; rw [← Real.exp_add]; apply Real.exp_monotone; nlinarith [mul_le_mul_of_nonneg_right he (Nat.cast_nonneg S.card)]
      change (1+x*y)^n*(rent d S*u) ≤ _
      rw [← mul_assoc,← mul_assoc]; apply mul_le_mul_of_nonneg_right _ ((p S).nonn ..); exact (mul_le_mul_of_nonneg_right h1 (rent_pos ..).le).trans (le_trans (le_of_eq (mul_assoc ..)) (mul_le_mul_of_nonneg_left h2 (by unfold K; positivity)))
    _ ≤ _:=by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (q.rows _) (by unfold K; positivity)
lemma gain {r a c v:ℝ}(hr:0≤r)(ha:0<a)(hc:0<c)(hv:0<v)(m:ℕ): ∃ (w:ℕ)(ρ d:ℝ), 0<ρ∧ρ<1∧0<d∧ d≤1 ∧ 2*d≤a/2∧
    let D:= Real.exp (-a/2*w)*r; let V:= (c*(((((w+w):ℕ):ℝ)+1)^4)); ((d/(m+1:ℝ))⁻¹)^m*( V*Real.exp (2*d*V)*(D+r*(2*ρ))+D)≤v:=by
  let x:=Real.exp (-a/2); have hx:0<x:=Real.exp_pos _; have hp:x<1:= Real.exp_lt_one_iff.mpr (by linarith)
  let f(w:ℕ):=Real.exp (-a/2*w); have hf(w): f w=x^w:=by unfold f x; rw [mul_comm (-a/2),Real.exp_nat_mul]
  let D(w:ℕ):=f w*r; let V(w:ℕ):=(c*(((((w+w):ℕ):ℝ)+1)^4)); let β:= min c (a*c/4); let g(w:ℕ):= β / V w
  have hβ:0<β:=lt_min hc (by positivity); have hV(w):c≤V w:=by
    unfold V
    exact le_mul_of_one_le_right hc.le (one_le_pow₀ (by simp))
  have ht(w):0<V w := hc.trans_le (hV w); have hd(w):0<g w:=div_pos hβ (ht _)
  have hu(w): g w ≤ 1 :=by unfold g; rw [div_le_one (ht _)]; exact (min_le_left ..).trans (hV _)
  have hk (w):2*g w≤a/2 :=by unfold g; rw [←mul_div_assoc]; apply (div_le_iff₀ (ht _)).mpr; have hh:=min_le_right c (a*c/4); change β≤ _ at hh; nlinarith [mul_le_mul_of_nonneg_left (hV w) ha.le]
  let Q(w:ℕ):=((g w/(m+1:ℝ))⁻¹)^m*(V w*Real.exp (2*g w *V w)*(D w+r*(2*f w))+D w)
  let R:=c*81; have hR(w:ℕ)(hw:0<w): V w≤R*(w:ℝ)^4:=by
    have hp:(1:ℝ)≤w:= by exact_mod_cast hw
    unfold V R; rw [mul_assoc c, show (81:ℝ)*(w:ℝ)^4=(3*w:ℝ)^4 by ring]; gcongr; push_cast; linarith
  let t(n:ℕ):=(n:ℝ)^4; let A:=(m+1:ℝ)/β; let E:=Real.exp (2*β)
  have hw(w:ℕ)(p:0<w) : Q w ≤ A^m*(R*t w)^m * (3*r*E*(R*t w)*x^w + r*x^w) := by
    have he' : 2*g w*V w=2*β:=by have hc:=ht w; unfold g; field_simp
    have hh: (g w/(m+1:ℝ))⁻¹=A*V w:=by unfold g A; field_simp
    unfold Q D; rw [he',hf,hh, mul_pow]; apply mul_le_mul_of_nonneg
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (ht _).le (hR w p) _) (by unfold A; positivity)
    · calc
        _ = 3*r*E* (V w)*x^w+r*x^w:=by unfold E; ring
        _ ≤ _:=by gcongr; first| exact hR w p| unfold E; positivity
    · exact mul_nonneg (by unfold A; positivity) (pow_nonneg (ht _).le _)
    unfold E R t; positivity
  let Y(w:ℕ):= A^m*(R*t w)^m * (3*r*E*(R*t w)*x^w + r*x^w)
  have hy(k:ℕ): Summable fun w:ℕ=> (w:ℝ)^k*x^w:= summable_pow_mul_geometric_of_norm_lt_one _ (by rwa [Real.norm_of_nonneg hx.le])
  have hpY : Summable Y := by
    apply (((hy (4*m+4)).mul_left (3*A^m*R^m*r*E*R)).add ((hy (4*m)).mul_left (A^m*R^m*r))).congr
    intro w; unfold Y t; rw [pow_add, pow_mul (w:ℝ) 4]; ring
  obtain ⟨w,hw',q⟩:= ((eventually_gt_atTop 0).and (hpY.tendsto_atTop_zero.eventually (gt_mem_nhds hv))).exists
  refine ⟨w,f w,g w, Real.exp_pos _,?_,hd _,hu _,hk _,(hw w hw').trans (show Y w<v from q).le⟩
  unfold f; rw [Real.exp_lt_one_iff]; exact mul_neg_of_neg_of_pos (by linarith) (by exact_mod_cast hw')
end YM.CF.Drapes
