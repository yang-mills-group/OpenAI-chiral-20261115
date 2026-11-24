import YM.CF.Mint.Key
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mint
open Function NormedSpace Filter Finset Graph Lattice Laurent Wilson Analysis Pressure
open scoped Topology ContDiff InnerProductSpace BigOperators
variable {x y A B:ℕ→ℝ}
variable {N:ℕ→Side}{c b w r:ℝ}{β θ L:ℕ→ℝ}
open Tulip Lat Cube SU Emu Rush Scree Graph RG
variable (P:RangeH x β c b)
lemma Gray.eqK {F G:ℕ→ℝ}(p:Gray A F)(h:F=ᶠ[atTop] G):Gray A G:=by obtain ⟨c,p,u,v⟩:=p; exact ⟨c,p,u,(h.and v).mono fun i e=>e.1 ▸ e.2⟩
def hemp(x:ℕ→ℝ)(i:ℕ):ℝ:= (Real.sqrt (x i))⁻¹ /4
namespace RangeH
include P
variable (p:Gray (lum x) (eur N))
lemma helm:∀ᶠ i in atTop,0<hemp x i∧hemp x i ≤1∧4*hemp x i≤tame x i:=by
 filter_upwards [P.rank.eventually_ge_atTop 1] with i e; have hp:1≤x i:=e; have he:1≤Real.sqrt (x i):=by nlinarith only [hp,Real.sq_sqrt (show 0≤x i from zero_le_one.trans hp),Real.sqrt_nonneg (x i)]
 unfold hemp; refine ⟨by positivity,?_,?_⟩
 · refine le_trans (div_le_self (by positivity) (by norm_num)) (inv_le_one_of_one_le₀ he)
 unfold tame temp; rw [show 4*((Real.sqrt (x i))⁻¹/4)=(Real.sqrt (x i))⁻¹ by ring]; exact le_mul_of_one_le_right (by positivity) (Real.one_le_exp (sq_nonneg _))
include p
lemma plush (D h:ℝ)(g:Gray (lum x) L): Aqua (lum x) fun i=> stoutY (N i) (β i) (4*hemp x i) h (tame x i) D (L i) * (vast x i)⁻¹ :=by
 let A':= lum x; have he:= tc P.rank; let B(t:ℕ):ℝ:=Fintype.card (Face (Per (N t))); let v:=h/2+D^2/2
 have hB:Gray (lum x) B:= ((((p.powG he 4).mul (Gray.coef he (Fintype.card PlaqAxes:ℝ)))).eqK (Eventually.of_forall fun i=>by
    change eur N i^4*_ = _; rw [show B i= _ from (show B i=(Fintype.card (Site (N i)×PlaqAxes):ℝ) from rfl),Fintype.card_prod,site_card, Nat.cast_mul,Nat.cast_pow]))
 have hv:= ((frost P.rank).fed (((P.ratio_v.mul hB).mul (Gray.coef he v))) he); refine (hv.panel (P.tax_p D p g)).changeA ?_
 filter_upwards [P.infl] with i ⟨e,t,u,b⟩; change (β i/x i*B i*v)*_ +_ = _; unfold stoutY goldY hemp; rw [add_mul]; congr 2 -- tune
 have he:= Real.sq_sqrt e.le; change _= β i*(B i*_); unfold v; field_simp; grind
lemma gate: Gray (lum x) fun i=>Real.log (gainS (N i) (hemp x i)):=by
 let F':ℝ:= (Module.finrank ℝ SU.group.Mat); let C:=Real.log (4:ℝ); have he:=tc P.rank; let G(i):= -(lum x i)/2 + (-C) + (-C); have hg: Gray (lum x) G:=by
    refine Gray.add he (Gray.add he ?_ (Gray.coef he (-C))) (Gray.coef he (-C)); simpa [div_eq_mul_inv] using (Gray.arg he).neg.mul (Gray.coef he (2:ℝ)⁻¹)
 refine ((((Gray.coef he 4).mul (p.powG he 4)).mul ((Gray.coef he F').mul hg))).eqK ?_
 filter_upwards [P.infl] with i ⟨e,v,h,b⟩; change 4*_*(F'*G i)= _; unfold gainS hemp; rw [Real.log_pow, Real.log_pow, Real.log_div (by positivity) (by norm_num),Real.log_div (by positivity) (by norm_num),Real.log_inv, Real.log_sqrt e.le]; unfold G lum F' eur C; push_cast; ring
-- $exp hU$ upper.G poly
lemma mark (C:ℝ)(h:Gray (lum x) L)(p':Gray (lum x) A): Gray (lum x) fun i=> flagT (N i) (A i) (L i) C:=by
 have he:=tc P.rank; let H:= fun k=> Gray.coef he k; have hu:=H 180|>.mul (p.powG he 4); exact Gray.add he ((H ((2:ℝ)^2*C)).mul (p.powG he 4)) (((p'.add he p'|>.add he h).mul ((P.age p).powG he 4)).add he ((hu.powG he 2).mul (hu.mul (H (45*((2+(2:ℝ)^2)*C)))))) -- syntax
end RangeH
end YM.CF.Mint
