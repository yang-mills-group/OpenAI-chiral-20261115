import YM.CF.Tap.Ray
set_option autoImplicit false
noncomputable section
namespace YM.CF.Tap
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {c f:Side}(G: Ratio c f)
abbrev oneF :ℝ:= G.count.val
abbrev plot (v:Single f)(x:Cover):Single f:= ((v.1.1+wrap f x,v.1.2),v.2)
def streak (m:ℕ)(v:Single f)(x: Single c):ℝ:= gum m (dish G v x)
lemma streak_pos(m:ℕ)(v x):0≤streak G m v x:=by unfold streak gum; positivity
private lemma hopL(v:Single f)(x:Cover)(w:Single c): dish G v w ≤ (dish G (plot v x) w:ℝ)+2*(Laurent.size x)/oneF G+4:=by
 let A:=ratio G; let y:=plot v x; let i:=place_x v; let j:=place_x y; let k:=place_x w; let n:=A.count.val; let d:=separation (A.parent i) (A.parent j)
 have ht:A.count.val=G.count.val:=rfl
 have hp:n*d≤ separation i j + _:=Corona.foreshorten A i j -- might order
 have he:j=i+ wrap (More f) (2 • x):=by
    change node (v.1.1+wrap f x)=node v.1.1+_; unfold node; rw [map_add, Ratio.root_embed (assembly f) (wrap f x), Ratio.embed_wrap]; change _+wrap _ (2 • x) + 1=_; abel
 have hu: separation i j ≤ 2*Laurent.size x:=by
    rw [separation_comm,separation, he,add_sub_cancel_left]; apply Work.E01.pdist_wrap_le; rw [box_test]; have h(a): -(↑(2*Laurent.size x):ℤ)≤ (2:ℕ) • x a∧(2:ℕ) • x a ≤ (↑(2*Laurent.size x):ℤ):=by
        have hk : (x a).natAbs ≤ Laurent.size x:= Finset.single_le_sum (f:=fun b:Axis=>(x b).natAbs) (fun _ _=> Nat.zero_le _) (mem_univ a);
        simp only [nsmul_eq_mul,Nat.cast_ofNat,Nat.cast_mul]; omega
    exact ⟨fun a=> (h a).1,fun a=> (h a).2⟩
 have hh: n*d≤2*Laurent.size x+4*n:=by omega -- tune
 have hw : separation (A.parent i) k ≤ d+separation (A.parent j) k:= separation_triangle ..
 refine (le_trans (Nat.cast_le.mpr hw) ?_); unfold oneF; rw [←ht]; change ((d+separation (A.parent j) k:ℕ):ℝ)≤ separation (A.parent j) k + _+_
 have hl : (n:ℝ)*d≤ 2*Laurent.size x+4*n :=by exact_mod_cast hh
 push_cast; have hz:0<(n:ℝ):= side_pos _; change _≤ _+_/(n:ℝ)+_; field_simp; nlinarith
private lemma ship (m:ℕ)(a:ℝ)(h:0<a): ∃ C:ℝ,0<C∧∀ y:ℝ,0≤y→ gum m y≤ C*Real.exp (a*y):=by
 let x:=a/(m+1); let F:=max 1 x⁻¹; have ht:0<x:=div_pos h (by positivity); have hv:0<F:=lt_of_lt_of_le one_pos (le_max_left ..)
 refine ⟨F^m,pow_pos hv _,fun y e=>?_⟩; unfold gum; calc
   _ ≤ (F*Real.exp (x*y))^m:=by
      have hx: y≤ F*(x*y):=by rw [←mul_assoc]; exact le_mul_of_one_le_left e ((inv_le_iff_one_le_mul₀ ht).mp (le_max_right ..))
      have hp:1≤F:=le_max_left ..
      have hv:= Real.add_one_le_exp (x*y)
      refine pow_le_pow_left₀ (by positivity) ?_ _; nlinarith only [hx,hp,mul_le_mul_of_nonneg_left hv (zero_le_one.trans hp)]
   _ ≤_:=by
      rw [mul_pow,←Real.exp_nat_mul]; refine mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (by positivity); rw [←mul_assoc]; refine mul_le_mul_of_nonneg_right ?_ e; unfold x; field_simp; nlinarith
variable (h:Odd G.count.val)(T:Script Male)(j:ℕ)(e:Use j G.count T)(p:Even j)(u:Bool)(M: Male)
def pax (z:Single f)(D:List Axis)(x:Cover):Single c→ℂ:= fun y=> Rush.wind z.1.1 x * fan G h T j u M D (plot z x) y
include p e
lemma pax_e(v D i x)(s:2≤j):pax G h T j u M v (i::D) x=pax G h T j u M v D (x+step i)-pax G h T j u M v D x:=by
 obtain ⟨⟨r,a⟩,l⟩:=v; ext y; let F:=plot ((r,a),l) x; unfold pax plot; dsimp only [Pi.sub_apply,Prod.fst]; rw [fans G h T j e p u M s, map_add,wrap_step,←add_assoc r]; let t:=r+wrap f x; suffices he: Rush.wind r x * seam (anticut f) (r+wrap f x) i= Rush.wind r (x+step i) by rw [←he]; ring
 let Y:=t+step i; let K:Site f:=0; let ρ:= frequency K
 apply mul_right_cancel₀ (show ρ Y≠0 from by intro hg; have he:star (ρ Y)*(ρ Y)=1:= frequency_unit ..; rw [hg,mul_zero] at he; exact zero_ne_one he)
 have ht: t=r+wrap f x:=rfl; rw [mul_assoc, ←seam_eq (r+wrap f x) i]; change _* (Rush.wind t _ *ρ Y)= _; let H:= Laurent.mode (mel K); rw [show Rush.wind t (step i) *ρ Y=ρ t*H (step i) from ?_, ←mul_assoc,show Rush.wind r x*ρ t=ρ r*H x from freq_advance .., mul_assoc, ←mode_shift]; apply Eq.symm; have hk:=freq_advance K r (x+step i); rw [map_add,wrap_step,←add_assoc] at hk; exact hk
 have hk:=freq_advance K t (step i); rw [wrap_step] at hk; exact hk
omit G h T e M
lemma ferryY(m:ℕ)(D:List Axis)(hx:D.length+2≤j):∃ C:ℝ,0<C∧∀ {c f:Side}(G:Ratio c f)(h:Odd G.count.val)(T:Script Male), Use j G.count @T → ∀ M v x, let r:ℝ:=Laurent.size x; paidX (streak G m v) (pax G h T j u M v D x)≤ C* followV D G.count * (1+r/oneF G)^m:=by
 obtain ⟨a,C,hA,hC,H⟩:=ferry j p u D hx; obtain ⟨F,hF,K⟩:= ship m a hA; refine ⟨(8:ℝ)^m*F*C,by positivity,fun {c f} G h T e M v x=>?_⟩; intro r
 let z:=r/oneF G; have hl:0<oneF G:= side_pos _; have hg:0≤r:=Nat.cast_nonneg _; have ht:0≤z:=by unfold z; positivity
 let y:= plot v x; let A:=(8:ℝ)^m*F*(1+z)^m
 have hp(w): streak G m v w ≤ A * bolt a G y w:=by
    have h':= hopL G v x w; change (dish G v w:ℝ)≤ dish G y w+2*r/oneF G+4 at h'; rw [mul_div_assoc] at h'; let d:ℝ:=dish G y w; have hv:0 ≤ d:=Nat.cast_nonneg _
    unfold A bolt; change _ ≤ _*Real.exp (a*d)
    calc
      _ ≤ ((8*(1+z))*(1+d))^m:=by
         unfold streak gum; refine pow_le_pow_left₀ (by positivity) ?_ _; change ↑(dish G v w)≤ d+2*z+4 at h'; nlinarith
      _ ≤ _:=by rw [mul_pow, mul_pow]; apply le_trans (mul_le_mul_of_nonneg_left (K d hv) (by positivity)); exact le_of_eq (by ring)
 unfold paidX; apply le_trans _ ((mul_le_mul_of_nonneg_left (H G h T e M y) (by unfold A; positivity:0≤A)).trans ?_)
 · rw [mul_sum]; apply sum_le_sum; intro i _; unfold pax; rw [norm_mul,show ‖Rush.wind v.1.1 x‖=1 from fee_norm _,one_mul,←mul_assoc]; exact mul_le_mul_of_nonneg_right (hp i) (norm_nonneg _)
 unfold A z; exact le_of_eq (by ring)
end YM.CF.Tap
