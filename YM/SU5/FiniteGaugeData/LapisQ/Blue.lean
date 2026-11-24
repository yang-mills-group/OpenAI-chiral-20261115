import YM.SU5.FiniteGaugeData.LapisQ.Ocelot
/-! # A color window that filters all-coordinate near approaches in gauge-only observation. -/
set_option autoImplicit false
set_option maxHeartbeats 630000
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.SU5.FiniteGaugeData.LapisQ
open Function Finset Filter MeasureTheory ProbabilityTheory Matrix Lattice Wilson RG Precision Tree Next.Fluctuations Work.F03
open Pressure Exterior Laurent Bloch Drachma Galope Avenue Galope.Press Wrist Poeme Haute Lapis Punch Affiche Work.F06 Complex
open scoped Topology InnerProductSpace Matrix MatrixOrder RealInnerProductSpace ContDiff BigOperators NNReal ENNReal Kronecker Classical ComplexOrder
set_option quotPrecheck false
namespace Cordon
open Vulcan Willow Nosh
variable {n:Side} {ρ C Δ ε σ K:ℝ}
local notation "T"=> Site n
local notation "Q"=> Cover
local notation "P"=> Per n
-- mixing lags
abbrev day(r:ℕ) := Finset.Icc (-(r:ℤ)) (r:ℤ)
abbrev bandX (r:ℕ) := Axis × (day r)
abbrev colorX (r:ℕ):= Finset (bandX r)
abbrev periodU (s:Site n)(i:Axis): Site n:= Pi.single i (s i) -- step Fourier
variable (s p q : Site n)(a:Axis)(ℓ r:ℕ)
lemma meridian (i:Axis)(x y:Site n)(h: x i=y i) : cell (periodU s i) x= cell (periodU s i) y:=by
 unfold cell mode; congr 2; apply sum_congr rfl; intro z _; by_cases e:z=i; · subst z; rw [show lift x i=lift y i from congrArg ZMod.valMinAbs h]
 have hh:mon (periodU s i) z=0:=by simp [mon,reciprocal,Lattice.lift,periodU,e]
 rw [hh]; simp
-- mixes. downstream Ward. 
local notation "K" a:max=> periodU s a

local notation "R"=> colorX ℓ
def rail (b:Axis)(j:ℤ):Cover := j • (step b)
variable {s} in
lemma meridian_q(i:Axis)(x:Q): cell (periodU s i) (wrap n x)= cell (periodU s i) (wrap n (rail i (x i))):=by apply meridian s i; apply congrArg (fun x:ℤ=> (x:Per n)); simp [rail]
def rimX (i:bandX ℓ):ℂ:= - cell (periodU s i.1) (wrap _ (rail i.1 i.2.val))
abbrev flowU (i:Axis): Site n:= periodU s i
variable (i:colorX ℓ)
noncomputable def billX : ℂ:= ∏ j ∈ iᶜ,rimX s ℓ j
def shiftU :Site n:= ∑ j∈ i, flowU s j.1
@[simp] lemma billX_r : ‖billX s ℓ i‖ = 1:= by simp_rw [billX,norm_prod, rimX,norm_neg,cell_pay]; simp
@[simp] lemma shiftU_r : shiftU s ℓ ∅=0 := by simp [shiftU]
#check colorX
lemma wave_shiftH(x y:Site n) : cell (x+y) p= cell x p*cell y p:= by rw [cell_duality (x+y),cell_add,cell_duality x, cell_duality y]
lemma coastU (x:Site n): cell (shiftU s ℓ i) x=∏ j ∈ i, cell (flowU s j.1) x:=by
 unfold shiftU; induction i using Finset.induction_on with
 | empty=> simp [show cell (0:Site n) x=1 from (cell_duality _ x).trans (cell_origin x)]
 | insert j A h u=> rw [sum_insert h, prod_insert h,wave_shiftH,u]
lemma crook(x:Site n) : (∑ i:colorX ℓ,billX s ℓ i*cell (shiftU s ℓ i) x)= ∏ j: bandX ℓ, (cell (flowU s j.1) x+rimX s ℓ j):=by
 rw [Fintype.prod_add]; apply sum_congr rfl; intro i _; rw [coastU,billX, mul_comm]
lemma crook_off (x:Cover)(h: x a∈ day ℓ) : (∑ i:colorX ℓ,billX s ℓ i*cell (shiftU s ℓ i) (wrap n x))=0:=by
 rw [crook]; refine Finset.prod_eq_zero (Finset.mem_univ ((a,⟨x a,h⟩):bandX ℓ)) ?_; change cell (periodU s a) (wrap n x)+ -cell (periodU s a) (wrap n (rail a (x a)))=0; rw [meridian_q (s:=s) a x]; exact add_neg_cancel _
noncomputable def machine (s:Site n)(ℓ:ℕ)(p q: Site n)(f:Site n→ℂ) := ∑ i:colorX ℓ,billX s ℓ i*(f (p+shiftU s ℓ i)-f (q+shiftU s ℓ i))
def payable (ℓ:ℕ):ℝ:= 1/(2*(Fintype.card (colorX ℓ):ℝ))
lemma part_p: 0<payable ℓ:=by unfold payable; positivity
abbrev MtRequest(s:Site n)(ℓ:ℕ)(p q:Site n)(f:Site n→ℂ) := ∀ i:colorX ℓ,
 ‖f (p+shiftU s ℓ i)-f (q+shiftU s ℓ i)-(if i=∅ then (1:ℂ) else 0)‖≤ payable ℓ
lemma earnsMX(f:T→ℂ)(h:MtRequest s ℓ p q f) : (1/2:ℝ) ≤‖machine s ℓ p q f‖:=by
 let t(v:colorX ℓ):=f (p+shiftU s ℓ v)-f (q+shiftU s ℓ v); let U:= billX s ℓ ∅; let S':=machine s ℓ p q f; let H(i:colorX ℓ):=billX s ℓ i*(if i=∅ then (1:ℂ) else 0)
 have he:(∑ i,H i)=U:=by simp [H,U,mul_ite]; -- maybe no goals.N.
 have hp:‖S'-U‖≤1/2:=by
    unfold S' machine; rw [←he,←sum_sub_distrib]; apply (norm_sum_le ..).trans ((sum_le_sum (g:=fun i=> payable ℓ) (fun i _=>?_)).trans_eq ?_); -- tune goals order
    swap; · unfold H; rw [←mul_sub,norm_mul,billX_r,one_mul]; exact h i
    let S:=Fintype.card (colorX ℓ); have hP:(S:ℝ)≠0:=(by unfold S; positivity); rw [sum_const,card_univ,payable,nsmul_eq_mul]; change (S:ℝ)*_=_; field_simp; rfl
 have ht:= norm_le_norm_sub_add U S'; rw [norm_sub_rev] at ht; change 1/2 ≤ ‖S'‖; linarith only [ht,hp,show ‖U‖=1 from billX_r ..]
noncomputable abbrev tomeX(x:Site n):= cropE r (fun v => cell v x)
lemma roll_p (h:r+1<n.val)(x:Site n) : ‖tomeX r x‖ ≤ 1:=by
 unfold tomeX cropE; apply (norm_sum_le ..).trans (le_of_eq ?_); simp_rw [norm_mul,Complex.norm_real, Real.norm_of_nonneg (wind_p _),cell_pay,mul_one]; exact wind_sum h
noncomputable def lord(U:T→ℂ) (p:Site n):=∑ x:Site n,U x*cell p x
lemma lord_spread(U:T→ℂ): lore p r (lord U)= lord (fun x=>U x*tomeX r x) p:=by
 unfold lore lord tomeX cropE; simp_rw [mul_sum,wave_shiftH]; rw [Finset.sum_comm]; apply sum_congr rfl; intro x _; rw [Finset.sum_mul]; apply sum_congr rfl; intro i _; ring -- tune []; -- tune `cropE` RHS need unfold twice.
---- upper knot
lemma nap (U:T→ℂ) : machine s ℓ p q (fun t=>lore t r (lord U))=∑ x:Site n, U x * tomeX r x * (cell p x-cell q x) * (∑ i:colorX ℓ,billX s ℓ i * cell (shiftU s ℓ i) x):=by
 unfold machine; simp_rw [lord_spread,lord,←sum_sub_distrib,mul_sum,wave_shiftH]; rw [Finset.sum_comm]; apply sum_congr rfl; intro x _; apply sum_congr rfl; intro i _; ring
-- uniform family.Telescope
abbrev marketZ(r:ℕ): Finset Cover:= Fintype.piFinset (fun _=>day r)
lemma buoy (x:Site n)(h:r+1<n.val)(p':tomeX r x≠0) : ∃ y∈ marketZ r,wrap n y=x:=by
 obtain ⟨y,hz⟩:= card_pos.mp (show 0<(hatch (blockK (r+1) n) x).card from (Nat.pos_of_ne_zero (by intro v; apply p'; rw [tomeX,critic,v]; simp)))
 obtain ⟨u,w⟩:= mem_filter.mp hz; let H(i:Site n):Cover:=fun x=> (i x).val; let Y:=H (y+x)-H y; have hm(i:Site n):wrap n (H i)=i:=by funext j; simp [wrap,H] -- tune
 have hU(i):=(block_bled h).1 u i; have hW(i):= (block_bled h).1 w i
 refine ⟨Y,Fintype.mem_piFinset.mpr (fun i=>?_ ),?_ ⟩
 · apply Finset.mem_Icc.mpr; change -(r:ℤ)≤ _ ∧ _; unfold Y H; simp only [Pi.sub_apply,Pi.add_apply]; have v:= hU i; have w:=hW i; simp only [Pi.add_apply] at w; omega -- tune natural abs
 unfold Y; rw [map_sub,hm,hm]; abel
lemma capeH : (∑ i∈ marketZ r, 1) = (marketZ r).card:=by simp -- bind type `1` inferred.. remove
-- Count offset in true lifts. no injection assumed. Native coupons only.
abbrev lapse (x:Cover): Prop:= ∀ i:Axis,(x i)∉ day ℓ
abbrev tariffMX(r ℓ:ℕ)(c:ℝ):ℝ:= (marketZ r).card*(c*2*Fintype.card (colorX ℓ))
lemma priceMX (U:T→ℂ) (h:r+1<n.val)(p0:0≤C)(v0: ∀ y∈ marketZ r,lapse ℓ y→‖U (wrap _ y)‖ ≤ C): ‖machine s ℓ p q (fun t=>lore t r (lord U))‖ ≤ tariffMX r ℓ C:=by
 let A:= marketZ r; let Kt:= (A.image (wrap n)); let Y:= (Fintype.card (colorX ℓ):ℝ); let x:= C*2*Y; let m(z:Site n):=∑ i:colorX ℓ,billX s ℓ i*cell (shiftU s ℓ i) z; let f(z:Site n):= U z*tomeX r z*(cell p z-cell q z)*m z; have hx:0≤x:=by unfold x Y; positivity
 rw [nap]; change ‖∑ z,f z‖ ≤ _; rw [←sum_subset (f:=f) (subset_univ Kt)]
 swap
 · intro i _ v; by_cases he:tomeX r i=0; · simp [he,f]
   
   obtain ⟨y,q,rfl⟩:= buoy r i h he; exact False.elim (v (mem_image_of_mem _ q))
 have he(i:Site n):‖m i‖ ≤ Y:=by unfold m; apply (norm_sum_le ..).trans_eq; simp_rw [norm_mul,billX_r,cell_pay,mul_one,sum_const,card_univ,nsmul_eq_mul,mul_one]; rfl
    
 have hv(z:Site n)(p':z∈Kt): ‖f z‖≤ x:=by
    obtain ⟨z,t,rfl⟩:=mem_image.mp p'; unfold f; let w:=wrap n z; by_cases v:lapse ℓ z; swap; · unfold lapse at v; push Not at v; obtain ⟨i,z'⟩:=v; rw [show m (wrap _ z)=0 from crook_off s i ℓ z z',mul_zero,norm_zero]; exact hx
    simp_rw [norm_mul]; apply mul_le_mul _ (he w) (norm_nonneg _) (by positivity : 0 ≤ C*2);
    refine mul_le_mul ((mul_le_of_le_one_right (norm_nonneg _) (roll_p r h w)).trans (v0 z t v)) ?_ (norm_nonneg _) p0
    exact (norm_sub_le ..).trans (by rw [cell_pay,cell_pay]; norm_num)
 apply (norm_sum_le ..).trans ((sum_le_sum hv).trans ?_); rw [sum_const, nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right _ hx; exact_mod_cast card_image_le
end Cordon
end YM.SU5.FiniteGaugeData.LapisQ
#print axioms YM.SU5.FiniteGaugeData.LapisQ.Cordon.earnsMX
#print axioms YM.SU5.FiniteGaugeData.LapisQ.Cordon.priceMX
