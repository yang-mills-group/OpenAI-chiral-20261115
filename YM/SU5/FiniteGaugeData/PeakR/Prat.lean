import YM.SU5.FiniteGaugeData.Eight.Outlive
import YM.SU5.FiniteGaugeData.ArchiveK.Peach
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 380000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Quest
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Heat Brique Window.Brique Journey Py Py.Rate LocalLimit Preparation FullBill Steam Vale
open Largo ArchiveK.Midway Chaperone
namespace Corners
-- charges shape. arbitrary α at packing. use ∞. positive.L wrap supports.Frame.Huge. *Crags express*
set_option quotPrecheck false
variable {σ c C ζ X α b tρ v θ r:ℝ}{n l K ℓ J:ℕ}{A B S T Z A' B':Finset Cover}
abbrev TaxA(n:ℕ):= 2000000000*(n:ℝ) -- quantum Height object. ℝ
abbrev EPay :ℝ:=3000000000
abbrev helix (n:ℕ):ℕ:= 2*n+2
abbrev ceilT (n d J:ℕ):ℕ:= helix n+d+J+10
def expanse (n d J g:ℕ) := ((4:ℝ)*(2*ceilT n d J+g:ℕ))^4
abbrev dualM(n m:ℕ):ℝ:= Mirage.twinCost (perF 16384 n) (64*m)
local notation "Τ"=>tailCost
section price
lemma taxe_p : 0≤TaxA n:=mul_nonneg (by norm_num) (by positivity)
lemma ebe_pay {d:ℕ}(i u:ℕ)(e:d=u*n)(h:0< n)(J g:ℕ)(z:J+g ≤ n): expanse n d J g ≤ ((4:ℝ)* (40+2*(u:ℝ)))^4 * (n:ℝ)^4:= by
 unfold expanse ceilT helix; rw [←mul_pow]; push_cast [e]; apply pow_le_pow_left₀ (by positivity); have ht:= Nat.one_le_cast (α:=ℝ)|>.2 h; have hv: (J:ℝ)+(g:ℝ) ≤ n:=by exact_mod_cast z
 nlinarith only [ht,hv,Nat.cast_nonneg (α:=ℝ) g]
lemma boost_log (n:ℕ) (p:1≤ n) : 1+perF 16384 n ≤ Real.exp (16385*n):=by
 let x:=perF 16384 n; have he: 1 ≤ x:=Real.one_le_exp (by positivity : 0 ≤16384*(n:ℝ)); rw [show (16385:ℝ)*n= 16384*n+n from (by ring), Real.exp_add]; have h:2 ≤ Real.exp n:= le_trans (a:=2) (show 2 ≤↑n+(1:ℝ) from (by linarith only [(Nat.one_le_cast (α:=ℝ)).2 p])) (Real.add_one_le_exp _); change 1+x≤ x*_ ; nlinarith only [mul_le_mul_of_nonneg_left h (show 0≤x from zero_le_one.trans he),he]
lemma dual_pay (n:ℕ)(q:1≤ n)(m:ℕ) : dualM n m*dualM n m ≤ Real.exp (500000000*n*m):=by
 let M:= (64*m*45*4:ℕ); let x:= Real.exp (16385*n); have he:(Mirage.twinCost (perF 16384 n) (64*m)) ≤ x^M:= pow_le_pow_left₀ (add_nonneg zero_le_one (Real.exp_pos _).le) (boost_log n q) M; have ht:0≤ dualM n m:=by unfold dualM Mirage.twinCost perF; positivity
 apply le_trans (mul_le_mul he he ht (ht.trans he)); unfold x M; rw [← Real.exp_nat_mul, ←Real.exp_add]; push_cast; apply Real.exp_monotone; nlinarith only [show 0 ≤ (n:ℝ)*(m:ℝ) by positivity]
lemma Pepper (t:0≤ζ)(u:ℕ)(J g:ℕ) : ∃ i:ℕ,0 < i ∧ ∀ᶠ n: ℕ in atTop, lighting (i*n^3) (TaxA n) (dualM n (i*n^3)*dualM n (i*n^3))*Real.exp (ζ*expanse n (u*n) J g) <1/4:= by
 let K:=((4:ℝ)*(40+2*(u:ℝ)))^4; obtain ⟨i,w⟩:=exists_nat_gt (ζ*K+10); have hi:0 < i:=(Nat.cast_pos.mp (lt_trans (by unfold K; positivity) w)); refine ⟨i,hi,?_⟩; filter_upwards [eventually_ge_atTop (J+g+1)] with n h; let m:= i*n^3; let y:=Real.exp (ζ *expanse n (u*n) J g); unfold lighting
 let z:=500000000*(n:ℝ)* m; let v:=Real.exp (-(TaxA n)/2*m); change v*(_*_) * y< _
 have he:= ebe_pay i u (n:=n) rfl (by omega) J g (by omega); have ht: 1 ≤ (n:ℝ):= (Nat.one_le_cast (α:=ℝ)).2 (by omega); apply lt_of_le_of_lt (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (dual_pay n (by omega) m) (show 0 ≤ v from (Real.exp_pos _).le)) (show 0≤y from (Real.exp_pos _).le)); change v*Real.exp z*y<_; unfold v z y; rw [←Real.exp_add,←Real.exp_add]; apply lt_of_le_of_lt (Real.exp_monotone (show _ ≤ -(2:ℝ) from ?_)) ?_
 · unfold TaxA m; push_cast; have hp:=mul_le_mul_of_nonneg_left he t; have hm:=one_le_pow₀ ht (n:=4); have hz:0≤ (n:ℝ)^4:= (by positivity);
   change ζ*_ ≤ ζ*(K*(n:ℝ)^4) at hp; nlinarith only [mul_lt_mul_of_pos_right w (show 0<(n:ℝ)^4 from zero_lt_one.trans_le hm),hp,hm,show 0≤(i:ℝ)*(n:ℝ)^4 by positivity]
 have he:4<Real.exp 2:=by rw [show (2:ℝ)=1+1 from (by norm_num),Real.exp_add]; nlinarith only [Real.exp_one_gt_d9]; -- tune
 rw [Real.exp_neg, ←one_div]; exact one_div_lt_one_div_of_lt (by norm_num) he
#print axioms Pepper
end price
structure Grant (ζ c C tρ :ℝ)(l J g n m d:ℕ)(q x:ℝ) (A B A' B': Finset Cover) : Prop where
 peak : helix n≥ l
 fuel : 0<x
 budget : 0≤ q
 field : ArchiveK.Midway.Demand l n m EPay A B A' B'
 height : Real.exp (TaxA n) +1 ≤ tρ
 hot : q + Τ c C d ≤ Real.exp (-TaxA n)
 earn : 2*perF (-EPay) n+(2*Τ c C d+x*C)≤ q - Τ c C d
 price : lighting m (TaxA n) (dualM n m*dualM n m)*Real.exp (ζ*expanse n d J g) < 1/4
abbrev optionH (ζ c C :ℝ)(l J g:ℕ)(t:ℝ):= ∃ n m d q x A B A' B',Grant ζ c C t l J g n m d q x A B A' B'
#check ArchiveK.Midway.accessK
lemma bravo (ζ c C:ℝ)(l J g:ℕ) (u:0≤ζ)(h:0<c)(t:0<C): ∃ y:ℝ,optionH ζ c C l J g y:=by
 obtain ⟨D,he⟩:= exists_nat_gt (2*EPay/c); have hx: EPay ≤ c/2*D:= by rw [div_lt_iff₀ h] at he; linarith only [he]; -- tune
 obtain ⟨i,v,hy⟩:= Pepper u D J g; let P(n):= perF (-EPay) n; let Q(n:ℕ):=Real.exp (-(TaxA n)); have hp(n:ℕ):0<Q n:=Real.exp_pos _
 have ht(n:ℕ): tailCost c C (D*n) ≤ P n*C:= by unfold tailCost; gcongr; unfold P perF; apply Real.exp_monotone; push_cast; nlinarith only [mul_le_mul_of_nonneg_right hx (show 0≤(n:ℝ) by positivity)]
 have hh:∀ᶠ n:ℕ in atTop,P n*(4+8*C)<Q n/2:=by filter_upwards [surge_powers (-EPay) (-2000000000) (4+8*C) (1/2) (by unfold EPay; norm_num) 0 (by norm_num)] with n h; change _ < _ /(_ :ℝ); unfold Q TaxA; let y:= h; rw [← neg_mul]; unfold P; simp only [pow_zero,one_mul] at h; unfold perF at *; linarith only [h]
 obtain ⟨σ,Wc,f,v₀,w⟩:= pull_bar; obtain ⟨n,⟨A,B,A',B',he⟩,hX,H',hf⟩:= ((accessK f w v₀.le i l v (by unfold EPay; positivity : 0 ≤ EPay)).and_eventually (hy.and (hh.and (eventually_ge_atTop l)))).exists;
 let y:= Q n/(8*C); refine ⟨_,n,i*n^3,D*n,Q n/2,y,A,B,A',B',?_,?_,(half_pos (hp n)).le,he,le_rfl, ?_,?_,hX⟩; · unfold helix; omega
 · exact div_pos (hp _) (by positivity)
 · change Q n / 2 + _≤ Q n; nlinarith only [Real.exp_pos (-EPay* (n:ℝ)), H', ht n, mul_pos (show 0 <P n from Real.exp_pos _) t,hp n]
 have hg: y*C=Q n/8:=by unfold y; field_simp
 have hz:0 < P n:=Real.exp_pos _; -- issue placeholders order
 nlinarith only [hz,hp n,ht n, mul_pos hz t, hg, H']
#print axioms bravo
end Corners
end YM.CF.Buffered.Afterglow.Hierarchy.Quest
