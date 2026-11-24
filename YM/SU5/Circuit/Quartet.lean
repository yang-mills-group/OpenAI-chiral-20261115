import YM.SU5.Circuit.Lark
import YM.SU5.Circuit.Oriole
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Regis.Head.Brecht
open Function Filter Metric Lattice Laurent Next.Free Bloch Finset Exterior Precision RG Work.F03 Gleam MeasureTheory NormedSpace ProbabilityTheory Wilson Matrix
open Circuit
open scoped Matrix Topology BigOperators NNReal ENNReal InnerProductSpace
variable {E: Type*}[NormedAddCommGroup E][InnerProductSpace ℝ E][MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E] {ι:Type*} [Fintype ι]
local notation "μ" =>stdGaussian E
local notation "ℓ"=>(Fintype.card ι:ℝ)
variable (F G:ι→ E)
def talents (n: ℕ)(x:E):ℝ:= ∑ i, inner ℝ (F i) x^(n*2)
lemma talent_non(n:ℕ)(x:E):0≤ talents F n x:=sum_nonneg fun i _=> by rw [pow_mul]; positivity
lemma capT(n:ℕ)(x:E): talents F n x ^2 ≤ ℓ* talents F (2*n) x:=by
 have he:= sum_mul_sq_le_sq_mul_sq univ (fun _ : ι=> (1:ℝ)) (fun i=>inner ℝ (F i) x^(n*2)); have hy(i): (inner ℝ (F i) x^(n*2))^2= (inner ℝ (F i) x)^(2*n*2) := by rw [← pow_mul]; rw [show n*2*2=2*n*2 from by ring]
 simpa only [one_mul,sum_const,one_pow,card_univ,nsmul_eq_mul,mul_one,talents,hy] using he
lemma partT(n:ℕ): MemLp (talents F n) 2 μ:= memLp_finsetSum univ (fun i _=> coats (F i) _)
abbrev coalK (x:E) := talents F 1 x
lemma fondum : (∫ x, coalK F x ∂μ)=∑ i, ‖F i‖^2:=by
 unfold coalK talents; rw [integral_finsetSum]; swap; · exact fun _ _=>curtain ..
 apply sum_congr rfl; intro i _; rw [← real_inner_self_eq_norm_sq,← appraisal]; simp only [one_mul,pow_two]
lemma workDuet : (∫ x, coalK F x * coalK G x∂μ)= (∫ x,coalK F x∂μ)*(∫ x,coalK G x∂μ)+2*∑ i, ∑ j,inner ℝ (F i) (G j)^2:=by
 let V(i j:ι)(x:E):= inner ℝ (F i) x^2 *inner ℝ (G j) x^2
 have hv(i j:ι): Integrable (V i j) μ:=(coats (F i) 2).integrable_mul (coats (G j) 2)
 have he(x): coalK F x * coalK G x=∑ i,∑ j,V i j x:=sum_mul_sum ..
 simp_rw [he]; rw [integral_finsetSum]; swap; · exact fun _ _=>integrable_finsetSum _ (fun i _=>hv _ _)
 simp_rw [integral_finsetSum univ (fun i _=>hv _ i)]; rw [fondum,fondum]; unfold V; simp_rw [duet, sum_add_distrib,← mul_sum, ← sum_mul] -- tune
local notation "Θ" n:max => (partT F n).integrable (show (1:ℝ≥0∞)≤2 by norm_num)
variable {B:ℝ}(h:0 ≤ B)(u: ∀ i,‖F i‖ ≤ B)
def balboa (B:ℝ)(ι:Type*) [Fintype ι] := 105*B^8*(Fintype.card ι:ℝ)
include u h
lemma tin_four : (∫ x,talents F 4 x ∂μ) ≤ balboa B ι:=by
 unfold talents balboa; rw [integral_finsetSum]; swap; · exact fun _ _=>curtain ..
 refine (Finset.sum_le_sum (g:=fun _=>105*B^8) (s:=univ) (fun i _=>?_)).trans (le_of_eq ?_)
 · change (∫ x,inner ℝ (F i) x^8∂ μ) ≤ _; rw [houston]; gcongr; exact u _
 simp; ring
omit u h
lemma tributeV (x:E) : coalK F x^4≤ℓ^3 * talents F 4 x:=by
 have he: coalK F x ^2 ≤ ℓ * talents F 2 x:= capT F 1 x; have hx: talents F 2 x^2 ≤ ℓ * talents F 4 x:= capT F 2 x
 calc _=(coalK F x^2)^2:=by ring
      _≤_:= le_trans (pow_le_pow_left₀ (sq_nonneg _) he _) (by rw [mul_pow]; exact (mul_le_mul_of_nonneg_left hx (sq_nonneg _)).trans_eq (by ring))
-- cutoff f^2
variable {k:ℝ}(p:0 < k)
def viewμ (k x:ℝ):= x/(1+x/k)
include p
lemma clipμ (x:ℝ)(q:0≤x): let y:=viewμ k x; 0≤y ∧ y≤ k ∧ y ≤ x ∧ x-y ≤ x^2/k:=by
 intro y; have hv :0 < 1+x/k:=by positivity
 have he:y*(1+x/k)=x:=div_mul_cancel₀ x hv.ne'
 have hx:y≤ x:=div_le_self q (le_add_of_nonneg_right (div_nonneg q p.le))
 refine ⟨div_nonneg q hv.le,?_,hx,?_⟩; · unfold y viewμ; rw [div_le_iff₀ hv]; field_simp; nlinarith only [p, q]
 have ht: y*(x/k)≤ x*(x/k):=mul_le_mul_of_nonneg_right hx (div_nonneg q p.le); calc _= y*(x/k):=by linarith
                                                                                     _ ≤ _:= ht.trans_eq (by ring)
lemma clipped : MemLp (fun x=> viewμ k (coalK F x)) 2 μ:=by
 refine MemLp.of_bound ?_ k (ae_of_all _ fun i=>?_)
 · unfold viewμ coalK talents; apply Measurable.aestronglyMeasurable; fun_prop
 obtain ⟨e,t,_⟩:= clipμ p _ (talent_non F 1 i); rwa [Real.norm_eq_abs,abs_of_nonneg e]
variable (b:∀ i,‖G i‖ ≤ B)
-- Error universal for ρ ≤2 priced from actual B
local notation "H"=> balboa B ι
def sizingμ (ι:Type*) [Fintype ι](B:ℝ): ℝ:= 2*(2+(Fintype.card ι:ℝ)^3 * (balboa B ι+balboa B ι))
include h u
lemma clipD : let z:= ∫ x, coalK F x∂μ; let y:= ∫ x,viewμ k (coalK F x)∂μ; 0≤y ∧ y≤z ∧ z≤ ℓ*B^2 ∧ z-y≤ (1 + ℓ^3*H)/k:=by
 intro z y
 have he:= Θ 1; have hp:= (clipped F p).integrable (show (1:ℝ≥0∞)≤2 by norm_num)
 have hx: ∀ i,0 ≤ viewμ k (coalK F i)∧ viewμ k (coalK F i) ≤ coalK F i:= fun i=>⟨(clipμ p _ (talent_non ..)).1,(clipμ p _ (talent_non ..)).2.2.1⟩
 refine ⟨integral_nonneg (fun i=> (hx i).1), integral_mono hp he (fun i=> (hx i).2), ?_, ?_⟩
 · unfold z; rw [fondum]; refine (sum_le_sum (g:=fun i=>B^2) (fun i _=>pow_le_pow_left₀ (norm_nonneg _) (u i) 2)).trans (le_of_eq (by simp)) -- tune
 unfold z y; rw [← integral_sub he hp]
 calc _ ≤ ∫ x,(1+ℓ^3*talents F 4 x)/k ∂μ:=by
             refine integral_mono (he.sub' hp) ((Integrable.fun_add (integrable_const (1:ℝ)) ((Θ 4).const_mul (ℓ^3))).div_const k) (fun x=> ?_); apply (clipμ p _ (talent_non F 1 x)).2.2.2.trans; refine div_le_div_of_nonneg_right ?_ p.le; change _^2 ≤ _; have ht:0≤ coalK F x:=talent_non ..; nlinarith [sq_nonneg ((coalK F x)^2-1/2),tributeV F x]
      _ ≤ _ := by rw [integral_div, integral_add (integrable_const (1:ℝ)) ((Θ 4).const_mul (ℓ^3)), integral_const_mul, integral_const]; simp only [probReal_univ,one_smul]; gcongr; exact tin_four F h u
include b
lemma clipE : let X:=∫ x, coalK F x * coalK G x∂μ; let Y:=∫ x, viewμ k (coalK F x) *viewμ k (coalK G x)∂μ; Y ≤ X ∧ X-Y≤ sizingμ ι B/k:=by
 intro X Y; have hx: Integrable (fun x=>coalK F x *coalK G x) μ:= (partT F 1).integrable_mul (partT G 1); have hy: Integrable (fun x=> viewμ k (coalK F x)*viewμ k (coalK G x)) μ:= (clipped F p).integrable_mul (clipped G p)
 have ht(i):0 ≤ coalK F i:= (talent_non ..); have hv(i):0≤ coalK G i:=talent_non ..
 constructor; · refine integral_mono hy hx (fun i=> ?_); exact mul_le_mul (clipμ p _ (ht i)).2.2.1 (clipμ p _ (hv i)).2.2.1 (clipμ p _ (hv i)).1 (ht i)
 unfold X Y; rw [←integral_sub hx hy]; let g(x):= talents F 4 x + talents G 4 x; have hg: Integrable g μ:= (Θ 4).add ((partT G 4).integrable (show (1:ℝ≥0∞)≤2 by norm_num))
 let Z:=2/k; have hZ:0 ≤ Z:=div_nonneg (by norm_num) p.le
 calc _≤ ∫ x,(2+ℓ^3*g x)*Z ∂μ:=by
         apply integral_mono (hx.sub' hy) ((Integrable.fun_add (integrable_const (2:ℝ)) (hg.const_mul (ℓ^3))).mul_const Z); intro x; let A:= coalK F x; let B:=coalK G x
         obtain ⟨f,_,r,z⟩:= clipμ p A (ht _); obtain ⟨d,_,m,n⟩:=clipμ p B (hv _); change A*B-viewμ k A*viewμ k B≤(2+ℓ^3*g x)*Z
         have he: A^4+B^4≤ ℓ^3*g x:=by unfold g; rw [mul_add]; exact add_le_add (tributeV F x) (tributeV G x)
         have hw: A*B-viewμ k A*viewμ k B ≤ A^2/k*B+B^2/k*A:=by linarith only [mul_le_mul_of_nonneg_right z (hv x),mul_le_mul_of_nonneg_right n f,mul_le_mul_of_nonneg_left r (show 0≤ B^2/k by positivity)] -- abbreviations normalize?
         apply hw.trans; unfold Z; rw [div_mul_eq_mul_div,div_mul_eq_mul_div,← add_div,←mul_div_assoc]; gcongr; have h':A^2*B≤ A^4+B^2:=by nlinarith [sq_nonneg (A^2-B),sq_nonneg B,sq_nonneg (A^2)]
         nlinarith [sq_nonneg (B^2-A),sq_nonneg (A^2-1/2),sq_nonneg (B^2-1/2)]
      _ ≤ _:=by
         have he: ∫ x,g x ∂μ ≤ H+H:=by unfold g; rw [integral_add (Θ 4) ((partT G 4).integrable (show (1:ℝ≥0∞)≤2 by norm_num))]; exact add_le_add (tin_four F h u) (tin_four G h b) -- precedence
         rw [integral_mul_const,integral_add (integrable_const (2:ℝ)) (hg.const_mul (ℓ^3)),integral_const_mul,integral_const]; simp only [probReal_univ,one_smul]; exact (mul_le_mul_of_nonneg_right (add_le_add_right (mul_le_mul_of_nonneg_left he (by positivity : 0≤ℓ^3)) 2) hZ).trans_eq (by unfold sizingμ Z; ring)
end YM.Regis.Head.Brecht
#print axioms YM.Regis.Head.Brecht.clipE
#print axioms YM.Regis.Head.Brecht.clipD
#print axioms YM.Regis.Head.Brecht.workDuet
