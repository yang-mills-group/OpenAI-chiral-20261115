import YM.CF.Jet.Sam
set_option autoImplicit false
noncomputable section
namespace YM.CF.Gas
set_option linter.unusedSimpArgs false
open Function Filter Metric Finset NormedSpace Jet Planned.AtomRegular
open scoped Topology BigOperators ContDiff
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
section s
variable {Y: Type}[NormedCommRing Y][NormedAlgebra ℝ Y]
variable {f g:E→Y}{k:ℕ}{C a:ℝ}{x:E}
lemma nob_k (h:0≤a)(l:ContDiffAt ℝ (↑k:WithTop ℕ∞) f x)(s:ContDiffAt ℝ (↑k:WithTop ℕ∞) g x):noble a k (fun x=> f x*g x) x≤∑ i∈range (k+1), noble a i f x*noble a (k-i) g x:=by
 obtain ⟨U,hU,i,t⟩:= open_patch l; obtain ⟨V,hV,j,p⟩:=open_patch s
 have hw:=i.inter j; have hx:x∈U∩V:= ⟨hU,hV⟩; have ht:=norm_iteratedFDerivWithin_mul_le (t.mono Set.inter_subset_left) (p.mono Set.inter_subset_right) hw.uniqueDiffOn hx (n:=k) le_rfl
 simp_rw [iteratedFDerivWithin_of_isOpen _ hw hx] at ht
 unfold noble
 calc
   _ ≤ _ := mul_le_mul_of_nonneg_left ht (by positivity)
   _ = _:=by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi
      have hi := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      let j := k-i
      have hh : (k.factorial:ℝ)=k.choose i*i.factorial*j.factorial := by exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hi).symm
      rw [show a^k=a^i*a^j by rw [←pow_add]; exact congrArg _ (by unfold j; omega),hh]
      have hr: 0<(k.choose i:ℝ):= Nat.cast_pos.mpr (Nat.choose_pos hi)
      unfold j at *; field_simp
lemma pot_k (h:0≤a)(l:ContDiffAt ℝ (↑k:WithTop ℕ∞) f x)(s:ContDiffAt ℝ (↑k:WithTop ℕ∞) g x):potash a k (fun x=> f x*g x) x≤ potash a k f x *potash a k g x:=by
 let A (i:ℕ):= noble a i f x; let B (i:ℕ):=noble a i g x
 let R:= Finset.range (k+1)
 unfold potash; change (∑ i∈ R,_ ) ≤ (∑ i∈R,A i)* ∑ i∈R,B i; rw [Finset.sum_mul_sum]
 calc
   _ ≤ ∑ i∈ R, ∑ j∈ Finset.range (i+1), A j * B (i-j) := by
      apply sum_le_sum; intro i hi
      have he:i≤k:= Nat.le_of_lt_succ (mem_range.mp hi)
      exact nob_k h (l.of_le (by exact_mod_cast he)) (s.of_le (by exact_mod_cast he))
   _ ≤ _ := by
      let p (i:ℕ):= Finset.antidiagonal i
      let v (d:ℕ×ℕ) := A d.1*B d.2
      simp_rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j=> A i*B j)]; change (∑ i∈R,∑ d∈ p i, v d)≤_
      rw [← Finset.sum_biUnion, ←Finset.sum_product'] -- tune
      · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i t n=> mul_nonneg (pos_nob h _) (pos_nob h _)); rintro ⟨i,j⟩ hp
        obtain ⟨l,g,v⟩:=mem_biUnion.mp hp; rw [mem_product]; change l∈range _ at g; change (_,_)∈ Finset.antidiagonal _ at v; simp only [Finset.mem_antidiagonal] at v; simp only [R,mem_range,Prod.fst,Prod.snd] at *; omega
      intro i _ j _ ht; apply disjoint_left.mpr; intro d f g; exact ht ((Finset.mem_antidiagonal.mp f).symm.trans (Finset.mem_antidiagonal.mp g))
end s
section d
variable {Y: Type}[NormedAddCommGroup Y][NormedSpace ℝ Y]
variable {f g:E→Y}{k:ℕ}{C c d a b:ℝ}{x:E}
-- at-point and aperture downgrade. use strictly only for extraction
abbrev Assets(k:ℕ)(f:E→Y)(x:E)(a c:ℝ):= ContDiffAt ℝ (↑k:WithTop ℕ∞) f x ∧ potash a k f x ≤ c
namespace Assets
lemma cheaperA (h:Assets k f x a c)(u:0≤b)(p:b≤a): Assets k f x b c:=by
 refine ⟨h.1,le_trans ?_ h.2⟩; apply sum_le_sum; intro i _; unfold noble; gcongr
lemma out (h:Assets k f x a c)(p:0<a)(q:a≤1): Allows k f x (k.factorial*c*a⁻¹^k):=⟨h.1,nob_out p q h.2⟩
lemma plus (p:0≤a)(h:Assets k f x a c)(g':Assets k g x a d):Assets k (fun x=>f x+g x) x a (c+d):=by
 refine ⟨h.1.add g'.1,le_trans ?_ (add_le_add h.2 g'.2)⟩; unfold potash; rw [←sum_add_distrib]; apply sum_le_sum; intro i v; have ht:i≤ k:= Nat.le_of_lt_add_one (mem_range.mp v); unfold noble; rw [←mul_add,show (fun x=>f x+g x)=f+g from rfl,iteratedFDeriv_add_apply (h.1.of_le (by exact_mod_cast ht)) (g'.1.of_le (by exact_mod_cast ht))]; apply mul_le_mul_of_nonneg_left (norm_add_le ..) (by positivity)
lemma smB (p:0≤a)(h:Assets k f x a c)(z:ℝ): Assets k (fun i=>z • f i) x a (‖z‖*c):=by
 refine ⟨contDiffAt_const.smul h.1,le_trans ?_ (mul_le_mul_of_nonneg_left h.2 (norm_nonneg _))⟩; unfold potash; rw [Finset.mul_sum]; apply sum_le_sum; intro i g; have hp:i≤ k:= Nat.le_of_lt_add_one (mem_range.mp g); unfold noble; rw [show (fun i=>z • f i)=z • f from rfl,iteratedFDeriv_const_smul_apply (h.1.of_le (by exact_mod_cast hp)),norm_smul]; exact le_of_eq (mul_left_comm ..)
lemma valueB(p:0≤a)(h:Assets k f x a c): ‖f x‖ ≤ c:=by
 have he:= Finset.single_le_sum (fun j _=>pos_nob (g:=f) (x:=x) p j) (Finset.mem_range.mpr (show 0<k+1 by omega)) ; exact le_trans (by simpa [potash,noble] using he) h.2 -- tune
lemma monoL (h:Assets k f x a c)(p:c≤d): Assets k f x a d :=⟨h.1,h.2.trans p⟩
lemma ballot (g':ContDiffAt ℝ (↑k:WithTop ℕ∞) f x)(v:potash a k f x ≤ c) :Assets k f x a c:=⟨g',v⟩
lemma fixed (p:Y)(h:‖p‖≤ c): Assets k (fun _=>p) x a c:=⟨contDiffAt_const,(pot_const p ..).trans_le h⟩
lemma tot (p:0≤a){I:Type*}(P:Finset I){f:I→ E→Y}{v:I→ℝ}(h:∀ i∈P,Assets k (f i) x a (v i)):Assets k (fun x=>∑ j∈P,f j x) x a (∑ i∈P,v i):=by
 classical
 induction P using Finset.induction_on with|empty=>simp_rw [sum_empty]; exact fixed _ norm_zero.le|insert i P p' ih=>simp_rw [sum_insert p']; exact (plus p (h i (mem_insert_self ..)) (ih (fun i p=>h i (mem_insert_of_mem p))))
end Assets
end d
section x
open Assets MeasureTheory
variable {I:Type}[Countable I][MeasurableSpace I][MeasurableSingletonClass I] [TopologicalSpace I][DiscreteTopology I][FiniteDimensional ℝ E]
variable {Y: Type}[NormedAddCommGroup Y][NormedSpace ℝ Y][CompleteSpace Y]{S:Set E}{x:E}{a:ℝ}{k:ℕ}{f:I→E→Y}{l:I→ℝ}
lemma sum_assets (s: IsOpen S)(u:x∈ S)(p:0<a)(v:a≤1)(h:∀ i y,y∈S→Assets k (f i) y a (l i))(H:Summable l): Assets k (fun y=>∑' i,f i y) x a (∑' i,l i):=by
 let L(i):=(k.factorial:ℝ)*l i*a⁻¹^k; let μ:Measure I:=Measure.count; have hl:Summable L:= (H.mul_left _).mul_right _; have ht(i)(x)(p':x∈S):Allows k (f i) x (L i):=out (h i x p') p v; have he:=under s (fun j y t=> (ht j y t).smooth) (fun _ _=> StronglyMeasurable.of_discrete) (integrable_count_iff.mpr hl.abs) ht
 let F:=average μ f; let A(y):=∑' i,f i y
 have hh : F =ᶠ[𝓝 x] A:=by filter_upwards [s.mem_nhds u] with i t; unfold F Planned.AtomRegular.average; rw [integral_countable (integrable_count_iff.mpr (Summable.of_norm_bounded hl fun j=> by rw [norm_norm]; exact (ht j i t).value))]; simp [μ]; rfl -- tune
 refine ⟨(he.germ s u).congr_of_eventuallyEq hh.symm,?_⟩; unfold potash
 have hL (i:ℕ)(g:i∈range (k+1)): i ≤ k:= Nat.le_of_lt_succ (mem_range.mp g)
 have hb(i:ℕ)(hi:i ∈ range (k+1)): Summable (fun j=> ‖iteratedFDeriv ℝ i (f j) x‖):=integrable_count_iff.mp (he.integrate u (hL i hi))
 have hs(j):potash a k (f j) x≥0:=sum_nonneg (fun i _=>pos_nob p.le _)
 have hm:Summable (fun j=>potash a k (f j) x):=H.of_nonneg_of_le hs (fun i=>(h i x u).2)
 apply le_trans _ (Summable.tsum_le_tsum (fun i=>(h i x u).2) hm H); unfold potash noble; rw [Summable.tsum_finsetSum (fun i l=>(hb i l).mul_left (a^i/i.factorial))] -- tune noble
 apply sum_le_sum; intro i l; have hg:= hL i l; have hz:=he.integrate u hg; change noble a i A x ≤ ∑' j, noble a i (f j) x; unfold noble; rw [←(hh.iteratedFDeriv (𝕜:=ℝ) i).eq_of_nhds, show iteratedFDeriv ℝ i F x= _ from (he.less hg).differentiate s u, integral_countable hz,tsum_mul_left]; apply mul_le_mul_of_nonneg_left _ (by positivity); simpa using (show ‖_‖ ≤ _ from norm_tsum_le_tsum_norm (hb i l)) -- tune
end x
end YM.CF.Gas
