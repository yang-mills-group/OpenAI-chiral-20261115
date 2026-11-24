import YM.CF.Jet.Mask

/-! Weighted finite-order submultiplicative norm. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Jet
open Function Filter Metric Finset
open scoped Topology BigOperators ContDiff
variable {E Y Z:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup Y][NormedSpace ℝ Y]
variable {f:E→ℝ}{g:E→Y}{k:ℕ}{C a:ℝ}{x:E}
def noble (a:ℝ)(i:ℕ)(g:E→Y)(x:E):=a^i / i.factorial * ‖iteratedFDeriv ℝ i g x‖
def potash (a:ℝ)(k:ℕ)(g:E→Y)(x:E):= ∑ i∈ range (k+1),noble a i g x
lemma pos_nob (h:0≤a)(i:ℕ):0≤ noble a i g x:=by unfold noble; positivity
lemma nob_s (h:0≤a)(l:ContDiffAt ℝ (↑k:WithTop ℕ∞) f x)(s:ContDiffAt ℝ (↑k:WithTop ℕ∞) g x):noble a k (fun x=> f x • g x) x≤∑ i∈range (k+1), noble a i f x*noble a (k-i) g x:=by
 obtain ⟨U,hU,i,t⟩:= open_patch l; obtain ⟨V,hV,j,p⟩:=open_patch s
 have hw:=i.inter j; have hx:x∈U∩V:= ⟨hU,hV⟩; have ht:=norm_iteratedFDerivWithin_smul_le (t.mono Set.inter_subset_left) (p.mono Set.inter_subset_right) hw.uniqueDiffOn hx (n:=k) le_rfl
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
lemma pot_s (h:0≤a)(l:ContDiffAt ℝ (↑k:WithTop ℕ∞) f x)(s:ContDiffAt ℝ (↑k:WithTop ℕ∞) g x):potash a k (fun x=> f x • g x) x≤ potash a k f x *potash a k g x:=by
 let A (i:ℕ):= noble a i f x; let B (i:ℕ):=noble a i g x
 let R:= Finset.range (k+1)
 unfold potash; change (∑ i∈ R,_ ) ≤ (∑ i∈R,A i)* ∑ i∈R,B i; rw [Finset.sum_mul_sum]
 calc
   _ ≤ ∑ i∈ R, ∑ j∈ Finset.range (i+1), A j * B (i-j) := by
      apply sum_le_sum; intro i hi
      have he:i≤k:= Nat.le_of_lt_succ (mem_range.mp hi)
      exact nob_s h (l.of_le (by exact_mod_cast he)) (s.of_le (by exact_mod_cast he))
   _ ≤ _ := by
      let p (i:ℕ):= Finset.antidiagonal i
      let v (d:ℕ×ℕ) := A d.1*B d.2
      simp_rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j=> A i*B j)]; change (∑ i∈R,∑ d∈ p i, v d)≤_
      rw [← Finset.sum_biUnion, ←Finset.sum_product'] -- tune
      · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i t n=> mul_nonneg (pos_nob h _) (pos_nob h _)); rintro ⟨i,j⟩ hp
        obtain ⟨l,g,v⟩:=mem_biUnion.mp hp; rw [mem_product]; change l∈range _ at g; change (_,_)∈ Finset.antidiagonal _ at v; simp only [Finset.mem_antidiagonal] at v; simp only [R,mem_range,Prod.fst,Prod.snd] at *; omega
      intro i _ j _ ht; apply disjoint_left.mpr; intro d f g; exact ht ((Finset.mem_antidiagonal.mp f).symm.trans (Finset.mem_antidiagonal.mp g))
lemma nob_earn (h:Allows k g x C)(t:0≤a)(e:a≤1): potash a k g x ≤ ‖g x‖ + k*C*a :=by
 induction k with
 | zero => simp [potash,noble]
 | succ k ih=>
    unfold potash; rw [sum_range_succ]; change potash _ _ _ _+_≤_; apply (add_le_add (ih (h.order k.le_succ)) (d:=C*a) ?_).trans (le_of_eq ?_)
    · unfold noble; have he:a^(k+1)≤ a:= (pow_le_pow_of_le_one t e (Nat.le_add_left 1 k)).trans_eq (pow_one _)
      rw [mul_comm C]
      refine mul_le_mul ?_ (h.norm_le _ le_rfl) (norm_nonneg _) t
      apply (div_le_self (by positivity) (by exact_mod_cast (Nat.factorial_pos (k+1)))).trans he
    push_cast; ring
lemma nob_out (l:0<a)(s:a≤1)(h:potash a k g x ≤ C)(i)(p:i≤k): ‖iteratedFDeriv ℝ i g x‖≤ k.factorial*C*a⁻¹^k:=by
 have ht:= Finset.single_le_sum (fun j _=>pos_nob (g:=g) (x:=x) l.le j) (Finset.mem_range.mpr (show i<k+1 by omega)); unfold noble at ht
 have hg:= ht.trans h; have hx :0≤ C:= le_trans (pos_nob l.le _) (le_trans ht h)
 calc
    _ ≤ i.factorial*C*a⁻¹^i:=by
       rw [inv_pow,← div_eq_mul_inv,le_div_iff₀ (by positivity)]; field_simp at hg; linarith
    _ ≤ _:= by gcongr; exact one_le_inv₀ l|>.mpr s
lemma pot_const (f:Y) (k a) (x:E): potash a k (fun _=>f) x= ‖f‖ := by
 unfold potash; rw [Finset.sum_eq_single 0,noble,norm_iteratedFDeriv_zero]; · simp
 · intro i _ hi; simp [noble,iteratedFDeriv_const_of_ne hi]
 simp
end YM.CF.Jet
