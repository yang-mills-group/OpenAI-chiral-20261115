/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Siete.Sales
set_option autoImplicit false
noncomputable section
namespace YM.CF.Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset SU Fock Lat Spire Scroll MeasureTheory Skye Scree Cube RG PhysicalNext.JointLoad Next.Foundations
open MultiNext.SignedSource Lyre Banjo Analysis Push.Local AnalyticBridge.VerifiedReset
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
variable {n:Side}{a b r C d:ℝ}{k p j m:ℕ}{B:BudgetPoint}{X:Support (More n)}{o:Seat n}{F: Pane n→ℂ}
private structure Thesis (B:BudgetPoint)(X:Support (More n))(o:Seat n)(F:Pane n→ℂ):Prop where
 base (L:ℂ→L[ℝ]ℝ): Heir.Seed B o X (L∘F)
 un(U:Pane n): Healthy B.threshold X U→ Chart B.order F U
 theorem_I : Nonwrapping X o
 pass:4 ≤ (More n).val
private lemma extinguish (h : Thesis B X o F)(a:Fin m→ℕ)(v:Fin m→tangD n)(he:∑ i,a i ≤4)(hx:∀ i,1 ≤ a i)(hv:∀ i,a i≤2→Mom.screen X (v i)∈Mom.Maps o X (a i)): iteratedFDeriv ℝ m (F∘increment 1) 0 v=0:=by
 let G(L:ℂ→L[ℝ]ℝ):=Heir.Seed B o X (L∘F); have gX:= Thera.yet_one; have hn:=h.pass
 have hy :m ≤ B.order:=by
    have hh := Finset.sum_le_sum (s:=univ) (f:=fun _=> 1) (fun i _=>hx i); simp at hh; have hg:=B.order_ge; omega
 have hp(L:ℂ→L[ℝ]ℝ): L (iteratedFDeriv ℝ m (F ∘ increment 1) 0 v)=0:=by
    let t:=L ∘ F; let f:=h.base L
    rw [show L (iteratedFDeriv ℝ m _ 0 v)= iteratedFDeriv ℝ m (t∘ increment 1) 0 v from ?_]; swap; · change _=iteratedFDeriv ℝ m (L ∘ (F∘increment 1)) 0 v; rw [L.iteratedFDeriv_comp_left (f:= F∘ increment 1) (h.un 1 (flat_ok B X)) (Nat.cast_le.mpr hy)]; rfl -- tune
    by_cases hk: ∃ i, 2 < a i; swap; · exact Heir.Seed.ghost gX f h.theorem_I hn v hx he (fun i=> hv i (le_of_not_gt fun k=> hk ⟨i,k⟩)) -- order?
    obtain ⟨i,hi⟩:= hk
    have ht:=Finset.card_erase_add_one (Finset.mem_univ i); simp only [card_univ,Fintype.card_fin] at ht; have hs:=Finset.sum_le_sum (s:=univ.erase i) (f:=fun _=>1) (fun i _=>hx i); rw [← Finset.add_sum_erase _ _ (mem_univ i)] at he; simp only [Finset.sum_const,nsmul_eq_mul,mul_one] at hs; change (Finset.univ.erase i).card ≤ ∑ j∈Finset.univ.erase i, a j at hs; have hh:=i.pos; rcases show m=1 ∨ m=2 by omega with p|p
    · subst m; rw [iteratedFDeriv_one_apply, show fderiv ℝ (t∘ increment 1) 0=0 from flat_critical gX f.good]; rfl
    subst m; change iteratedFDeriv ℝ 2 (t∘ increment 1) 0 _ = _; rw [show v=![v 0,v 1] from funext fun i=>by fin_cases i <;> rfl]; change logHessian t _ _=0
    have hz:a 0+a 1≤4:=by rwa [add_sum_erase _ _ (mem_univ i), Fin.sum_univ_two] at he
    fin_cases i
    · change 2 < a 0 at hi; have ht:a 1=1:=by have:=hx 1; omega
      rw [hessian_symm f.good]; exact f.constant_hessian gX h.theorem_I hn (by simpa only [ht] using hv 1 (show a 1≤2 by omega))
    change 2<a 1 at hi; have ht:a 0=1:=by have:=hx 0; omega
    exact f.constant_hessian gX h.theorem_I hn (by simpa only [ht] using hv 0 (show a 0≤2 by omega))
 exact Complex.ext (hp Complex.reCLM) (hp Complex.imCLM)
structure Acceptance (B:BudgetPoint)(X:Support (More n))(o:Seat n)(F:Pane n→ℂ)(c:ℝ):Prop where
 track (U: Pane n) : pingS B.threshold X U→ Signs B o (F∘ increment U) c
 anchor : o∈X
 mute : F 1=0
 muteT (x y : tangD n) (hx : IsAffineDirection o x)(hy:IsAffineDirection o y): iteratedFDeriv ℝ 2 (F∘ increment 1) 0 ![x,y]=0
 depends:LocalOn X F
 gaugeV:GaugeInvariant F
 borel:Measurable F
private lemma Acceptance.escapes (h:Acceptance B X o F d)(hx: Nonwrapping X o)(v:4 ≤ (More n).val) : Thesis (pintK B) X o F:=by
 have he (L:ℂ→L[ℝ]ℝ): (pintK B).Regular X (L∘F):=by
    have ht(U:Pane n)(p: Healthy (pintK B).threshold X U):Chart B.order (L∘F) U:= L.contDiff.contDiffAt.comp 0 (f:=F∘increment U) (h.track U (ping_lo (half_lt_self B.threshold_pos) p)).paid
    refine ⟨fun U V e=> congrArg L (h.depends _ _ e), L.continuous.measurable.comp h.borel, fun u i=> congrArg L (h.gaugeV u i), ht, fun U p a l g=> left_has a g (ht U p)⟩
 refine ⟨fun L=> ⟨he _,h.anchor,(by simp [h.mute]),fun p x y u v=> ?_⟩,fun U t=>(h.track U (ping_lo (half_lt_self B.threshold_pos) t)).paid,hx,v⟩
 unfold logHessian; change iteratedFDeriv ℝ 2 (L ∘ (F∘ increment 1)) 0 _=_; rw [L.iteratedFDeriv_comp_left (f:= F∘ increment 1) ((h.track 1 (ping_f B X)).paid) (i:=2) ?_]; change L (iteratedFDeriv ℝ 2 (F∘ increment 1) 0 ![x,y])=_; rw [h.muteT x y u v, map_zero]; exact Nat.cast_le.mpr (show 2≤ B.order from (le_trans (by norm_num : 2 ≤ 6) B.order_ge))
private lemma taper (u:ℝ)(h:Acceptance B X o F u)(hx:Nonwrapping X o)(hn:4 ≤ (More n).val)(hg:0≤r)(hr:r≤1)(ht:1≤C)(v:Fin m→ tangD n)(l:m≤k)(p:k≤ B.order)(k':∀ i,Promise 2 C r B o X (v i)): ‖iteratedFDeriv ℝ m (F∘ increment 1) 0 v‖≤ ((3*C)^k*r^5)*u:=by
 choose w hw hW hP using k'
 let T:=iteratedFDeriv ℝ m (F∘ increment 1) 0; change ‖T v‖≤ _; have hτ:=(h.track 1 (ping_f B X)).grade
 rw [funext hw,T.map_sum (α:=fun _=> Fin 3)]
 refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=> (C^m*r^5)*u) (fun j _=>?_)).trans ?_)
 · let a (i : Fin m) := (j i).val+1
   by_cases he : ∑ i,a i ≤ 4
   · rw [show T _ = 0 from extinguish (h.escapes hx hn) a _ he (fun _ => by unfold a; omega) (fun i hi => hP i _ (show (j i).val < 2 from Nat.lt_of_succ_le hi)),norm_zero]
     positivity
   apply (seals (h.track 1 (ping_f B X)) _ (fun i=> C*r^(a i)) (l.trans p) (fun i=> hW i _)).trans; rw [prod_mul_distrib,prod_pow_eq_pow_sum]; simp only [prod_const,card_univ,Fintype.card_fin]
   exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hg hr (by omega)) (by positivity)) hτ
 rw [sum_const,card_univ,Fintype.card_fun,Fintype.card_fin,Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow]
 have hi := pow_le_pow_right₀ (show 1 ≤ 3*C by linarith) l
 calc
    _ = ((3*C)^m*r^5)*u := by push_cast; rw [mul_pow]; ring
    _ ≤ _ := by gcongr
lemma storm (k:ℕ)(hp:5≤k)(u:ℝ)(p:1≤u):∃ C:ℝ,1≤ C∧∀ (n:Side)(X:Support (More n))(P: BudgetPoint)(o:Seat n)(v:tangD n)(F:Pane n → ℂ) (a r:ℝ), Nonwrapping X o  →  k≤P.order  →  4≤(More n).val → Acceptance P X o F a → Promise 2 u r P o X v  →  0≤r → r ≤ 1  →  (∀ i,Mom.needed X i → ‖v i‖≤1∧Lyre.width P o i≤1)  → (∀ t∈ Set.Icc (0:ℝ) 1, pingS P.threshold X (increment 1 (t • v)))  → ∀ m:ℕ,m≤k → ∀ (y:Fin m →  tangD n), (∀ i, Promise 2 u r P o X (y i)) →  ‖iteratedFDeriv ℝ m (F∘ increment 1) v y‖ ≤ C*r^5*a:=by
 obtain ⟨C,f,H⟩:=multip k
 let K:= C*(3*u)^k; have hk:1≤ K:=one_le_mul_of_one_le_of_one_le f (one_le_pow₀ (by linarith)) -- tune name
 refine ⟨(k+1:ℝ)*K,one_le_mul_of_one_le_of_one_le (by simp) hk,fun n X B o x F a r hx hb hn q h hg hv ho hX m hm v hz=>?_⟩
 have hF:=(q.track 1 (ping_f B X)).grade
 let M:= K*r^5*a; let T:=F∘ increment 1
 have hs(j)(hj : j≤k)(v :Fin j→tangD n)(hy:∀ i,Promise 2 u r B o X (v i))(s:ℝ)(ht:s∈Set.Icc (0:ℝ) 1): ‖iteratedFDeriv ℝ j T (s • x) v‖ ≤ ((k+1-j:ℕ):ℝ)*M:=by
   have hl t i (p:t ∈ Set.Icc (0:ℝ) 1)(v:i≤k):ContDiffAt ℝ (↑(i:ℕ)) T (t • x):=(stirring 1 (t • x) q.depends _ (q.track _ (hX _ p))).of_le (Nat.cast_le.mpr (v.trans hb))
   induction hj using Nat.decreasingInduction generalizing s with
   | self=> rw [show k+1-k=1 by omega,Nat.cast_one,one_mul]
            refine (H n X 1 B o (s • x) F q.depends a (q.track _ (hX _ ht)) (fun i hi=>?_ ) k le_rfl hb v (fun _=>3*u*r) (fun i=>?_ )).trans ?_
            · rw [Pi.smul_apply,norm_smul, Real.norm_of_nonneg ht.1]; exact ⟨mul_le_one₀ ht.2 (norm_nonneg _) (ho i hi).1,(ho i hi).2⟩
            · convert (hy i).shot hg hv (zero_le_one.trans p) using 1; norm_num
            simp only [prod_const,card_univ,Fintype.card_fin,mul_pow]; unfold M K; rw [mul_pow,← mul_assoc C (_ *_^k) (r^k)]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hg hv hp) (by positivity)) hF
   | of_succ j hj ih =>
     have hV : ∀ i : Fin (j+1), Promise 2 u r B o X ((Fin.cons x v : Fin (j+1) → tangD n) i) := Fin.cases (by simpa using h) (fun i=>by simpa using hy i)
     have he:= Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f:=fun t:ℝ=> iteratedFDeriv ℝ j T (t • x) v) (fun t he=> (Heir.along_deriv x v t (hl t _ he hj)).hasDerivWithinAt) (fun t ht=> ih (Fin.cons x v) hV t ht) (convex_Icc ..) (show (0:ℝ)∈Set.Icc (0:ℝ) 1 by simp) ht
     rw [zero_smul,sub_zero, Real.norm_of_nonneg ht.1] at he
     have hj := he.trans (mul_le_of_le_one_right (by unfold M; positivity) ht.2)
     have hs: ‖iteratedFDeriv ℝ j T 0 v‖≤M:= (taper a q hx hn hg hv p v (show j ≤ k by omega) hb hy).trans (show (3*u)^k*r^5*a≤_ from ?_); swap; · unfold M K; gcongr; exact le_mul_of_one_le_left (by positivity) f
     refine (show ‖iteratedFDeriv ℝ j T (s • x) v‖ ≤ _ from le_trans (by simpa using (norm_add_le (iteratedFDeriv ℝ j T (s • x) v-iteratedFDeriv ℝ j T 0 v) (iteratedFDeriv ℝ j T 0 v))) (add_le_add hj hs)).trans_eq ?_ -- tune norm_le
     rw [show k+1-j=k+1-(j+1)+1 by omega,Nat.cast_add_one,add_mul,one_mul]
 have hb:= hs m hm v hz 1 (by simp); rw [one_smul] at hb
 exact hb.trans ((mul_le_mul_of_nonneg_right (by exact_mod_cast (show k+1-m≤k+1 by omega)) (by unfold M; positivity)).trans_eq (show ((k+1:ℕ):ℝ)*M=_ from by unfold M; push_cast; ring))
end YM.CF.Siete
