/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Prism.Veste
set_option autoImplicit false
noncomputable section
namespace YM.CF.Prism
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset SU Fock Lat Spire Scroll MeasureTheory Skye Scree Cube RG PhysicalNext.JointLoad Next.Foundations
open MultiNext.SignedSource Lyre Banjo Analysis Push.Local AnalyticBridge.VerifiedReset
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
variable {n:Side}{a b r C d:ℝ}{k p j m:ℕ}{B:BudgetPoint}{X:Support (More n)}{o:Seat n}{F: Pane n→ℂ}

structure Roman (r C:ℝ)(B:BudgetPoint)(X:Support (More n))(o:Seat n)(F:Pane n→ℂ)(c:ℝ):Prop where
 track (U: Pane n) : pingS B.threshold X U→ Signs B o (F∘ increment U) c
 mute : F 1=0
 tune(u:tangD n)(v:Mom.screen X u ∈ Mom.Maps o X 1)(s:Sized (C*r) u B o) : ‖fderiv ℝ (F ∘ increment 1) 0 u‖ ≤ C*r^2*c
 depends:LocalOn X F
private lemma taper (u:ℝ)(h:Roman r C B X o F u)(hx:Nonwrapping X o)(hn:4 ≤ (More n).val)(hg:0≤r)(hr:r≤1)(ht:1≤C)(v:Fin m→ tangD n)(l:m≤k)(p:k≤ B.order)(kp:∀ i,Promise 2 C r B o X (v i)): ‖iteratedFDeriv ℝ m (F∘ increment 1) 0 v‖≤ ((3*C)^k*r^2)*u:=by
 have H:= h.track 1 (ping_f B X); have ht':= H.grade
 by_cases hm:m=0
 · subst m; rw [iteratedFDeriv_zero_apply]; simp only [Function.comp_apply,Work.G07.at_zero_increment,h.mute,norm_zero]; positivity
 by_cases he:m=1; swap
 · apply (seals H v (fun _=> 3*C*r) (l.trans p) (fun i=> by convert (kp i).shot hg hr (zero_le_one.trans ht) using 1; norm_num)).trans
   rw [prod_const,card_univ,Fintype.card_fin,mul_pow]; apply mul_le_mul_of_nonneg_right _ ht'; exact mul_le_mul (pow_le_pow_right₀ (by nlinarith) l) (pow_le_pow_of_le_one hg hr (by omega)) (by positivity) (by positivity)
 subst m; obtain ⟨w,hw,hW,hh⟩:= kp 0; rw [iteratedFDeriv_one_apply,hw,map_sum]; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun i=>C*r^2*u) (fun i _=>?_)).trans ?_)
 · by_cases g:i.val=0
   · have hp :i=(0:Fin 3):= Fin.ext g; subst i; exact h.tune _ (hh 0 (by decide)) (by simpa using hW 0)
   apply le_trans (b:= (C*r^(i.val+1))*u) _ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hg hr (by omega)) (by positivity)) ht'); simpa [iteratedFDeriv_one_apply] using seals H (fun _:Fin 1=> w i) (fun _=>C*r^(i.val+1)) (l.trans p) (fun _=>hW i)
 rw [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; norm_cast -- tune
 push_cast; rw [←mul_assoc,←mul_assoc]; gcongr; simpa using (pow_le_pow_right₀ (show 1 ≤ 3*C by nlinarith) l)
lemma hoped (k:ℕ)(hp:2≤k)(u:ℝ)(p:1≤u):∃ C:ℝ,1≤ C∧∀ (n:Side)(X:Support (More n))(P: BudgetPoint)(o:Seat n)(v:tangD n)(F:Pane n → ℂ) (a r:ℝ), Nonwrapping X o  →  k≤P.order  →  4≤(More n).val → Roman r u P X o F a → Promise 2 u r P o X v  →  0≤r → r ≤ 1  →  (∀ i,Mom.needed X i → ‖v i‖≤1∧Lyre.width P o i≤1)  → (∀ t∈ Set.Icc (0:ℝ) 1, pingS P.threshold X (increment 1 (t • v)))  → ∀ m:ℕ,m≤k → ∀ (y:Fin m →  tangD n), (∀ i, Promise 2 u r P o X (y i)) →  ‖iteratedFDeriv ℝ m (F∘ increment 1) v y‖ ≤ C*r^2*a:=by
 obtain ⟨C,f,H⟩:=multip k
 let K:= C*(3*u)^k; have hk:1≤ K:=one_le_mul_of_one_le_of_one_le f (one_le_pow₀ (by linarith)) -- tune name
 refine ⟨(k+1:ℝ)*K,one_le_mul_of_one_le_of_one_le (by simp) hk,fun n X B o x F a r hx hb hn q h hg hv ho hX m hm v hz=>?_⟩
 have hF:=(q.track 1 (ping_f B X)).grade
 let M:= K*r^2*a; let T:=F∘ increment 1
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
     have hs: ‖iteratedFDeriv ℝ j T 0 v‖≤M:= (taper a q hx hn hg hv p v (show j ≤ k by omega) hb hy).trans (show (3*u)^k*r^2*a≤_ from ?_); swap; · unfold M K; gcongr; exact le_mul_of_one_le_left (by positivity) f
     refine (show ‖iteratedFDeriv ℝ j T (s • x) v‖ ≤ _ from le_trans (by simpa using (norm_add_le (iteratedFDeriv ℝ j T (s • x) v-iteratedFDeriv ℝ j T 0 v) (iteratedFDeriv ℝ j T 0 v))) (add_le_add hj hs)).trans_eq ?_ -- tune norm_le
     rw [show k+1-j=k+1-(j+1)+1 by omega,Nat.cast_add_one,add_mul,one_mul]
 have hb:= hs m hm v hz 1 (by simp); rw [one_smul] at hb
 exact hb.trans ((mul_le_mul_of_nonneg_right (by exact_mod_cast (show k+1-m≤k+1 by omega)) (by unfold M; positivity)).trans_eq (show ((k+1:ℕ):ℝ)*M=_ from by unfold M; push_cast; ring))
end YM.CF.Prism
