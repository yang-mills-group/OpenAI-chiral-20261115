import GaugeFieldConstruction.VoidCharge
/-!
# Radius test of double contractions, all external jets
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Flux.One
open Gap Complex Cauchy Row Wick Phys Function Set Filter YM.Analysis MeasureTheory
open YM.Maxwell (grad)
open scoped Topology ContDiff BigOperators
open Matter (Slot)

def half (n : ℕ) := (1/2:ℝ)^n
def big (f : SmoothGap) (n : ℕ) := ∀ x:E4, eye ((2:ℝ) • x) f=half n • eye x f
lemma big_add {f g n} (h : big f n) (p : big g n):big (f+g) n := fun x=> by rw [map_add,h,p,map_add,smul_add]
lemma big_s {f n} (p : big f n) (r : ℂ) : big (r • f) n := fun x=>by rw [map_smul,map_smul,p]; exact smul_comm ..
lemma big_z (n) : big 0 n := by intro x; simp
lemma big_sum {α : Type*} {s : Finset α} {p : α→SmoothGap} {n} (h : ∀ i ∈ s,big (p i) n) : big (∑ i∈s,p i) n := by intro x; rw [map_sum,map_sum,Finset.smul_sum]; exact Finset.sum_congr rfl fun i hi=> h i hi x
lemma big_g {f : SmoothGap} {n} (h : big f n) (i) : big (Gap.step i f) (n+1) := by
  intro x
  change (Gap.step i f).val _=half _ • (Gap.step i f).val x
  by_cases e:x=0
  · simp [e]
  have p : (2:ℝ) • x≠0 := smul_ne_zero (by norm_num) e
  rw [flash _ _ p,flash _ _ e]
  let L:= (2:ℝ) • ContinuousLinearMap.id ℝ E4
  have he : grad i (f.val ∘ L) x=half n • grad i f.val x := by
    have ht : f.val ∘ L=half n • f.val := funext h
    rw [ht]; unfold YM.Maxwell.grad D; rw [fderiv_const_smul ((Gap.healthy f e).differentiableAt (by simp))]; rfl
  unfold YM.Maxwell.grad D at he ⊢
  rw [fderiv_comp x (f:=L) (show DifferentiableAt ℝ f.val (L x) from (Gap.healthy f p).differentiableAt (by simp)) L.differentiableAt,L.fderiv, ContinuousLinearMap.comp_apply] at he
  change fderiv ℝ f.val ((2:ℝ) • x) ((2:ℝ) • basis i) = _ at he; rw [map_smul] at he
  rw [show half (n+1)= (1/2:ℝ) * half n from pow_succ' ..,mul_smul,← he, ← mul_smul]; norm_num
lemma big_neg {f n} (p : big f n) : big (-f) n:=fun x=>by rw [map_neg,map_neg,p]; exact (smul_neg ..).symm
lemma big_sub {f g n} (h : big f n) (p : big g n) : big (f-g) n:=by rw [sub_eq_add_neg]; exact big_add h (big_neg p)
lemma big_t {f g p q} (h : big f p) (k : big g q): big (Gap.times f g) (p+q) := fun x=>by rw [tick,tick,h x,k x]; simp only [half,pow_add, real_smul]; push_cast; ring
lemma big_sg : big stone 2 := by
  intro x; change stone.val _=half 2 • stone.val x; by_cases h:x=0; simp [h]
  have p : (2:ℝ) • x ≠ 0:= smul_ne_zero (by norm_num) h
  unfold stone; rw [lap _ _ p,lap _ _ h]; norm_num [YM.Maxwell.Green,norm_smul,half,real_smul]; ring
lemma big_tg (i j k l) : big (curl i j k l) 4 := by
  let f i j:=Gap.step i (Gap.step j stone)
  have he p q:big (f p q) 4:= big_g (big_g big_sg q) p
  rw [Raster.curlwork i j k l f fun i j=> by simp [Raster.word,f]]; split_ifs <;> apply big_sub <;> apply big_sub <;> first|apply he|apply big_z
lemma big_sp (d a b) : big (thread d a b) 3 := by rw [present]; exact big_sum fun i _=> big_s (big_g big_sg i) _
lemma big_mi {f n} (p : big f n) (i k): big (mi i k f) (n + Invoice.deg k) := by
  have h (f : SmoothGap) n (p : big f n) (j : Axis) (m : ℕ): big ((foot i j^m) f) (n+m) := by
    induction m with
    | zero=> rw [pow_zero,Module.End.one_apply,add_zero]; exact p
    | succ m he=> rw [power_age,← add_assoc]
                  have h:=big_g he j; cases i
                  · exact big_neg h
                  exact h
  simp only [mi,Module.End.mul_apply]
  convert h _ _ (h _ _ (h f n p _ _) _ _) _ _ using 1; unfold Invoice.deg; omega

def weightG (x : GIndex) := Invoice.deg x.2.val.2
def weight (x : FIndex):= Invoice.deg x.2
lemma big_covF (b i k) (s t : Slot) (r):big (yarn b (sessionF s i) (ket (k,t))) (3+weight k + (r-r)):=by -- r awkward
  rw [sessionF,← heights t k,yarn, matchU]; split_ifs
  · change big (directed b _ (C k.1 k.2)) _; rw [psD,ends,Module.End.one_apply,Nat.sub_self,add_zero]; exact big_mi (big_sp _ _ _) true _
  exact big_z _
lemma big_covG (a b) (u v : Pig) (k : GIndex): big (ge (sectionG u a b) (ket (k,v))) (4+weightG k) := by
  rw [ge, sectionG,← heights v k,matchU]; split_ifs
  · have h (j:GIndex) : F (Solution.truck j.1 j.2.val.1).1 (Solution.truck j.1 j.2.val.1).2 j.2.val.2 = ket j := by
      let p:=j.2.val.1
      have k (i : S3) z : F (cw i).castSucc (ccw i).castSucc z=G true i z := by fin_cases i <;> rfl
      rw [← picked_G j]; cases j.1
      · change F (Fin.last 3) (Fin.castSucc _) _ = _; simp only [F,Fin.lastCases_last,Fin.lastCases_castSucc]
      apply k
    nth_rw 1 [← h k]; rw [unroll,ends,Module.End.one_apply]; exact big_mi (big_tg _ _ _ _) true _
  exact big_z _
lemma big_fv (X : Mode) (b i s) : big (yarn b (sessionF s i) (ket X)) (3+weight X.1):= big_covF _ _ _ _ _ 0
lemma big_fv' (X : Mode) (b i u j): big (yarn b (stride b j (sessionF u i)) (ket X)) (4+weight X.1):= by rw [baseF, show 4+weight X.1=3+weight X.1+1 by omega]; exact big_neg (big_g (big_fv _ _ _ _) _)
lemma big_f (u i j p) (X : Spair): big (fGap (fStress u i j) (ket X)) (7+weight X.1.1+weight X.2.1+(p-p)):=by
  rw [fStress,map_sum,LinearMap.sum_apply,Nat.sub_self,add_zero]
  apply big_sum; intro i' _
  simp_rw [map_smul, LinearMap.smul_apply,map_add,LinearMap.add_apply]
  have he (i j): big (fGap (sD i' i' (L j (B i))) (ket X)) (7+weight X.1.1+weight X.2.1):=by
    rw [degreeP]; simp_rw [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply, map_sub,LinearMap.sub_apply]; apply big_sum; intro k _; apply big_sum; intro l _; apply big_s; apply big_sub
    · rw [← takes X.1 X.2, f_pay] -- takes not available now
      rw [show 7+weight _+weight _ = (3+weight X.2.1)+(4+weight X.1.1) by omega]; exact big_t (big_fv _ _ _ _) (big_fv' _ _ _ _ _)
    rw [← takes X.1 X.2,f_pay,show 7+weight _+weight _=(4+weight X.2.1)+(3+weight X.1.1) by omega]; exact big_t (big_fv' _ _ _ _ _) (big_fv _ _ _ _)
  apply big_s; apply big_s; exact big_add (he _ _) (he _ _)

lemma bareg {X : GaugePair} (p : Pig) (i j k) : gaugeGap (times' (sectionG p i k) (sectionG p j k)) (ket X) =
    Gap.times (ge (sectionG p i k) (ket X.1)) (ge (sectionG p j k) (ket X.2))+ Gap.times (ge (sectionG p i k) (ket X.2)) (ge (sectionG p j k) (ket X.1)) := by
  change _ = _; rw [← takes X.1 X.2]; apply Gap.eyes; intro z _; rw [gauge_contract,map_add,tick,tick]
lemma big_v (i j x) (c:Pen) : big (ge (sectionG x i j) (ket c)) (4+weightG c.1) := big_covG i j x c.2 c.1
lemma big_gG (X : GaugePair) i j a : big (gaugeGap (gStress a i j) (ket X)) (8+weightG X.1.1+weightG X.2.1):=by
  have he p i j k : big (gaugeGap (times' (sectionG p i k) (sectionG p j k)) (ket X)) (8+weightG X.1.1+weightG X.2.1) := by
    rw [bareg p i j k]; apply big_add
    · rw [show 8+weightG _+weightG _=(4+weightG X.1.1)+(4+weightG X.2.1) by omega]; exact big_t (big_v _ _ _ _) (big_v _ _ _ _)
    rw [show 8+weightG _+weightG _=(4+weightG X.2.1)+(4+weightG X.1.1) by omega]; exact big_t (big_v _ _ _ _) (big_v _ _ _ _)
  have hr i j: big (gaugeGap (graph_g (U1.Gauge97.bill i j)) (ket X)) (8+weightG X.1.1+weightG X.2.1) := by
    rw [gPalette,map_smul,LinearMap.smul_apply]; apply big_s
    simp_rw [map_sum,map_add,LinearMap.sum_apply,LinearMap.add_apply]; exact big_sum (fun i _=>big_sum (fun j _=>big_add (he _ _ _ _) (he _ _ _ _)))
  unfold gStress U1.Gauge97.recorded; simp_rw [map_smul,map_sub, LinearMap.smul_apply,LinearMap.sub_apply]; split_ifs
  · apply big_s; apply big_s; apply big_sub; simp_rw [map_smul,LinearMap.smul_apply]; exact big_s (hr _ _) _
    simp_rw [map_sum,LinearMap.sum_apply]; apply big_sum; intro j _; exact hr _ _
  simp only [map_smul,LinearMap.smul_apply,map_zero, LinearMap.zero_apply,sub_zero]; exact big_s (big_s (big_s (hr _ _) _) _) _
end YM.GaugeFieldConstruction.Flux.One
