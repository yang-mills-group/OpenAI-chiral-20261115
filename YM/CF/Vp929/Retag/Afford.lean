import YM.CF.Vp929.Retag.Energy
import YM.CF.Reef.Ice
import YM.CF.Rill.Catch
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.flexible false
noncomputable section
namespace YM.CF.SplitFlag
open Lattice Wilson RG Function MeasureTheory Filter Finset
open PathData Reef Cube Skye WilsonStartup
open scoped Topology Matrix.Norms.Frobenius Classical
local notation "G₁"=> SU.group
variable {n:Side} (c : Clip) (b p : BudgetPoint) (β : ℝ) (D : Support (More n)) (U : Pane n)
lemma mask_reads (i:Key (More n)) : UsesFinal b.threshold i.skin (maskK b i) := by
  intro U V h k
  have hK : Healthy b.threshold i.skin U ↔ Healthy b.threshold i.skin V := by rw [Healthy,Healthy,Finset.disjoint_iff_inter_eq_empty,Finset.disjoint_iff_inter_eq_empty,k]
  by_cases v : Healthy b.threshold i.skin U
  · unfold maskK; rw [masked_eq _ _ _ _ v,masked_eq _ _ _ _ (hK.mp v)]; exact (Start.accrual_regular (b:=b) i).sites U V h
  unfold maskK; rw [masked_ne _ _ _ _ v,masked_ne _ _ _ _ (mt hK.mpr v)]
lemma book_reads (H : Decent c b) (he : 12 ≤ b.B) : LocalOn (tiles b D) (book c b p D) := by
  intro U V h
  let T:=halo (2*b.B) D; have ht : halo 12 T ⊆ tiles b D:=by
    rw [tiles_spec]; intro x hx; obtain ⟨y,hy,h⟩:=halo_spec.mp hx; obtain ⟨z,hz,k⟩:=halo_spec.mp hy; refine halo_spec.mpr ⟨z,hz,(separation_triangle z y x).trans ?_⟩; omega
  have hv : Agrees (↑T) U V := agrees_mono h (Finset.coe_subset.mpr ((halo_subset 12 T).trans ht))
  have hm t:= Rill.news U V t ht h
  unfold book; refine congrArg _ (sum_congr rfl fun i _=>?_)
  split
  next h =>
    have hp : halo b.B {i.native} ⊆ T:=by
      intro x hx; obtain ⟨y,hy,h'⟩:= halo_spec.mp h; simp [halo_spec] at hx; exact halo_spec.mpr ⟨y,hy,(separation_triangle _ i.native _).trans (by omega)⟩
    have hs : i.skin ⊆ T:=fun x hx=> hp (halo_spec.mpr ⟨_,mem_singleton_self _,(i.nearby hx).trans H.radius⟩)
    unfold debt; rw [Work.H03.reads_larger hp (Key.owed_reads c b i H) U V hv (hm _), Work.H03.reads_larger hs (mask_reads b i) U V hv (hm _),Work.H03.reads_larger hs (mask_reads p i) U V hv (hm _)]
  next h=> rfl
lemma energy_reads (H : Decent c b) (he : 12 ≤ b.B) : LocalOn (tiles b D) (tagEnergy c b p D) := by
  intro U V h; unfold tagEnergy; rw [book_reads c b p D H he U V h,book_reads c b p D H he (echo U) (echo V) (fun i hi hj=>congrArg qG (h i hi hj))]
lemma mask_turn (s: Signed) (x: Seat n) (i: Key (More n)) : maskK b (Key.perm s x i) U=maskK b i (pull s x U):= by
  have e : Healthy b.threshold (Key.perm s x i).skin U ↔ Healthy b.threshold i.skin (pull s x U):=by rw [Key.spins_healthy,Key.spins_healthy, Key.oriented]; rfl
  unfold maskK
  by_cases h : Healthy b.threshold i.skin (pull s x U)
  · rw [masked_eq _ _ _ _ (e.mpr h),masked_eq _ _ _ _ h,Key.accrual,Key.oriented]; rfl
  rw [masked_ne _ _ _ _ (mt e.mp h), masked_ne _ _ _ _ h]
lemma energy_echo : tagEnergy c b p D (echo U)=tagEnergy c b p D U:=by unfold tagEnergy; rw [echo2,add_comm];
lemma energy_turn (s:Signed)(x:Seat n): tagEnergy c b p D (pull s x U)= tagEnergy c b p (D.image (affine s x)) U:=by
  have ht (U: Pane n) : book c b p (D.image (affine s x)) U=book c b p D (pull s x U):= by
    unfold book; rw [←Equiv.sum_comp (Key.perm s x)]; congr 1
    refine sum_congr rfl fun i _=>?_; simp only [show (Key.perm s x i).native=affine s x i.native from rfl,halo_image_mem]; simp_rw [debt,mask_turn,Key.owed,Key.oriented]; rfl
  unfold tagEnergy; rw [← echo_p,ht,ht]
lemma energy_gauge (k):tagEnergy c b p D (gauge k U)= tagEnergy c b p D U:=by
  have hp(V:Pane n)(k)(p:BudgetPoint)(i:Key (More n)):maskK p i (gauge k V)=maskK p i V:=by
    have e:Healthy p.threshold i.skin (gauge k V) ↔ Healthy p.threshold i.skin V:=by rw [Healthy,Healthy,gauge_flags]
    unfold maskK; by_cases h:Healthy p.threshold i.skin V
    · rw [masked_eq _ _ _ _ (e.mpr h),masked_eq _ _ _ _ h]; exact (Start.accrual_regular (b:=p) i).symmetry k V
    rw [masked_ne _ _ _ _ (mt e.mp h), masked_ne _ _ _ _ h]
  have ht(V:Pane n)(k):book c b p D (gauge k V)= book c b p D V:=by simp only [book,debt,Key.owed_gauge,hp]
  unfold tagEnergy; rw [ht, show echo (gauge k U)= gauge (echo k) (echo U) from by funext i; simp [echo,Lattice.gauge],ht]
lemma energy_measurable : Measurable (tagEnergy c b p D) := by
  have hp(p:BudgetPoint)(i:Key (More n)): Measurable (maskK p i):= masked_measurable _ _ _ (Start.accrual_regular (b:=p) i).borel
  have ht: Measurable (book c b p D):= by
    unfold book; refine Measurable.mul measurable_const (measurable_fun_sum _ fun i _ =>?_); split
    · exact ((due_measurable ..).comp (continuous_pull .. |>.measurable)).sub (Measurable.mul measurable_const ((hp p i).sub (hp b i)))
    exact measurable_const
  exact (ht.add (ht.comp (continuous_pi (fun i=>icyC.comp (continuous_apply i))|>.measurable))).div_const _
abbrev liabilities: ℝ:= share*((b.B+b.B+1:ℕ)^4 *(Fintype.card Signed:ℕ)* Fintype.card PlaqAxes:ℕ) * (Design.bulk c * Start.item G₁ p)
lemma book_price (H : Decent c b) (h : b.threshold ≤ p.threshold) (hp : p.threshold ≤ Start.threshold G₁ p.order p.power) (hd : D ⊆ flags b.threshold U) :
    (D.card:ℝ)*(gain b - liabilities c b p) ≤ book c b p D U:= by
  have hx:=charge_price c b H U D hd; let K(i: Key (More n)):= if i.native∈ halo b.B D then Design.bulk c * (maskK p i U-maskK b i U) else 0
  have hz:book c b p D U=charge c b D U-share * ∑ i,K i:=by
    unfold book charge; rw [←mul_sub,←sum_sub_distrib]; congr 1; refine sum_congr rfl fun i _=>?_ ; unfold K; split_ifs; rfl; ring
  rw [hz]; apply le_trans _ (sub_le_sub_right hx _)
  rw [mul_sub]; apply sub_le_sub_left
  let T:= Design.bulk c*Start.item G₁ p
  have hb : 0 ≤ Design.bulk c:= sub_nonneg.mpr H.direct; have hT:T≥0:=mul_nonneg hb (Start.item_pos ..).le
  have hk (i:Key (More n)) : K i ≤ if i.native ∈ halo b.B D then T else 0:= by
    unfold K; split_ifs with k
    · apply mul_le_mul_of_nonneg_left _ hb; unfold maskK; by_cases hr : Healthy p.threshold i.skin U
      · rw [masked_eq _ _ _ _ hr]; by_cases hR : Healthy b.threshold i.skin U
        · rw [masked_eq _ _ _ _ hR,sub_self]; exact (Start.item_pos ..).le
        rw [masked_ne _ _ _ _ hR, sub_zero]; exact (le_abs_self _).trans ((Start.accrual_fit i hp).2 U hr [] (by simp) (by simp))
      rw [masked_ne _ _ _ _ hr, masked_ne _ _ _ _ (mt (mask_le b p U h _) hr),sub_self]; exact (Start.item_pos ..).le
    exact le_rfl
  refine (mul_le_mul_of_nonneg_left (sum_le_sum fun i _=> hk i) share_pos.le).trans ?_
  have hv : (∑ i:Key (More n), if i.native∈halo b.B D then T else 0) =(Fintype.card Signed:ℝ)*((halo b.B D).card* ((Fintype.card PlaqAxes:ℝ)*T)):=by
    rw [Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type (fun _ : WilsonStartup.Cell (More n)=>_)]; change (∑ _ : Signed, ∑ x : Seat n, ∑ _ : PlaqAxes, if x∈halo b.B D then T else 0) = _; simp_rw [sum_const,card_univ,nsmul_eq_mul]; rw [mul_right_inj' (by positivity : (Fintype.card Signed : ℝ) ≠ 0)]; simp_rw [mul_ite,mul_zero]; rw [← sum_filter]; simp
  rw [hv];
  have hp : ((halo b.B D).card:ℝ) ≤ D.card*((b.B+b.B+1:ℕ)^4:ℕ):=by exact_mod_cast Corona.halo_size D b.B
  unfold liabilities; push_cast;
  push_cast at hp; apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp (by positivity : (0:ℝ) ≤ Fintype.card PlaqAxes * T)) (by positivity)) share_pos.le) (le_of_eq ?_); unfold T; ring
lemma energy_price (H : Decent c b) (h : b.threshold ≤ p.threshold) (hp : p.threshold ≤ Start.threshold G₁ p.order p.power) (hd : D ⊆ flags b.threshold U) :
    (D.card:ℝ)*(gain b - liabilities c b p) ≤ tagEnergy c b p D U:= by
  unfold tagEnergy; linarith only [book_price c b p D U H h hp hd,book_price c b p D (echo U) H h hp (by rwa [Beau.flags_l])]
end YM.CF.SplitFlag
