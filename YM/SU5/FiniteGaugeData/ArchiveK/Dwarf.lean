import YM.SU5.FiniteGaugeData.ArchiveK.Laptop
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.ArchiveK
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush Largo WithLp
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
namespace Midway
open Violas LightK
variable (G:E4≃ₗᵢ[ℝ] E4)(L:FilterK){A:Op SpinIdx}{n:ℕ}{r:ℝ}(x y:E4)
local notation "Ω"=> Op SpinIdx
local notation "Φ"=> Violas.page
-- approximation φ impulse per sites for true spectrum orientation. MPEG
abbrev BasisK(n:ℕ):= (coon n)
abbrev BddT(n:ℕ):= ↑(BasisK n)
lemma BasisK_dim : page (BddT n)=2*(2*n+1)^3 := by unfold page BddT BasisK; rw [Fintype.card_coe,coon_cnt]
def BloomX : Ω→ₗ[ℂ]ℂ where
 toFun f:= ∑ i:Glue,weigh G i*f (hat_a i) (hed_a i)
 map_add' x y:= by simp only [Matrix.add_apply,mul_add,sum_add_distrib]
 map_smul' c x:= by simp only [Matrix.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
def glintK := ‖(BloomX G).toContinuousLinearMap‖*rover
abbrev shellM(v:EdgeM)(x:E4):ℂ:= BloomX G (spectx v x)
abbrev River (r:ℝ)(x y: E4):= 100 < ‖x‖ ∧ 32*‖y‖ ≤ r*‖x‖
lemma shea (h:River r x y)(u:0<r)(t:r≤1): ‖shear G (x+y)-∑ i∈coon n,shellM G i x *arcX n y i‖ ≤ glintK G *r^n:= by
 let A:= BloomX G; have ht:= (A.toContinuousLinearMap).le_opNorm (spiral (x+y)-∑ i∈coon n, (arcX n y i) • spectx i x); let q:=roverPt y n x u t h.1 h.2; rw [show shear G (x+y)-_ = A (spiral (x+y)-∑ i∈coon n,(arcX n y i) • spectx i x) from ?_]; refine (le_trans ht ((mul_le_mul_of_nonneg_left q (norm_nonneg _)).trans_eq (by unfold glintK; dsimp only [A]; ring))); rw [map_sub,_root_.map_sum]; simp_rw [map_smul, smul_eq_mul]; simp_rw [mul_comm (arcX n y _)]; rfl -- placeholder.and dsimp tune
local notation "Γ"=>emitX
abbrev rebate(v:Cover)(i:Cover): E4:= emitX (v-i)
abbrev stone(v v': Cover): ℂ:=∑ i∈L.s,L.f i * shear G (Γ v + -rebate v' i)
def bumble(G:E4≃ₗᵢ[ℝ] E4)(L:FilterK):=glintK G *∑ i∈L.s,‖L.f i‖
lemma bumble_n : 0≤bumble G L:= by unfold bumble glintK; have hv:= rover_n; positivity
-- rank approximation post filtering
variable {X:Type*}[Fintype X][DecidableEq X](F H:X→ Cover){P:Op X}(h:∀ i j, P i j=stone G L (F i) (H j))(n:ℕ)(u:0<r)(t:r≤1)
local notation "Δ"=> BddT n
include h u t
private lemma fort (g:X→EdgeM→ℂ)(l:X→Cover→EdgeM→ℂ)(p:∀ (i j:X) (k:Cover), k∈L.s→‖shear G (emitX (F i) + -rebate (H j) k)- ∑ x∈coon n,g i x*l j k x‖≤glintK G *r^n): Cast (BddT n) P (bumble G L *r^n) := by
 let A: Ruler X Δ:= Matrix.of fun i j=> g i j.val; let B:Ruler Δ X:= Matrix.of fun i j=>∑ k∈ L.s, L.f k*l j k i.val; refine ⟨A,B,fun i j=>?_⟩
 let E(k):=shear G (emitX (F i) + -rebate (H j) k); let T(x:EdgeM):= g i x; let f(k:Cover):=∑ x∈coon n,T x*l j k x
 rw [h,Matrix.mul_apply]; simp_rw [A,B,Matrix.of_apply]; rw [show ∑ x:Δ,g i (x.val)*_ =∑ i∈L.s,L.f i *f i from ?_];
 · change ‖_-(∑ k∈L.s, L.f k*f k)‖ ≤ _; unfold stone; rw [← Finset.sum_sub_distrib]; simp_rw [← mul_sub]; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun i=> ‖L.f i‖*(glintK G*r^n)) fun k e=> (norm_mul ..).le.trans (mul_le_mul_of_nonneg_left (p i j k e) (norm_nonneg _))).trans_eq ?_); unfold bumble; rw [←sum_mul]; ring
 unfold f T; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm (s:=@univ Δ _)]; apply sum_congr rfl; intro x _; rw [← Finset.sum_coe_sort (coon n)]; apply sum_congr rfl; intro v _; ring -- tune sort
lemma plaque_left (g:∀ i j:X,∀ k∈ L.s,River r (Γ (F i)) (rebate (H j) k)): Cast (BddT n) P (bumble G L *r^n) := fort G L F H h n u t (fun i x=>shellM G x (Γ (F i))) (fun j k x=> arcX n (-rebate (H j) k) x) (fun i j k w=> shea G (Γ (F i)) _ (by simpa only [River,norm_neg] using (g i j k w)) u t)
lemma plaque_right (g:∀ i j:X,∀ k∈L.s, River r (rebate (H j) k) (Γ (F i))): Cast (BddT n) P (bumble G L *r^n) := by
 refine fort G L F H h n u t (fun i x=>arcX n (Γ (F i)) x) (fun j k x=>shellM G x (-rebate (H j) k)) fun i j k w=>?_
 let x:= Γ (F i); let y:= -rebate (H j) k; have he: River r y x:=by simpa only [x,y,River,norm_neg] using (g i j k w)
 change ‖shear G (x+y)-∑ i∈coon n, arcX n x i*shellM G i y‖ ≤ _; rw [add_comm]; simp_rw [mul_comm (arcX n x _)]; exact shea G _ _ he u t
#print axioms plaque_left
#print axioms plaque_right
end Midway
end YM.CF.Window.ArchiveK
