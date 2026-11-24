import Anomaly.Gab.Norn
import Anomaly.Gab.Crown
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Py
open Function Module NormedSpace Filter Metric Finset
open Moto Hove Oath Haro Bake Fock Roots Rive Neon
open Lattice Wilson RG Lat Tune QuadClock Cube Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
variable {I E:Type}[Fintype I][NormedAddCommGroup E][NormedSpace ℂ E][FiniteDimensional ℂ E] {B:Basis I ℂ E} {m:ℕ}(pκ:SketchA B m) {L:Side}{X Y:BudgetPoint}{H w Q A K C v0 v1 v2 ε T:ℝ}{z:ℂ}
namespace SketchA
variable {u f q:ℝ}{P:ArmorK}
variable (t: ScaleKit pκ K C v0 v1 v2 A T u f ε L)(S:Melon L X Y z H Q A w)
variable (Z F: Sum I Unit→ArcΦ × ℂ)(h:∀ i,Markup L X Y z H Q A w K C v0 v1 v2 (Z i).1 (F i).1 (Z i).2 (F i).2) (y:∀ i,pκ.winA H (Z i)= (Q:ℂ) • (ρZee B i))(p:0<q)
include t S h y p
lemma portD :∃ D:(E × ℂ)≃ₗ[ℂ](E × ℂ), Tiara pκ Z F z H Q w K A (ρθ (ρZee B)* f) u (shadowY u K C) q L D:=by
 obtain ⟨⟨G,a,g⟩,c,u⟩:= pκ.arrester t.earn t.bite S t.grants t.minkPay.le t.pays t.buys t.grip Z F h y; exact calyx pκ S F G a g h y c t.tunes u t.rule t.rites.le p
omit t S h y p
local notation "ι"=> Sum I Unit
local notation "ΣS"=> ρZee B
local notation "κπ"=> κprobe mintR L H (A*Q) w z
local notation "ΠV"=> E × ℂ
variable {c t':ℝ}
variable (D:(E × ℂ)≃ₗ[ℂ](E × ℂ))(g:Tiara pκ Z F z H Q w K A t' u c q L D)(qQ:q ≤ 2*Q)(qT:Q ≤ 2*q)(p':0<c)(qK:0≤u)(QR:0<t') (QQ:0<Q)
def knotLove (B:Basis I ℂ E)(C:ℝ):= 2* βSize (ρZee B) * (Fintype.card (Sum I Unit):ℝ)*C
include g
lemma frontUp (x:E × ℂ):∑ i, ((ρZee B).coord i (D x)) • pκ.winA H (F i)= (q:ℂ) • x:=by
 let P:B = B :=rfl --
 have he:x= D.symm (∑ i, ((ρZee B).coord i (D x)) • ((ρZee B) i)):=by rw [show (∑ i,_) =_ from (show (∑ i, ((ρZee B).coord i (D x)) • ((ρZee B) i)) =D x from (ρZee B).sum_repr _),LinearEquiv.symm_apply_apply]
 nth_rw 2 [he] -- nth? x many? inspect. use Eq.trans instead.
 simp_rw [map_sum, map_smul, Finset.smul_sum, g.bead,←smul_assoc,smul_eq_mul,mul_comm (↑q:ℂ)] -- tune
omit g
lemma βfront (i:I): ‖B i‖≤ βSize B:= (single_le_sum (fun j _=>norm_nonneg (B j)) (mem_univ i)).trans (le_add_of_nonneg_left zero_le_one)
lemma front_pos (B:Basis I ℂ E):0<βSize B:=add_pos_of_pos_of_nonneg zero_lt_one (sum_nonneg fun _ _=>norm_nonneg _)
include g
include qQ p QQ QR
lemma stretch (i:Sum I Unit)(x:ΠV): ‖(ρZee B).coord i (D x)‖≤ 2*(L.val:ℝ)^m * (t'*‖x‖):=by
 let Z:= pκ.coin_Z L Q i; have hp:= pκ.coin_pos L Q QQ i; apply (g.seat x i).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
 apply (div_le_iff₀ hp).2; apply qQ.trans; have ht:0 < (L.val:ℝ):= by positivity
 let p:= pκ.coin_range L Q QQ i
 exact (Eq.le (show 2*Q=2*(L.val:ℝ)^m* (Q*((L.val:ℝ)⁻¹)^m) by rw [inv_pow]; field_simp)).trans (mul_le_mul_of_nonneg_left (show _≤ Z from p.1) (by positivity))
lemma highTax (x:E × ℂ): ‖D x‖≤ knotLove B t' * (L.val:ℝ)^m * ‖x‖:=by
 let h0:=front_pos (ρZee B)
 have he : D x=(∑ i, ((ρZee B).coord i (D x)) • ((ρZee B) i)):= (show (∑ i,_) =_ from (ρZee B).sum_repr _).symm -- tune rw
 rw [he]; refine (norm_sum_le ..).trans ((Finset.sum_le_sum (g:=fun _=> 2*(L.val:ℝ)^m * (t'*‖x‖)*βSize (ρZee B)) (fun i _=>?_)).trans_eq ?_)
 · rw [norm_smul]; exact mul_le_mul (stretch pκ Z F p D g qQ QR QQ i x) (βfront i) (norm_nonneg _) (by positivity)
 rw [sum_const,nsmul_eq_mul,card_univ]; unfold knotLove; ring
include qK
abbrev fareZ (B:Basis I ℂ E)(t u K:ℝ):= (Fintype.card (Sum I Unit):ℝ) * (t*|K| *u)
lemma stretches_cost (x: E × ℂ): (∑ i, ‖(ρZee B).coord i (D x)‖*(K* κprobe mintR L H (A*Q) w z (Z i).1)) ≤ fareZ B t' u K *‖x‖* q:=by
 let U(i):= |K| * (u* pκ.coin_Z L Q i); apply le_trans (sum_le_sum (s:=univ) (g:=fun i:Sum I Unit=> t'*|K| *u*‖x‖ * q) (fun i _=>?_)); · unfold fareZ; rw [sum_const,card_univ,nsmul_eq_mul]; ring_nf; try rfl
 have hp:=g.seat x i; have hv : K*κπ (Z i).1 ≤ U i := (le_abs_self _).trans ((abs_mul ..).trans_le (mul_le_mul_of_nonneg_left (g.garb i) (abs_nonneg _)))
 have ht:=pκ.coin_pos L Q QQ i
 exact (mul_le_mul_of_nonneg_left hv (norm_nonneg _)).trans ((mul_le_mul_of_nonneg_right hp (show 0≤ U i from by unfold U; positivity)).trans_eq (by unfold U; field_simp))
end SketchA
end YM.CF.Py
