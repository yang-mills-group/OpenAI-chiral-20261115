import GaugeFieldConstruction.Vespers
import YM.CF.Moto.Rune
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 30000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
local notation "GS"=> SU.group
variable {n:Side}{p: BudgetPoint}{Q: InkD n}{o:Skye.Seat n}{X:Scree.Hub n}{h c:ℝ}
namespace Lenten
open Bank Laurent Bloch Tap Hove Spire
abbrev Plane := Four ℝ
abbrev Views := Plane ×Plane
abbrev angle (p:Plane): Momentum:= fun i=>(p i:ℂ)
def rom (x:Cover):Plane→L[ℝ]ℝ := ∑ i: Axis,(x i:ℝ) • (ContinuousLinearMap.proj i)
lemma rom_p(x:Cover)(i:Plane): rom x i=∑ j:Axis,(x j:ℝ)*(i j):=by unfold rom; rw [_root_.sum_apply]; rfl
lemma rom_e(x:Cover)(i:Plane): PayS (rom x) i=Laurent.mode (angle i) x:=by rw [PayS,rom_p,Laurent.mode, Complex.ofReal_sum]; simp only [Complex.ofReal_mul]; apply congrArg Complex.exp; congr 1; refine sum_congr rfl fun _ _=>?_ ; rw [mul_comm]; unfold angle; push_cast; ring
lemma radius_Z (x:Cover): ‖rom x‖≤ lateral x:=by
 apply ContinuousLinearMap.opNorm_le_bound _ (Nat.cast_nonneg _); intro i; rw [rom_p]; apply (norm_sum_le ..).trans; unfold lateral; rw [Nat.cast_sum, sum_mul]; apply sum_le_sum; intro j _; rw [norm_mul, Real.norm_eq_abs, ← Int.cast_abs]; simp only [Int.abs_eq_natAbs, Int.cast_natCast]; exact mul_le_mul_of_nonneg_left (norm_le_pi_norm i _) (Nat.cast_nonneg _)
variable (M:Male) (b:Bool)
abbrev binor (M:Male)(b:Bool)(x:Plane): Pal:= if b then boot 4 M (angle x) else 1-boot 4 M (angle x)
lemma ang₀ : angle 0=0:=by funext i; simp [angle]
lemma buoy_l : ∀ᶠ x in 𝓝 (0:Plane), angle x ∈ Next.Free.baseCube:=by
 filter_upwards [ball_mem_nhds (0:Plane) Real.pi_pos] with x h; have hp:= mem_ball_zero_iff.mp h
 refine ⟨(by unfold angle; ext i; simp), fun i=>?_⟩; unfold angle; rw [Complex.ofReal_re]; exact (norm_le_pi_norm x i).trans hp.le -- tune
lemma palP : ∀ᶠ x in 𝓝 (0:Plane), IsStarProjection (binor M b x):=by
 filter_upwards [buoy_l] with x h; obtain ⟨e,v⟩:= Fir.firm_bar 4 M.val M.property (Next.Free.base_subset_realCube Next.Free.zone_pos h)
 let c:=Tap.boot 4 M (angle x); have he :IsStarProjection c:=⟨(by change c*c=c; unfold c Tap.boot; rw [op_kron_mul,e,one_mul]), by unfold IsSelfAdjoint c Tap.boot; rw [op_star_kron,v,star_one]⟩
 cases b; · exact he.one_sub
 exact he
lemma binBase : binor M b 0=baseF b:=by unfold binor; rw [ang₀, Tap.boot_o]; cases b <;> simp [baseF]
noncomputable def flare_one (i j:Hove.Kt): ℂ →L[ℝ] Pal := by
 refine LinearMap.toContinuousLinearMap ⟨⟨Matrix.single i j,?_⟩,?_⟩
 · intro x y; exact Matrix.single_add ..
 intro a b; exact (Matrix.smul_single ..).symm
lemma flare_draw (u:Pal) : u=∑ i:Hove.Kt,∑ j:Hove.Kt,flare_one i j (u i j):=by
 ext a b; simp_rw [Matrix.sum_apply]; change _= ∑ i:Hove.Kt,∑ j:Hove.Kt,Matrix.single i j (u i j) a b; simp [Matrix.single_apply,ite_and]
abbrev CostOle {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F](z:Ole E F) := ‖z‖
abbrev clanJ {I J E F:Type}[Fintype I][Fintype J][NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F](P:I→J→Ole E ℂ)(Q:I→J→ℂ→L[ℝ]F): Ole E F:=∑ i:I,∑ j:J,postF (P i j) (Q i j)
abbrev clanK {I J F:Type}[Fintype I][Fintype J][NormedAddCommGroup F][NormedSpace ℝ F](Q:I→J→ℂ→L[ℝ]F)(C:ℝ): ℝ:=∑ i:I,∑ j:J, ‖Q i j‖*C
lemma c_nn {I J F:Type}[Fintype I][Fintype J][NormedAddCommGroup F][NormedSpace ℝ F](Q:I→J→ℂ→L[ℝ]F)(C:ℝ)(p:0≤C):0 ≤ clanK Q C:=by unfold clanK; positivity
lemma berth (a:ℝ)(F:Plane→ Pal)(P:Hove.Kt→Hove.Kt→ Ole Plane ℂ)(p:∀ i j,AptK (fun x=> F x i j) (P i j)):
 let Z:=clanJ P flare_one
 AptK F Z:=by
 intro Z; let V(i j:Hove.Kt)(x):= flare_one i j (F x i j); let K:=∑ i:Hove.Kt,∑ j:Hove.Kt,V i j
 have he:AptK K Z:= AptK.sumV univ _ _ (fun i _=> AptK.sumV univ (fun j=>V i j) _ (fun j _=> (p i j).geomF _))
 have ht(i): F i=K i:=by unfold K; simp_rw [Finset.sum_apply]; exact flare_draw _
 exact he.equal (Filter.EventuallyEq.of_eq (funext fun i=>(ht i).symm)) -- tune
set_option maxHeartbeats 120000 in
lemma post_pay {E F G:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup G][NormedSpace ℝ G](x:Ole E F)(v:F→L[ℝ] G):‖postF x v‖≤ ‖v‖*‖x‖:=by
 let Y:= ‖v‖*‖x‖; let X:=postF x v; have hp:0≤Y:=by positivity
 rw [Prod.norm_def, Prod.norm_def]; refine max_le ((v.le_opNorm x.1).trans (mul_le_mul_of_nonneg_left (le_max_left ..) (norm_nonneg _))) (max_le ((ContinuousLinearMap.opNorm_comp_le v x.2.1).trans (mul_le_mul_of_nonneg_left ((le_max_left ..).trans (le_max_right ..)) (norm_nonneg _))) ?_)
 apply ContinuousLinearMap.opNorm_le_bound X.2.2.val hp; intro i; apply ContinuousLinearMap.opNorm_le_bound _ (M:=Y*‖i‖) (by positivity); intro j
 let L:=x.2.2.val
 refine (show ‖v (_ )‖ ≤ _ from v.le_opNorm (L i j)).trans ?_; unfold Y; apply le_trans (mul_le_mul_of_nonneg_left ((L i|>.le_opNorm j).trans (mul_le_mul_of_nonneg_right (L.le_opNorm i) (norm_nonneg _))) (norm_nonneg _)); rw [mul_assoc,mul_assoc,mul_assoc]; gcongr; exact (le_max_right ..).trans (le_max_right ..)
private lemma berth_money {I J E L:Type}[Fintype I][Fintype J][NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup L][NormedSpace ℝ L](f:I→ J→ ℂ→L[ℝ]L)(K:I→J→ Ole E ℂ) (C:ℝ)(p:∀ i j,‖K i j‖≤C) : CostOle (clanJ K f) ≤ clanK f C:=by
 let Z:= fun i j=> postF (K i j) (f i j); change ‖∑ i:I,∑ j:J,Z i j‖≤ ∑ i:I,∑ j:J,‖f i j‖*C; apply le_trans (norm_sum_le univ (fun i:I=> ∑ j:J,Z i j)); apply sum_le_sum; intro i _; apply (norm_sum_le univ (Z i)).trans; apply sum_le_sum; intro j _; exact (post_pay _ _).trans (mul_le_mul_of_nonneg_left (p i j) (norm_nonneg _))
set_option maxHeartbeats 75000 in
set_option maxRecDepth 2500 in
lemma FlightJet (b:Bool):∃ c:ℝ,0≤ c ∧∀ M:Male, ∃ Z:Ole Plane Pal,AptK (binor M b) Z∧ CostOle Z≤ c:=by
 obtain ⟨C,c,H⟩:= pawn_p 4 2 (by norm_num) b
 let r(x:Cover):=1+(Laurent.size x:ℝ); have h(x):1 ≤ r x:=le_add_of_nonneg_right (Nat.cast_nonneg _); let A:=clanK flare_one C; have hp:0≤A:=c_nn _ _ c.le
 refine ⟨A,hp,fun M=>?_⟩; let P:=Paw 4 M b; let B:=binor M b
 have hx(i j:Hove.Kt): ∃ v:Ole Plane ℂ,AptK (fun x=>B x i j) v ∧ ‖v‖≤ C:=by
    let f(x:Cover):=P x i j; have ht (x:Cover):‖rom x‖ ≤ r x:= (radius_Z x).trans (show (_:ℝ)≤1+ (Laurent.size x:ℝ) from le_add_of_nonneg_left zero_le_one); have hv:=H M i j; obtain ⟨Z,g,hZ,s1,s2,s3⟩:= mainStream f rom r ht h hv.2.1; refine ⟨Z,g.equal ?_,hZ.trans hv.2.2⟩; filter_upwards [buoy_l] with x p
    simp_rw [rom_e]; exact (hel_pawn 4 (by norm_num) M b).readK _ p i j
 choose F ha hw using hx; let T_P :=clanJ F flare_one
 refine ⟨T_P,?_ ,?_⟩
 · exact berth C B F ha
 have h:= berth_money (L:=Pal) flare_one F C hw
 exact h
end Lenten
end YM.CF.TableF
end
