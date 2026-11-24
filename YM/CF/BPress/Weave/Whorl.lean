import YM.CF.BPress.Weave.Chunk
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
/-!
Matrix log entry budgets `eq:B-enorm`. `eq:B-jacdiff` trace exactly. Real CLM turn&back.
Log use all i with c0=0 (or +1 offsets via pull).
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Weave
open Function Filter Lattice Wilson RG Precision Grid Cube Bands Pressure Wealth Finset Branch Push.AbsoluteSums
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace
open SU Gauge
attribute [local instance] Gauge.frobInner
variable {s:Side}{B:BandWidth}(X : Bands s B)
variable (F:Fare X)(u l:ℝ)
def grainSelect (D r k:ℕ) := 2*(k:ℝ) * grainFee D (k*r)
structure Summer (r k:ℕ) : Prop where
 pos : 0<l
 bound : l≤u
 self S : IsSelfAdjoint (F S)
 margin S : Margins (F S) l u
 seen : Connect X F r
 buyL : grainFee B.D (k*r)*cost_strand u l k≤ 1/2
 k_pos : 0<k
-- Norm summable uses general result any complete space (mathlib assumes NormOneClass?)
def shade (F:Fare X)(u:ℝ) (d:ℕ→ℝ)(j:ℕ)(S:Finset X.Hcols) : BEnd X:= ∑' i:ℕ,d i • sea X F u S ^(i+j)
def waker (F:Fare X)(u:ℝ) (S:Finset X.Hcols): BEnd X:=∑' i:ℕ, sea X F u S ^ i
def sun (F:Fare X)(u:ℝ) (S:Finset X.Hcols): BEnd X:= u⁻¹ • waker X F u S
def lcoef (k:ℕ):= ((k:ℝ)+1)⁻¹
def logp:= shade X F u lcoef 1
lemma eye_row (A:ℕ→BEnd X)(h:Summable A)(i j:Axon X): rowM X (∑' n,A n) i j=∑' n,rowM X (A n) i j:= by
 let L:=ContinuousLinearMap.apply ℝ (RaySpace X) (q_ray X j); -- tune
 let P := (innerSL ℝ (q_ray X i)).comp L; exact P.map_tsum h
namespace Summer
variable {r k:ℕ}{X F u l}
variable (h:Summer X F u l r k)
include h
lemma hp : 0 < u:= h.pos.trans_le h.bound
lemma strict (S:Finset X.Hcols): ‖sea X F u S‖<1:= sea_strict X F u l S h.pos h.bound (h.self S) (h.margin S)
lemma powers (i:ℕ): Aura (soils X) (grassRate (k*r)) (grainFee B.D (k*r)*((1:ℝ)/2)^(i/k)) (rise X (sea X F u) i):=by
 refine grain_all X u l _ r k (fun i _ S=>?_ ) (Connect.one.sub (h.seen.scale u⁻¹)) (fun S=> sea_pow X F u l S h.pos h.bound (h.self S) (h.margin S) k) h.buyL h.k_pos i; apply le_trans (sea_pow X F u l S h.pos h.bound (h.self S) (h.margin S) i); apply Real.exp_le_one_iff.mpr; apply mul_nonpos_of_nonpos_of_nonneg _ (Nat.cast_nonneg _); have hp:=h.pos; have hv:=h.hp; exact neg_nonpos.mpr (by positivity)
lemma chills (d:ℕ→ℝ)(p:∀ i,|d i| ≤ 1)(j:ℕ)(S:Finset X.Hcols) : Summable (fun i:ℕ=>d i • sea X F u S ^(i+j)):=by
 have hp : Summable (fun i:ℕ=> (1-l/u)^i):= by apply summable_geometric_of_lt_one; exact sub_nonneg.mpr ((div_le_one h.hp).mpr h.bound); exact sub_lt_self _ (div_pos h.pos h.hp)
 apply ((summable_nat_add_iff j).mpr hp).of_norm_bounded; intro i; rw [norm_smul]; exact (mul_le_of_le_one_left (norm_nonneg _) (p i)).trans (sea_spec X F u l S h.pos h.bound (h.self S) (h.margin S) _)
lemma painted (d:ℕ→ℝ)(p:∀ i,|d i| ≤ 1)(j:ℕ) : Aura (soils X) (grassRate (k*r)) (grainSelect B.D r k) (fun S=> rowM X (shade X F u d j S)):=by
 let f:= fun (n:ℕ)(S:Finset X.Hcols)=> d n • rise X (sea X F u) (n+j) S; let Z(i:ℕ):= grainFee B.D (k*r)* ((1:ℝ)/2)^(i/k); have he: (fun S=> rowM X (shade X F u d j S))=Aura.tPlot f:=by ext i v w; unfold shade; rw [eye_row X _ (h.chills d p j i)]; exact tsum_congr fun n=>congrFun (congrFun (row_sm ..) v) w -- tune
 rw [he]; apply Aura.flow _ (fun i=>Z (i+j)) _ (budget_pull (fun i=>i+j) (add_left_injective _) (chuck k h.k_pos _ (grain_nn B.D (k*r)))) (gr_pos _).le; intro i; apply ((h.powers (i+j)).scale (d i)).weaken; exact mul_le_of_le_one_left (mul_nonneg (grain_nn ..) (by positivity)) (p i)
lemma cold : Aura (soils X) (grassRate (k*r)) (grainSelect B.D r k) (fun S=> rowM X (waker X F u S)):=by simpa only [shade,waker,one_smul,add_zero] using h.painted (fun _=>1) (fun _=> abs_one.le) 0
lemma slow : Aura (soils X) (grassRate (k*r)) (grainSelect B.D r k) (fun S=> rowM X (logp X F u S)):= h.painted _ (fun i=>by unfold lcoef; rw [abs_of_nonneg (by positivity : 0≤((i:ℝ)+1)⁻¹)]; exact inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg i (α:=ℝ))])) _
lemma inverse (S:Finset X.Hcols): sun X F u S * F S=1 ∧ F S* sun X F u S=1:=by
 have he:Summable (fun i:ℕ=> sea X F u S^i):=summable_geometric_of_norm_lt_one (h.strict S)
 have ht:1-sea X F u S=u⁻¹ • F S:=sub_sub_cancel ..; have hp (A B:BEnd X) : (u⁻¹ • A)*B=A*(u⁻¹ • B):=by ext1 i; rw [ContinuousLinearMap.mul_apply,ContinuousLinearMap.mul_apply,ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,map_smul]
 refine ⟨?_,?_⟩; rw [sun,hp,←ht]; exact he.tsum_pow_mul_one_sub; rw [sun,← hp,←ht]; exact he.one_sub_mul_tsum_pow
lemma sun_cap : Aura.RowCap (fun S=>rowM X (sun X F u S)) (u⁻¹* grainSelect B.D r k):=by have ht:= (h.cold.cap (gr_pos _).le).scale (u⁻¹); rw [abs_of_pos (inv_pos.mpr h.hp)] at ht; unfold sun; simp_rw [row_sm]; exact ht -- tune
lemma turnU_cap : Aura.RowCap (fun S=> rowM X (F S)) (grainFee B.D r*u):=by
 have he : Aura _ _ _ _ := charge_bay h.seen h.hp.le (fun S=> Margins.cap ((h.margin S).broad (by linarith [h.pos,h.hp] : -u≤ l) le_rfl) h.hp.le (h.self S)) (gr_pos r).le; simpa only [grainFee,grassRate,inv_mul_cancel₀ (show (taxArea r:ℝ) ≠ 0 by unfold taxArea; positivity)] using he.cap (gr_pos _).le -- tune
-- linear equivalence built from inverse
end Summer
abbrev Sep (X:Bands s B) := RaySpace X ≃L[ℝ] RaySpace X
variable {X u l F}{r k:ℕ} -- clean
noncomputable def swung (h:Summer X F u l r k)(S:Finset X.Hcols) : Sep X where
 toFun := F S
 invFun := sun X F u S
 map_add' := map_add _
 map_smul' := map_smul _
 continuous_toFun := (F S).continuous
 continuous_invFun := (sun X F u S).continuous
 left_inv x := congrArg (fun P:BEnd X=> P x) (h.inverse S).1
 right_inv x:= congrArg (fun P:BEnd X=> P x) (h.inverse S).2
end YM.CF.BPress.Weave
