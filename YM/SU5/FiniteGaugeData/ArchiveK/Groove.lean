import YM.SU5.FiniteGaugeData.ArchiveK.Dwarf
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
open Violas LightK Waltz
variable (A B:Finset Cover)(G:E4≃ₗᵢ[ℝ] E4)(L:FilterK)(b:Bool)(x y:E4)
abbrev Pick(A B:Finset Cover): Ruler (Beam A) (Beam B):= Matrix.of fun i j=> (spiral (emitX (i.1.val-j.1.val))*keel) i.2 j.2
lemma keel_cut : cutM plusHalfᶜ= keel:=by rw [keel, Adef,←raising,←cutM_read' plusHalf]; abel
abbrev tax (v:Cover): Cover:= if b then v else -v
abbrev rewardC :ℂ:= if b then 1 else -1
local notation "Φ"=> Waltz.Beam A
local notation "Ψ"=> Waltz.Beam B
local notation "Ρ"=> Violas.page
lemma duetT (p:Cover): tax b (tax b p)=p:=by cases b<;> simp [tax]
lemma ticketM (u v:Cover):tax b (u-v) = tax b u-tax b v:=by cases b<;> simp [tax,sub_eq_add_neg,add_comm]
lemma fee1 : ‖rewardC b‖=1:=by cases b <;> simp [rewardC]
lemma track (i:Cover) : rewardC b • spiral (emitX (tax b i))= spiral (emitX i):=by cases b <;> simp [spiral_other,tax,rewardC]
variable {X:Type*} [Fintype X][DecidableEq X](U V:X→Cover) -- local notation U conflict.
local notation "Χ"=> page X
variable {P:Op X}(h:∀ x y, P x y=stone G L (U x) (V y))
variable (p:∀ x:X,tax b (U x)∈A)(v:∀ x:X,∀ i∈L.s,tax b (V x-i) ∈ B)
-- lift lower guard location independent.L Budget.use hank.P
private lemma base (Z : Glue) (x y:X)(i:Cover)(w:i∈L.s): let f:Φ:= (⟨tax b (U x),p _⟩,hat_a Z); let g:Ψ:= (⟨tax b (V y-i),v _ _ w⟩,hed_a Z); rewardC b *Pick A B f g= (spiral (emitX (U x)+ -rebate (V y) i)) (hat_a Z) (hed_a Z):=by
 intro f g; let u:=U x; let y':= V y-i; let H:=spiral (emitX (tax b u-tax b y')); change rewardC b *((spiral (emitX (tax b u-tax b y'))*keel) _ _)=_; rw [←keel_cut,compass', ←ticketM, if_pos (hed_mem _)]; change ((rewardC b • spiral (emitX (tax b (u-y')))):Op SpinIdx) (hat_a Z) (hed_a Z)=_; rw [track,emit_sub]; rfl -- tune
abbrev sir(L:FilterK):ℝ:=∑ i∈ L.s, ‖L.f i‖
lemma rope(a b:ℕ) : True:=trivial -- remove
private lemma gripW {S:Type*}[Fintype S][DecidableEq S](f:X→S) (g:X→ℂ)(x:ℝ)(t:0≤x)(z:∀ i,‖g i‖≤x): ‖grip f g‖ ≤ page S * (page X:ℝ)*x:= jingle (grip f g) x t (fun i j=>by unfold grip; simp only [Matrix.of_apply]; split; exact z j; rw [norm_zero]; exact t)
abbrev fareQ (G:E4 ≃ₗᵢ[ℝ] E4):ℝ:=∑ i:Glue,‖weigh G i‖
def coins (x y z:ℕ):ℝ:= fareQ G*sir L * (x:ℝ)^2*y*z
lemma fare_n : 0 ≤ fareQ G:= Finset.sum_nonneg fun i _=>norm_nonneg _
lemma sir_n : 0 ≤ sir L:= Finset.sum_nonneg fun i _=>norm_nonneg _
lemma coins_pos (x y z:ℕ): 0 ≤ coins G L x y z:= by have t:= sir_n L; have h:= fare_n G; unfold coins; positivity
include p v h
lemma onward (c:ℝ)(q:0≤ c) : ∃ f : Glue→Ruler X Φ,∃ g:Glue→Ruler Ψ X, (∑ i:Glue,f i * Pick A B*g i)= P ∧ ∑ i:Glue,‖f i‖*c*‖g i‖ ≤ c*coins G L (page X) (page (Beam A)) (page (Beam B)) := by
 let Z:=Pick A B; let fu(i:X):A:=⟨tax b (U i), p _⟩; let fv(i:X)(j:L.s):B:=⟨tax b (V i-j.val), v _ _ j.property⟩; let Fg(x:Glue):= grip (fun i:X=> (fu i,hat_a x)) (fun _=> star (rewardC b*weigh G x)); let F'(x:Glue): Ruler X Φ:= (Fg x)ᴴ; let G'(x:Glue)(j:L.s): Ruler Ψ X:= grip (fun i=> (fv i j,hed_a x)) (fun _=> L.f j.val); let H(x:Glue):= ∑ j:L.s,G' x j
 have he(x:Glue)(j:L.s)(i z:X) : (F' x * Z * G' x j) i z= L.f j.val * (weigh G x * (spiral (emitX (U i)+ -rebate (V z) j.val) (hat_a x) (hed_a x))):=by unfold F' Fg G'; rw [on_grip,grip_off,star_star, ← base A B L b U V p v x i z j.val j.property]; unfold fu fv Z; ring
 refine ⟨F',H,?_,?_⟩
 · apply Matrix.ext; intro i j; rw [Matrix.sum_apply,h]; unfold H stone; unfold Z at he; simp_rw [Matrix.mul_sum, Matrix.sum_apply, he,shear]; rw [sum_comm]; simp_rw [←mul_sum]; rw [←Finset.sum_coe_sort L.s]; -- tune bookkeeping
 let α:= ((page (Beam A)):ℝ)*page X; let μ:=((page (Beam B)):ℝ)*page X; let t:= sir L; have hx(i:Glue):‖F' i‖ ≤ α * ‖weigh G i‖:= by rw [show ‖F' i‖=‖Fg i‖ from Matrix.l2_opNorm_conjTranspose (Fg i)]; apply gripW _ _ _ (norm_nonneg _) (fun j=>?_); simp only [norm_star,norm_mul,show ‖rewardC b‖=1 from fee1 b,one_mul, le_refl]
 have hy(i:Glue) : ‖H i‖ ≤ μ*t:=by apply (norm_sum_le ..).trans; refine (sum_le_sum (g:=fun j:L.s=> μ*‖L.f j.val‖) fun j w=> gripW _ _ _ (norm_nonneg _) (fun i=>le_rfl)).trans_eq ?_; unfold t sir; rw [← Finset.mul_sum, ← Finset.sum_coe_sort L.s]; -- tune
 refine (sum_le_sum (g:=fun i:Glue=>‖weigh G i‖*(α*c*(μ*t))) (fun i _=> ((mul_le_mul (mul_le_mul_of_nonneg_right (hx i) q) (hy i) (norm_nonneg _) (by unfold α; positivity))).trans_eq ?_)).trans_eq ?_; swap; · rw [← Finset.sum_mul]; unfold α μ coins fareQ t; ring
 ring
#print axioms onward
end Midway
end YM.CF.Window.ArchiveK
