import YM.SU5.FiniteGaugeData.Lapis.Waffle
import YM.Work.F03.Flat
import YM.Work.G06.TurnSlot
/-! # Frame. Ambient tangent Gaussian and projection prices for growth occupancy.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 20000
set_option linter.flexible false
set_option quotPrecheck false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Lapis
open Function Finset Filter MeasureTheory ProbabilityTheory Matrix Lattice Wilson RG Precision Tree Next.Fluctuations Work.F03
open Pressure Exterior Laurent Bloch Drachma Galope Avenue Galope.Press Wrist Poeme Haute Punch
open scoped Topology InnerProductSpace Matrix MatrixOrder RealInnerProductSpace ContDiff BigOperators NNReal ENNReal Kronecker Classical
namespace Lumi
-- Cuba. individual vision.Sensor.
open Affiche Next.Rank Next.Rank.Spindle
variable {ι:Type} [Fintype ι][DecidableEq ι] {G:Gauge} (T:Duct G ι){n:Side}{C h r t b:ℝ}(s:Signed)(x:Site n) (g: Portion n G)
local notation "A"=> Portion n G
local notation "B"=> T.seen
local notation "Y"=> ι → G.Color
local notation "I"=> macroK ι T
-- uniform coercion names.Plume.
def imprint:A →ₗ[ℝ] (ι→G.Color):= by
 let f(g:A):ι→ G.Color:= fun i=> (Γ T s i).2 • g (slotFace (Γ T s i).1 x,false)
 exact { toFun:=f, map_add':=fun p q=> funext (fun i=> smul_add _ _ _), map_smul':=fun t p=>funext (fun i=> smul_comm ((Γ T s i).2) t (p.ofLp (slotFace (Γ T s i).1 x,false))) }
def view :ℝ:= T.seen (imprint T s x g)
lemma unitJ(i:ι): |(Γ T s i).2|=1:=by rcases (marker s (G:=G) (T.beam i)).1 with h|h <;> (change |(pick (G:=G) s _).2|=_; rw [h]; norm_num)
-- no finite-dimensional magic on Cap.Stage
private lemma contLeg {E F:Type} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ E] (L:E→ₗ[ℝ] F)(p:F→ℝ)(h:ContDiff ℝ 1 p): ContDiff ℝ 1 (p ∘ L):=h.comp L.toContinuousLinearMap.contDiff
lemma paidV : ContDiff ℝ 1 (view T s x):= contLeg (imprint T s x) T.seen T.registered
-- parent.Future arrays
variable (R:Finset (Site n))(u:Site n→Signed)
local notation "J"=> Site n
local notation "P"=> Spindle.patch (macroK ι T)
-- disjoint; will later permit suborders.P.Proof unchanged orientation halo. Big κ
abbrev tribe (R:Finset (Site n)): Prop:= Set.PairwiseDisjoint (R:Set (Site n)) (Spindle.patch (macroK ι T))
abbrev touchR(R:Finset (Site n))(y:ℝ): A→ℝ := fun p=> y *∑ i∈R,view T (u i) i p
local notation "α"=> Real.sqrt (Fintype.card (Site n))
include u
lemma boost_sum (V:tribe T R)(p:A)(i:ι): (∑ j∈R,‖ imprint T (u j) j p i‖) ≤ Real.sqrt (Fintype.card (Site n))* ‖p‖:=by
 let w(j:J): Twin n:= (slotFace (Γ T (u j) i).1 j,false)
 let f(j:J):= ‖p (w j)‖; have he(j:J): ‖imprint T (u j) j p i‖ = f j:=by
    change ‖(Γ T (u j) i).2 • p (w j)‖=_; rw [norm_smul, Real.norm_eq_abs,unitJ, one_mul]
 let B':ℝ:= Fintype.card (Site n); have hm:Set.InjOn w R:=by
    intro j p k q v; by_contra h; apply Finset.disjoint_left.mp (V p q h) (nearby T (u j) i j); rw [show (slotFace (Γ T (u j) i).1 j).1=(slotFace (Γ T (u k) i).1 k).1 from congr_arg (fun i:Twin n=>i.1.1) v]; exact nearby T (u k) i k
 have hv: ∑ i∈R, f i^2 ≤ ‖p‖^2:=by
    let g(x:Twin n):= ‖p x‖^2; rw [PiLp.norm_sq_eq_of_L2]; calc
       _ = ∑ j∈R.image w,g j:= by rw [sum_image hm] -- tune proof HM
       _ ≤ _:=sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun x _ _=> sq_nonneg _)
 let S(i:J):=f i; simp_rw [he]; have hα:0 ≤ α:=Real.sqrt_nonneg _; apply (sq_le_sq₀ (sum_nonneg (show ∀ i∈R,0≤ f i from fun i _=>norm_nonneg _)) (mul_nonneg hα (norm_nonneg _))).1
 rw [mul_pow,Real.sq_sqrt (by positivity : (0:ℝ) ≤ Fintype.card (Site n))]; calc
    _ ≤ (R.card:ℝ)*∑ i∈R,f i^2:= by simpa only [one_mul, one_pow, sum_const,nsmul_eq_mul, mul_one] using sum_mul_sq_le_sq_mul_sq R (fun _=>1) f -- tune sum_const maybe
    _ ≤ _:=mul_le_mul (by exact_mod_cast R.card_le_univ) hv (sum_nonneg (fun i _=>sq_nonneg _)) (by positivity)
abbrev prizeL (b:ℝ):ℝ:=b*T.c * Fintype.card ι
omit u in
lemma prize_pos (e:0≤b):0≤ prizeL T b:=by unfold prizeL; exact mul_nonneg (mul_nonneg e T.grant) (Nat.cast_nonneg _)
lemma phase_spread (V:tribe T R) (e: |t|≤b)(x y:A): |touchR T u R t x - touchR T u R t y| ≤ (prizeL T b)* Real.sqrt (Fintype.card (Site n))* ‖x-y‖:=by
 let f(j:J)(x:A):=view T (u j) j x; let g(j:J)(z:A):=imprint T (u j) j z; let U:= ∑ i∈ R, T.c * ∑ j:ι, ‖g i (x-y) j‖; have hp:(0:ℝ)≤ T.c:=T.grant
 have hv(j:J):|f j x-f j y|≤ T.c *∑ i:ι, ‖g j (x-y) i‖:=by
    let Q:=g j (x-y); apply le_trans (T.cheer (g j x) (g j y)); rw [show g j x-g j y=Q from (map_sub (imprint T (u j) j) x y).symm]; apply mul_le_mul_of_nonneg_left _ hp
    apply (pi_norm_le_iff_of_nonneg (sum_nonneg (fun i _=> norm_nonneg _))).2; intro i; exact single_le_sum (fun i _=>norm_nonneg (Q i)) (mem_univ i) -- tune
 unfold touchR; rw [←mul_sub,←sum_sub_distrib,abs_mul]; apply (mul_le_mul e (le_trans (Finset.abs_sum_le_sum_abs ..) (sum_le_sum (show ∀ j∈R, |f j x-f j y|≤ T.c * ∑ i:ι, ‖g j (x-y) i‖ from fun i _=>hv _))) (abs_nonneg _) ((abs_nonneg _).trans e)).trans; rw [← Finset.mul_sum,sum_comm]; -- tune
 have hj:0≤ b:= (abs_nonneg _).trans e; apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (sum_le_sum (fun i _=> boost_sum T R u V (x-y) i)) hp) hj).trans_eq; unfold prizeL; rw [sum_const,card_univ,nsmul_eq_mul]; ring
end Lumi
end YM.SU5.FiniteGaugeData.Lapis
#print axioms YM.SU5.FiniteGaugeData.Lapis.Lumi.phase_spread
