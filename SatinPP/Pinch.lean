import SatinPP.Bastille
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3500
set_option maxHeartbeats 650000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six MacroGrid

open OS.Semigroup
variable {G:Hilbert}{j:Axis}(S:OS.Semigroup G j)
lemma bow_trip {h:ℝ}(e:0<h)(v:G)(n:ℕ):
 dist v (S.E ((n:ℝ)*h).toNNReal v)≤ n*dist v (S.E h.toNNReal v):=by
 induction n with
 | zero=>simp [S.eZero]
 | succ n ih=>
    let a:ℝ≥0:=((n:ℝ)*h).toNNReal
    rw [Nat.cast_succ,add_mul,one_mul,Real.toNNReal_add (by positivity) e.le,S.time]
    apply (dist_triangle _ (S.E a v) _).trans
    rw [add_mul,one_mul]
    apply add_le_add ih
    rw [ContinuousLinearMap.comp_apply,dist_eq_norm,dist_eq_norm,←map_sub]
    exact ((S.E a).le_opNorm _|>.trans (mul_le_of_le_one_left (norm_nonneg _) (S.shrinks _)))


/-- For all v bounded by M and with chord s of length ≥L s, all sufficiently short chords h have length ≥ l h too. -/
lemma bow {s l L M:ℝ}(p:0<s)(q:0<l)(z:l<L):∀ᶠ h in 𝓝[>] (0:ℝ),∀v:G,‖v‖≤M→ s*L ≤ dist v (S.E s.toNNReal v)→
 h*l ≤ dist v (S.E h.toNNReal v):= by
 let f h:= (s+h)*l+(2/s*h)*M
 have t:f 0<s*L:=by unfold f;simpa using mul_lt_mul_of_pos_left z p
 have e:Continuous f:=by unfold f;fun_prop
 filter_upwards [self_mem_nhdsWithin, e.continuousWithinAt (s:=Set.Ioi 0)|>.eventually (gt_mem_nhds t)] with h u w v d b
 have u:0<h:=u
 let n:=⌈s/h⌉₊
 let a:ℝ:=n*h
 have t₀:s ≤ a:= by unfold a;rw [←div_le_iff₀ u];exact Nat.le_ceil _
 have t₁:a ≤ s+h:= le_trans (mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one (div_nonneg p.le u.le)).le u.le) (by rw [add_mul,one_mul,div_mul_cancel₀ _ u.ne'])

 by_contra! m
 refine (not_le_of_gt w) ((b.trans (dist_triangle _ (S.E a.toNNReal v) _)).trans ?_)
 apply add_le_add
 · refine ((bow_trip S u v n).trans (mul_le_mul_of_nonneg_left m.le (Nat.cast_nonneg _))).trans ?_
   rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right t₁ q.le
 rw [dist_eq_norm, ←sub_apply]
 have B:=soften_le S p t₀ le_rfl
 exact (ContinuousLinearMap.le_opNorm ..).trans (mul_le_mul
    (B.trans (mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith only [u,t₀],by linarith only [t₁]⟩) (by positivity))) d (norm_nonneg _) (by positivity))

