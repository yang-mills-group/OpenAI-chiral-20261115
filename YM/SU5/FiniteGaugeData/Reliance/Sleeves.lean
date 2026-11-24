import YM.SU5.FiniteGaugeData.Reliance.LiftG
import YM.SU5.FiniteGaugeData.Marked.Journey.Smokestack
/-!
# Strengthened homestead, uniform relative to growth cost

 This is at the `K.c m` (cast later), need an ext budget PLUS any `Metered`
 ticket (we don't need its charge or candles uniform over the observing level).
 Exact reflected doubling with the same localized weights. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Reliance
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal Classical
attribute [local instance] opCStarAlgebra
open Afterglow Afterglow.Journey
variable {K: Calibration} {m n:Side}
local notation "N"=> K.c m
local notation "bZ" i:max z:max => band (K.c m) i (Heat.gaugeShift K.B z) K.ℓ
variable {L:Loom (K.c m)} {X: Mark (K.c m)→ℂ}{D:ℝ}

lemma apt_ref {r c:ℝ}(i:Axis)(z:ℤ){f:Mark n}{S:Support (More n)}(p:Apt r c S f): Apt r c (S.image ((plane i z).anon n)) (reflMark i z f):=by
 intro x; unfold reflMark; rw [theta_fee]; change ‖f (reflFields i z x)‖ ≤ _; apply le_trans (p (reflFields i z x)); apply le_of_eq; change c * Real.exp (glow r S (fling i z n x.1))= _; rw [fling_eq,reflect_till]; rfl -- tuning
lemma apt_paired {r c:ℝ}(i:Axis)(z:ℤ){S:Support (More (K.c m))}{f:Mark (K.c m)}(h:S ⊆ band (K.c m) i z K.ℓ)(p:Apt r c S f): Apt r (c^2) (S.image ((plane i z).anon N) ∪ S) (reflMark i z f*f):=by
 let T:= S.image ((plane i z).anon N)
 have he:Disjoint T S:= Finset.disjoint_left.mpr (fun x a b=> Nat.not_lt_zero _ ((margin_separate i z K.buffer x x (image_subset_image h a) (h b)).trans_le (by rw [separation_self])))
 intro x; rw [glow_plus r he x.1, Real.exp_add]; refine (norm_mul_le (reflMark i z f x) (f x)).trans ?_; exact (mul_le_mul (apt_ref i z p x) (p x) (norm_nonneg _) (mul_nonneg (apt_pos p) (Real.exp_pos _).le)).trans_eq (by ring)

variable (G: Metered K m L X D)

-- geometric capacity for an untranslated OR translated given support; estimate in gauge volume units, D out front (can choose independent of level)
structure Gross {K:Calibration}(m:Side)(X:Mark (K.c m)→ℂ)(r C:ℝ): Prop where
 posC : 0 ≤ C
 budget {f:Mark (K.c m)} {S:Support (More (K.c m))} {c:ℝ} (p:Apt r c S f)(t:AtSupport false S f): ‖X f‖ ≤ c*Real.exp (C*(m.val:ℝ)^4)

variable {r C:ℝ}
include G

lemma stem (i:Axis)(k:ℕ){d:ℕ}(h:2^k*(d+addgap K) ≤ (N).val){S:Support (More N)}(w:rest K m S i d)
    {x:Mark N}{c:ℝ}(p:Apt r c S x)(q:AtSupport false S x):
    ∃ (y:Mark N)(T:Support (More N)),‖X x‖^(2^k:ℕ) ≤ ‖X y‖ ∧ Apt r (c^(2^k:ℕ)) T y ∧
       AtSupport false T y ∧ ∀ j:Axis,j≠i→∀ d',rest K m S j d' → rest K m T j d':=by
 induction k generalizing d S c x with
 | zero=> exact ⟨x,S,by simp,by simpa using p,q,fun _ _ _ v=>v⟩
 | succ k ih=>
   have ht:d+addgap K ≤ (N).val:=h.trans' (Nat.le_mul_of_pos_left _ (pow_pos two_pos _))
   obtain ⟨z,u,v,e⟩:= twice i w ht; let s:=Heat.gaugeShift K.B z; let M:= S.image ((plane i s).anon N)∪S; let y:= reflMark i s x*x
   have hz: AtSupport false M y:= ((q.refl i s).mono subset_union_left).mulM (q.mono subset_union_right)
   obtain ⟨Y,T,a,b,j,t⟩:= ih (d:=2*d+addgap K) (by rw [pow_succ] at h; exact h.trans' (le_of_eq (by ring))) v (apt_paired i s u p) hz
   simp_rw [pow_succ' 2 k,pow_mul]; have hy:‖X x‖^2 ≤ ‖X y‖:= G.twiceX i z (q.mono u)
   exact ⟨Y,T,(pow_le_pow_left₀ (sq_nonneg _) hy (2^k)).trans a, b, j, fun i' h v f=> t i' h v (e i' h v f)⟩ -- typo

lemma foil (R:Finset Axis)(k:ℕ){d:ℕ}(h:2^k*(d+addgap K) ≤ (N).val){S:Support (More N)}(w:∀ i∈ R,rest K m S i d)
    {x:Mark N}{c:ℝ}(p:Apt r c S x)(q:AtSupport false S x):
    ∃ (y:Mark N)(T:Support (More N)),‖X x‖^((2^k:ℕ)^R.card) ≤ ‖X y‖ ∧ Apt r (c^((2^k:ℕ)^R.card)) T y ∧ AtSupport false T y:=by
 induction R using Finset.induction_on generalizing S x c with
 | empty=> exact ⟨x,S,by simp,by simpa using p,q⟩
 | @insert i R v ih=>
   obtain ⟨y,T,a,b,z,e⟩:=stem G i k h (w _ (mem_insert_self _ _)) p q
   obtain ⟨Y,M,u,d,g⟩:= ih (S:=T) (fun j p=>e j (fun V=>v (V ▸ p)) _ (w j (mem_insert_of_mem p))) b z
   rw [card_insert_of_notMem v,pow_succ']; simp only [pow_mul]; exact ⟨Y,M,(pow_le_pow_left₀ (pow_nonneg (norm_nonneg _) _) a _).trans u,d,g⟩

-- choose large extent util. or if period is too small, straight from global bill.
omit G in
private lemma indexer {x y:ℕ} (p:0<y) (t:y ≤ x): ∃ k:ℕ, 2^k*y ≤ x ∧ x ≤ 2*(2^k)*y := by
  have he : x < 2^x*y:= lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.le_mul_of_pos_right _ p)
  let P(k:ℕ):= x ≤ 2*(2^k)*y
  have ht: ∃ k,P k:=⟨x,by unfold P; linarith⟩
  refine ⟨Nat.find ht,?_,Nat.find_spec ht⟩
  generalize e:Nat.find ht=k
  cases k with
  | zero=> simpa using t
  | succ k=> have h:=Nat.find_min ht (by omega : k < Nat.find ht); change ¬ x ≤ 2*2^k*y at h; rw [pow_succ']; omega

variable (T:Gross (K:=K) m X r C)
def magnified (K: Calibration)(C:ℝ)(d:ℕ):ℝ:= Real.exp (C*((2*(d+addgap K):ℕ):ℝ)^4)
include T
theorem shelter {d:ℕ}{S:Support (More N)} (w:∀ i,rest K m S i d){f:Mark N}{c:ℝ}(p:Apt r c S f)(s:AtSupport false S f):
    ‖X f‖ ≤ c*magnified K C d:= by
 let Q:=d+addgap K; have hC:= T.posC; by_cases h:Q ≤ (N).val
 · obtain ⟨k,t,e⟩:= indexer (lt_of_lt_of_le addgap_pos (Nat.le_add_left (addgap K) d)) h
   let J:ℕ:= (2^k)^4
   have hd: (univ:Finset Axis).card=4 := card_fin 4
   obtain ⟨y,T',a,b,z⟩:=foil G univ k t (fun i _=>w i) p s; rw [hd] at a b
   have hv: m.val^4 ≤ J*(2*Q)^4:=by
     unfold J; rw [←mul_pow]; refine pow_le_pow_left' ?_ _
     exact (side_lower K).trans (e.trans_eq (by ring))
   unfold magnified; apply (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (apt_pos p) (Real.exp_pos _).le) (n:=J) (by unfold J; positivity)).mp
   rw [mul_pow,←Real.exp_nat_mul]; refine a.trans ((T.budget b z).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (pow_nonneg (apt_pos p) J)))
   have hu:(m.val:ℝ)^4 ≤ J*((2*Q:ℕ):ℝ)^4:=by exact_mod_cast hv
   calc _ ≤ C*(J*((2*Q:ℕ):ℝ)^4):=mul_le_mul_of_nonneg_left hu hC
        _=_:=by unfold Q; ring
 refine (T.budget p s).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (apt_pos p))
 refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr ((side_lower K).trans ?_)) _) hC
 unfold Q at h; omega
end YM.CF.Buffered.Reliance
#print axioms YM.CF.Buffered.Reliance.shelter
