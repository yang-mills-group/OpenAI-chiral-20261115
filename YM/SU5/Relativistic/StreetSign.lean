import YM.SU5.Relativistic.Boulevards
import YM.SU5.Selected.Undouble
/-! Stemmed energy for real time; sync actual book. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option maxHeartbeats 320000
noncomputable section
namespace YM.HostLegal
open CF.Buffered.Afterglow.Tower.MeshClock
open Function Filter Metric NormedSpace Finset MeasureTheory Set
open scoped Topology MatrixOrder InnerProductSpace ComplexOrder NNReal Classical
variable {X:Type} [AddCommGroup X][Module ℂ X](T:Tier X) (M:Mesh)
structure Ride where
 flow (i:ℕ): X →ₗ[ℂ] X
 source(x:X): flow 0 x=x
 compose(i j:ℕ)(x:X):flow i (flow j x)=flow (i+j) x
 ascent(s n k:ℕ)(h:s≤n)(x): T.cl s n (flow k x)=flow (acts M s n k) (T.cl s n x)
 paid (s n:ℕ)(x): ‖T.F s (flow n x) (flow n x)‖≤ ‖T.F s x x‖
 symmetry (s n:ℕ)(x y): T.F s (flow n x) y=T.F s x (flow n y)
 proper (s n:ℕ)(x):0≤ T.F s x (flow n x)
 possible (s:ℕ)(x):∃ (t:ℕ),s≤t ∧ ∃ y,flow 2 y=T.cl s t x

lemma payBasis(s:ℕ)(x:X):‖T.F s x x‖= ‖T.entry s x‖^2:=by rw [← T.arrived,inner_self_eq_norm_sq_to_K,norm_pow]; simp

def duplex (M:Mesh): Mesh:= { M with base:=2*M.base, baseP:=mul_pos (by norm_num) M.baseP }
lemma match_watch (s i:ℕ): whenly (duplex M) s i=2* whenly M s i:=by
 unfold whenly mill duplex; simp only; ring

variable {T M}
namespace Ride
variable (R:Ride T M)
include R
local notation "A" s:max=>T.entry s
lemma running_cost (s n:ℕ) (x) : ‖(A s) (R.flow n x)‖ ≤ ‖(A s) x‖:=by
 have ht:=R.paid s n x; rw [payBasis,payBasis] at ht; nlinarith [norm_nonneg (T.entry s x)]

noncomputable def itins(s n:ℕ): T.Lamination s where
 mover k:=R.flow (acts M s k n)
 weak k p v:=R.running_cost k _ v
 roll k t v w x:=by rw [R.ascent k t _ w,finer M _ _ _ _ v w]
noncomputable def fare(s n:ℕ): T.booth.Op:=(T.choose_ext s (R.itins s n)).choose
lemma rides(s n k:ℕ)(v:s ≤ k) (x): R.fare s n ((A k) x)=(A k) (R.flow (acts M s k n) x):=(T.choose_ext s (R.itins s n)).choose_spec.2 k v x
lemma site(s n:ℕ)(x): R.fare s n ((A s) x)=(A s) (R.flow n x):=by rw [R.rides s n s (le_refl _),same]
lemma price(s n:ℕ): ‖R.fare s n‖≤1:=(T.choose_ext s (R.itins s n)).choose_spec.1
lemma adds(s i j:ℕ): (R.fare s i)*(R.fare s j)= R.fare s (i+j):=by
 refine T.by_front s (D:=T.booth) (fun k v x=>?_); rw [ContinuousLinearMap.mul_apply,R.rides s _ _ v,R.rides s _ _ v,R.rides s _ _ v, R.compose, CF.Buffered.Afterglow.Tower.MeshClock.adds]
lemma base_(s:ℕ): R.fare s 0=1:=by
 refine T.by_front s (D:=T.booth) (fun k v x=>?_); rw [R.rides s _ _ v,acts,mul_zero,R.source]; rfl
lemma jointly (s t i:ℕ)(h:s≤t): R.fare s i=R.fare t (acts M s t i):=by
 refine T.by_front t (D:=T.booth) (fun k v x=>?_); rw [R.rides _ _ _ v,R.rides _ _ _ (h.trans v), finer M _ _ _ _ h v]
lemma self (s i:ℕ): (R.fare s i).adjoint= R.fare s i:=by
 refine T.by_front s (D:=T.booth) (fun t v x=>?_); apply T.see_late t; intro k p y; rw [←T.increase p,ContinuousLinearMap.adjoint_inner_right, R.rides s _ _ (v.trans p), R.rides s _ _ (v.trans p),T.arrived,T.arrived]; exact R.symmetry ..
lemma fare_ok(s i:ℕ): 0≤ R.fare s i := by
 apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
 let U:=R.fare s i
 change U.IsPositive; rw [ContinuousLinearMap.isPositive_iff']; refine ⟨R.self s i,fun x=>?_⟩
 rw [← show U.adjoint=U from R.self s i,ContinuousLinearMap.adjoint_inner_left] -- U let
 change 0≤ inner ℂ x (U x)
 refine closure_minimal (s:=⋃ r:ℕ,Set.range (T.entry r)) (t:={x|0 ≤ inner ℂ x (U x)}) ?_ (isClosed_le (f:=fun _=> (0:ℂ)) continuous_const (continuous_id.inner U.continuous)) (T.front x)
 intro x₁ e; obtain ⟨t,v⟩:=mem_iUnion.mp e; obtain ⟨v,rfl⟩:=v
 let k:=max s t; have h:t≤ k:=le_max_right ..; have w:s≤k:=le_max_left ..; change 0 ≤ inner ℂ ((A t) v) (U ((A t) v)); unfold U; rw [← T.increase h,R.rides _ _ _ w,T.arrived]; exact R.proper ..
noncomputable def mapGrid: Many (duplex M) T.booth where
 move:=R.fare
 small:=R.price
 source:=R.base_
 add:=R.adds
 refines:=R.jointly
 close:=R.self
 early:=by
    refine T.front.mono ?_; intro x p; obtain ⟨s,t⟩:= mem_iUnion.mp p; obtain ⟨v,rfl⟩:= t; obtain ⟨r,h,y,q⟩:= R.possible s v; exact mem_iUnion.mpr ⟨r,T.entry r y,(R.site ..).trans ((congrArg (T.entry r) q).trans (T.increase h v))⟩

lemma reaches (s i:ℕ): R.mapGrid.track (whenly M s i)= R.fare s i:=by
 let t:=whenly M s i
 let E:= R.mapGrid
 let Ux:=E.track t; have ht:E.track t * E.track t=R.fare s (i+i):=by
    change (E.track _).comp (E.track _)= _; rw [E.track_times,← two_mul,show 2*t=whenly (duplex M) s i from (match_watch M s i).symm,E.track_even]; unfold Many.double; rw [two_mul]; rfl
 have hp: 0 ≤ Ux:=by
    let k:=E.track (t/2)
    have hf:E.track (t/2)*(E.track (t/2))=E.track t:= by change (E.track _).comp (E.track _)=_; rw [E.track_times,add_halves]
    rw [show Ux=star k*k from (by rw [show star k=k from E.track_adjoint _]; exact hf.symm)]; exact star_mul_self_nonneg _
 exact (CFC.sqrt_unique ht hp).symm.trans (CFC.sqrt_unique (R.adds s i i) (R.fare_ok s i))
end Ride
end YM.HostLegal
#print axioms YM.HostLegal.Ride.reaches
