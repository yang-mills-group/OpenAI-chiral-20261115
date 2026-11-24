import YM.SU5.May.FloeVote
import YM.SU5.May.FloePencil
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 30000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.May.Floe
open Function Filter Finset Fir Lattice Laurent Next.Free Bloch Lat Ember Jill Rush
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Onyx Fock SU Flare Kea Sods Emu Dial Cube Tulip Spire Scroll Thera
open Fock Reflect
open Lamour (lakeP lakeK)
open Hygrometry Personality PriceCliff
open Stationary (Gaia cartWeight)
open Buffered.Lifted Buffered.Afterglow.Tower.Tilted
variable {j:ℕ} {N:Side} (s t:Personality)
def cake (j:ℕ)(N: Side)(x y: Cover):ℂ:= expected (fun c:Trace j N=>expected fun d:Trace j N=>poster (nature N x c) (nature N y d) s t)
lemma cake_shift (x y z:Cover)(p:Odd N.val): cake s t j N (x+z) (y+z)=cake s t j N x y:=by
 have he (x:Cover)(c:Trace j N) : nature N (x+z) c=nature N x c + riseX 1 z:= by
    apply PiLp.ext; intro i; change nature N (x+z) c i= nature N x c i +(z i:ℝ)/1
    rw [natural_stamp _ p c i,natural_stamp _ p c i]; change (((↑(x i+z i):ℝ)+1/2)+_)=_; push_cast; ring
 unfold cake; simp_rw [he,posted_shift]
lemma cake_squall (P:Ramp)(x y:Cover)(p:Odd N.val): cake s t j N ((whisper P).cell x) y=
 expected (fun c:Trace j N=>expected fun d:Trace j N=>poster (land_tilt P (nature N x c)) (nature N y d) s t):=by
 unfold cake; rw [←expected_reprice (reflected (N:=N) P j)]; simp_rw [Function.comp_def,nature,←reflect_chart p]; simp_rw [here_tilts] -- args

variable {D F:ℕ→Side}(G:∀ i,Ratio (D i) (F i))(p:1 ≤ j)
structure Twilight (j:ℕ)(G:∀ i,Ratio (D i) (F i)):Prop where
 orientation(i:ℕ): Even (D i).val
 coordinates(i:ℕ): Odd (G i).count.val
 cpu: Tendsto (fun i:ℕ=>(D i).val) atTop atTop
 yards:Yard F fun i=> (↑(G i).count.val:ℝ)
 seasonal: ∃ q:∀ i, Wave (Single (F i)),∀ᶠ i in atTop, Sea (latPose j white (F i)) (q i)
variable {ε:ℝ}(e:0<ε)(u:Twilight j G)(P:Ramp)(x y:Cover)
local notation "Q" i:max=> hail _ (u.coordinates i)
local notation "R" i:max=> (G i).count.val
local notation "S" i:max => Trace j ((G i).count)
local notation "X" i:max k:max c:max => point ((G i).count) k (traces _ j c)
local notation "δ" i:max x:max y:max=> ice j (D i) (Q i) 1 x y s t
local notation "ℬ" i:max x:max y:max => cake s t j ((G i).count) x y
include u p e
lemma perTest (h:Gap P j (x-y)) : ∀ᶠ i in atTop, ‖(δ i x y)-(ℬ i x y)‖ ≤ ε:=by
 obtain ⟨q,a⟩:= u.seasonal; filter_upwards [polls q u.yards p s t (fun _=>rfl) u.coordinates a P x y ε e h] with i h
 rw [person_coarse p x y (G i) (u.coordinates i) (u.orientation i) (u.yards.even i) s t]; unfold cake; apply expected_diff_le; intro k; exact expected_diff_le _ _ _ (fun j'=> (h k j').le)
omit u p e in
private lemma box_mono_c {n k:ℕ}(p:k ≤ n): Lattice.box k ⊆ Lattice.box n:=by intro x h; rw [box_test] at *; obtain ⟨v,t⟩:=h; constructor; intro i; specialize v i; omega; intro i; specialize t i; omega
-- above includes u p overshadow. tune
lemma receipt : ∀ᶠ i in atTop,∀ (x y:Cover), Smallish (D i) (x-y)→Gap P j (x-y)→ ‖(δ i x y)-(ℬ i x y)‖ ≤ ε :=by
 obtain ⟨n,k,H⟩:= fare_far p s t (ε/2) (half_pos e); obtain ⟨m,h⟩:=all_poster (j:=j) s t (ε/2) (half_pos e); let A:=Lattice.box (max k m);
 have ht: ∀ᶠ i:ℕ in atTop,∀ x∈ A, Gap P j x → ‖(δ i x 0)-(ℬ i x 0)‖≤ ε:=(A.eventually_all).mpr fun v _=> by
    by_cases hs:Gap P j v; · exact (perTest s t G p (ε:=ε) e u P v 0 (by rwa [sub_zero])).mono fun i e _=> e
    exact Eventually.of_forall fun _ h=> False.elim (hs h)
 obtain ⟨l,g⟩:= gave j p
 filter_upwards [ht,u.cpu.eventually_ge_atTop l,u.cpu.eventually_ge_atTop n] with i t' f d x y K z; by_cases n' : x-y∈ A
 · specialize t' (x-y) n' z; rw [ice_shift x y (-y) p (u.orientation i) _ _ _ _ zero_le_one,←cake_shift s t x y (-y) (u.coordinates i),add_neg_cancel]; exact t'
 have hm:=H _ (g _ (u.orientation i) f) d x y K (fun b=> n' (box_mono_c (le_max_left ..) b)) (Q i)
 have H : ‖ℬ i x y‖ ≤ ε/2:=by
    unfold cake; set tT:= ε/2
    have hQ(c: S i)(d:S i) : ‖poster (nature ((G i).count) x c) (nature ((G i).count) y d) s t‖≤ tT:= h x y (fun v=>n' (box_mono_c (le_max_right ..) v)) _ (u.coordinates i) c d
    have he {α:Type}[Fintype α][Nonempty α](f:α→ℂ)(p:∀ i,‖f i‖≤tT):‖expected f‖≤tT:=by simpa using expected_diff_le f (fun _=>0) tT (fun i=>by simpa using p i)
    apply he (α:=S i); exact fun k=>he (α:=S i) _ (hQ k)
 exact (norm_sub_le ..).trans ((add_le_add hm.le H).trans_eq (add_halves _))
end YM.CF.May.Floe
#print axioms YM.CF.May.Floe.receipt
#print axioms YM.CF.May.Floe.cake_squall
