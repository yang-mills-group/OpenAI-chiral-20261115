import YM.SU5.Reconstruction.Trap.LP
import YM.SU5.Reconstruction.Vermont.Harbor
/-! # New thermal momentum argument from arbitrarily far right observations, in one observer -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Lens
open Function Set Filter MeasureTheory Spectral Analysis OS.Semigroup ConePrice Sail BridgeClub Anvil ContinuousLinearMap
open scoped BigOperators Topology NNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}{a:Axis}(S:OS.Semigroup H a)(N:Submodule ℂ H) (q:IsClosed (N:Set H))
open Picket
local notation "E"=> S.E
local notation "U"=> trans S
local notation "mv"=> parcelUp S
variable {b:Axis}(u:b≠a)(C:ℝ) (X:Set ℝ)(dX:Dense X)(P:Forward S)
variable (L:H.Op)(x:H)

-- multi-arity Legion. Anchor constraints both ways thanks to cooling *both* legs
include u P dX q
lemma fromLocus (t s:ℝ≥0)(p:0<t)(v:0<s)(h:∀ y∈ X, C<y → S.E t (parcelUp S (y • basis b) L (S.E s x)) ∈ N) (y:ℝ) :
 S.E t (parcelUp S (y • basis b) L (S.E s x))∈ N:=by
 let γ:= Picket.cross a b u; have hz : ‖γ‖≤1:=le_of_eq (by change ‖basis b‖=1; simp); let R(z:ℂ):= Sail.transverse S P γ hz t p z; let T(z:ℂ):= Sail.transverse S P γ hz s v (-z)
 let F(z:ℂ):= (R z * L * T z) x; let e:= min (t:ℝ) (s:ℝ); have h' : 0<e:=lt_min p v
 have hf (y:ℝ): F y=S.E t (mv (y • basis b) L (S.E s x)):= by
   unfold F R T Sail.transverse; rw [on_strip S P γ hz t p,← Complex.ofReal_neg,on_strip S P γ hz s v]
   unfold parcelUp; rw [← neg_smul]; simp_rw [mul_apply_eq_comp, trans_space (h:=u)]; -- Transverse order
   apply DFunLike.congr_fun (S.independent _ _).symm
 have an: AnalyticOnNhd ℂ F (slit e):= by
   let hR:AnalyticOnNhd ℂ R (slit (t:ℝ)):= transverse_anal S P γ hz t p
   let hT(z:ℂ)(l:z∈ slit e) : AnalyticAt ℂ T z:= (transverse_anal S P γ hz s v (-z) (show -z∈ slit (s:ℝ) from (by rw [slit,mem_setOf_eq,Complex.neg_im,abs_neg]; exact lt_of_lt_of_le (show |z.im|<e from l) (min_le_right ..)))).comp (f:=fun z:ℂ=>-z) analyticAt_id.neg
   intro z vp; exact ((ContinuousLinearMap.apply ℂ H.space x).analyticAt _).comp (((hR z (lt_of_lt_of_le (show |z.im|<e from vp) (show e≤(t:ℝ) from min_le_left ..))).mul (analyticAt_const (v:=L))).mul (hT z vp))
 letI := q.completeSpace_coe
 let B:= N.starProjection
 have heq:AnalyticOnNhd ℂ (B ∘ F) (slit e):= fun i p=> (B.analyticAt _).comp (an i p)
 have ht: Continuous (fun i:ℝ=> F i):= an.continuousOn.comp_continuous Complex.continuous_ofReal (slit_ground e h')
 have hB: EqOn (fun i:ℝ=>B (F i)) (fun i:ℝ=>F i) (Ioi C):= (EqOn.closure (s:= Ioi C∩ X) (show EqOn (fun i:ℝ=> B (F i)) (fun i:ℝ=> F i) _ from (by rintro z ⟨p',v'⟩; apply Submodule.starProjection_eq_self_iff.mpr; rw[hf]; exact h z v' p')) (B.continuous.comp ht) ht).mono (dX.open_subset_closure_inter isOpen_Ioi)
 obtain ⟨s,d,u⟩:= exists_between (show C<C+1 by linarith)
 rw [← hf]; exact Submodule.starProjection_eq_self_iff.mp (pioneer (slit_connected _) (slit_ground _ h' s) _ _ ⟨d,u⟩ heq an (fun i d=> hB d.1) (slit_ground _ h' y)) -- args tune

open CF.Buffered.Afterglow.Tower CF.Buffered.Afterglow.Tower.MeshClock
variable (A:Mesh)
omit u q P dX in
lemma radiatory {W:Set ℝ≥0} (d:IsClosed W)(p:∀ t:marks A, 0<(t:ℝ)→ Real.toNNReal (t:ℝ) ∈ W) (x:ℝ≥0): x∈ W:= by
 refine d.mem_of_tendsto (shade A x) (Eventually.of_forall (fun i=>?_)); let k:= ⌊x/mill A i⌋₊+1; have hk: 0<whenly A i k:=when_pos _ _ _ (Nat.zero_lt_succ _); let y:=notch A i (k:ℤ); have hy:(y:ℝ)=(whenly A i k:ℝ):=natural_time ..
 have ht:=p y (by rw [hy]; exact (show 0<(whenly A i k:ℝ) from hk)); rw [hy,Real.toNNReal_coe] at ht; exact ht

include A in
lemma freeing (h:∀ y∈ X,C<y → ∀ (t s:ℝ≥0),0<t→ 0<s→ S.E t (parcelUp S (y • basis b) L (S.E s x)) ∈N): L x∈ N:=by
 have ht(t s:ℝ≥0)(p:0<t)(v:0<s): E t (L (E s x))∈ N:=by simpa only [zero_smul, parcel_zero] using fromLocus S N q u C X dX P L x t s p v (fun i d u=>h i d u _ _ p v) 0
 have hv(t:ℝ≥0)(p:0<t): E t (L x)∈ N:= by
   have hz:E t (L (E 0 x))∈N:=radiatory A (show IsClosed ((fun y=> E t (L (E y x))) ⁻¹' (N:Set H)) from q.preimage ((E t).continuous.comp (L.continuous.comp (S.continuousE x)))) (fun i v=> ht t _ p (Real.toNNReal_pos.mpr v)) 0; simpa only [S.eZero,id_apply] using hz
 have ha:E 0 (L x)∈N:= radiatory A (q.preimage (S.continuousE (L x))) (fun i v=> hv _ (Real.toNNReal_pos.mpr v)) 0; simpa only [S.eZero,id_apply] using ha

include q
omit u P dX in
lemma fromHeat (e:∀ t:ℝ≥0,E t x∈ N) (t:ℝ): trans S (t • basis a) x∈ N:= by
 letI:= q.completeSpace_coe; rw [trans_time, ← width_imaginary]; exact Submodule.starProjection_eq_self_iff.mp (Lens.patrol S N.starProjection 1 x (show (0:ℝ≥0)<1 from zero_lt_one) (fun t h v=> by rw [Submodule.starProjection_eq_self_iff.mpr (e t)]; rfl) _ (by rw [side]))
end YM.Lens
