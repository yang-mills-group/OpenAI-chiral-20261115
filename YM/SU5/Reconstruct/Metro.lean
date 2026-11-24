import YM.SU5.Reconstruct.Tresh
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option maxRecDepth 4000
set_option quotPrecheck false
noncomputable section
namespace YM.SelectionAnalysis.Regularizing
open Function Set Filter Metric MeasureTheory Measure InnerProductSpace
open CF.Buffered.Afterglow.Tower MeshClock Germ Vacancy Vacancy.Average Sunbelt Spectral OS Analysis Semigroup Reconstruction
open scoped Topology InnerProductSpace NNReal ENNReal
variable {A : Hilbert}(M : Mesh) {j:Axis}(B: Sunbelt j (marks M) A) (S : OS.Semigroup A j)
local notation "K"=> B.track.aviator B.list
local notation "T"=> B.track.Realm B.list
local notation "P₀"=> (K).orthogonalProjectionOnto
local notation "Ψ"=> B.plane
variable (h : B.heat = S.E)
/-! # continuity for all positions in compass plus complete overlaps buy raw in mesh.
 Vary a single direction before using others. Use operator NORM for
 continuity of heat away from boundary; contact NOT purchased. -/
variable {P D : Type}
local notation "V₀"=> SceneGrid M
local notation "R₀"=> Axis → ℝ
local notation "Ω"=> plain M
variable (x:A)
variable (a b:P→ SceneGrid M)(X:P→A.Op)
variable (z:P→Axis→ℝ)(e:Axis→ℝ)(t:List P)
local notation "Φ" z:max=> parkFilm a b z X Ψ x
include h
lemma film_cost (v:P→SceneGrid M)(u:SceneGrid M) : ‖parkFilm a b v X B.plane x t u‖≤ (t.map fun i=>‖X i‖).prod*‖x‖:=by induction t generalizing u with
| nil=> simp only [List.map_nil,List.prod_nil,one_mul]; exact le_refl _
| cons i t ih=>
   rw [film_step]; simp only [List.map_cons,List.prod_cons,mul_assoc]; exact (plane_cost M B S h ..).trans (((X i).le_opNorm _).trans (mul_le_mul_of_nonneg_left (ih _) (norm_nonneg _))) -- .. syntax
variable (L:Filter D)
lemma film_axis_for (u u': D→SceneGrid M)(p:Tendsto (fun i=> plain M (u i) j) L (𝓝 (e j)))(q:Tendsto (fun i=> plain M (u' i) j) L (𝓝 (e j)))(hx: 0<e j) (r:∀ n, ∀ k : Axis,k≠j→ u n k =u' n k) :
    Tendsto (fun n=> ‖B.plane (u n)-B.plane (u' n)‖) L (𝓝 0) := by
 let E(w: D→SceneGrid M)(n):=S.E (Real.toNNReal (plain M (w n) j))
 have hL(w:D→SceneGrid M)(h:Tendsto (fun i=> plain M (w i) j) L (𝓝 (e j))):Tendsto (E w) L (𝓝 (S.E ((e j).toNNReal))) := (norm_cont_area S (Real.toNNReal_pos.mpr hx)).tendsto.comp ((continuous_real_toNNReal.tendsto _).comp h)
 have hp:Tendsto (fun n=> ‖E u n-E u' n‖) L (𝓝 0):=by simpa only [sub_self,norm_zero] using ((hL u p).sub (hL u' q)).norm
 apply squeeze_zero' (Eventually.of_forall fun _=> norm_nonneg _) ?_ hp
 refine Eventually.of_forall fun i=> ?_
 let V:= B.track.raw B.list (fun k=> u i k.val)
 let U:= B.track.raw B.list (fun k=> u' i k.val)
 have ht: U=V:= congrArg (B.track.raw B.list) (funext fun k=> (r i k.val k.property).symm)
 unfold Sunbelt.plane; rw [h]; change ‖(E u i).comp V- (E u' i).comp U‖ ≤ _; rw [ht]; change ‖(E u i).comp V- (E u' i).comp V‖ ≤ _
 rw [←ContinuousLinearMap.sub_comp]; exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y=> by rw [one_mul]; exact raw_below M B.track B.list _ y))

-- Ordered kernel price with two variations having same spatial shifts.
local notation "s₀" i:max=> ((plain M (a i)+z i):R₀)
local notation "b₀" i:max=> ((plain M (a i)+plain M (b i)+z i):Axis→ℝ)
def OrderedP:= t.Pairwise (fun i k=> (plain M (a i)+plain M (b i)+z i) j < (plain M (a k)+z k) j)
lemma film_axis (v v': D→P→SceneGrid M)(u u':D→SceneGrid M)
   (p:∀ i,Tendsto (fun n=>plain M (v n i)) L (𝓝 (z i)))(p':∀ i,Tendsto (fun n=>plain M (v' n i)) L (𝓝 (z i)))
   (q:Tendsto (fun i=>plain M (u i)) L (𝓝 e))(q':Tendsto (fun i=> plain M (u' i)) L (𝓝 e))
   (r:∀ i n,∀ k:Axis,k≠ j→ v n i k=v' n i k)(r':∀ n,∀ k:Axis,k≠j → u n k=u' n k)
   (hy:∀ i∈ t,e j < (plain M (a i)+z i) j)
   (g : OrderedP M a b z t (j:=j)):
    Tendsto (fun n=> dist ((Φ (v n)) t (u n)) ((Φ (v' n)) t (u' n))) L (𝓝 0) := by
 induction t generalizing u u' e with
 | nil=>exact (by simp only [parkFilm,dist_self]; exact tendsto_const_nhds)
 | cons i t ih =>
   obtain ⟨α,β⟩:=List.pairwise_cons.mp g
   let A₀(y:D→P→SceneGrid M) (u:D→SceneGrid M)(n:D):= a i+ y n i-u n
   let s (y:D→P→SceneGrid M)(n:D) := a i+b i+y n i
   let m:= b₀ i
   let W(y:D→P→SceneGrid M) (n:D):= (Φ (y n)) t (s y n)
   have he(Z:D→P→SceneGrid M)(h:Tendsto (fun n=>plain M (Z n i)) L (𝓝 ((s₀ i)-Ω (a i)))):Tendsto (fun n=>plain M (s Z n)) L (𝓝 m):=by
     unfold s; simp_rw [map_add]; rw [add_sub_cancel_left] at h; exact tendsto_const_nhds.add h -- shadow
   have hT:Tendsto (fun n=>dist (W v n) (W v' n)) L (𝓝 0):=ih m (s v) (s v') (he v (by simpa only [add_sub_cancel_left] using p i)) (he v' (by simpa only [add_sub_cancel_left] using p' i)) (fun n k h=>by unfold s; simp only [Pi.add_apply,r i n k h]) α β
   let q₀(n:D):= A₀ v u n; let q₁(n:D):= A₀ v' u' n
   let e':Axis→ℝ:= (s₀ i)-e; have hp : 0 < e' j:=by unfold e'; exact sub_pos.mpr (hy i List.mem_cons_self)
   have hU:Tendsto (fun n=> ‖Ψ (q₀ n)-Ψ (q₁ n)‖) L (𝓝 0):= by
     refine film_axis_for M B S h e' L q₀ q₁ ?_ ?_ hp ?_
     rotate_left 2
     · intro n k hk; unfold q₀ q₁ A₀; simp only [Pi.sub_apply,Pi.add_apply,r i n k hk,r' n k hk]
     all_goals apply tendsto_pi_nhds.mp _ j; first | unfold q₀ A₀ | unfold q₁ A₀
               simp_rw [map_sub,map_add]; first|exact (tendsto_const_nhds.add (p i)).sub q|exact (tendsto_const_nhds.add (p' i)).sub q'
   let c := (t.map fun i=>‖X i‖).prod * ‖x‖
   simp_rw [film_step]
   have hW : Tendsto (fun n=> ‖X i‖*dist (W v n) (W v' n) + ‖Ψ (q₀ n)-Ψ (q₁ n)‖ * (‖X i‖*c)) L (𝓝 0):=by simpa using (hT.const_mul ‖X i‖).add (hU.mul_const (‖X i‖*c))
   apply squeeze_zero' (Eventually.of_forall fun _=>dist_nonneg) ?_ hW
   refine Eventually.of_forall fun n=> ?_; let a' := X i (W v' n)
   change dist (Ψ _ (X i (W v n))) (Ψ (q₁ n) a')≤ _
   apply le_trans (dist_triangle _ (Ψ (q₀ n) a') _)
   refine add_le_add ?_ ?_
   · unfold a'; rw [dist_eq_norm,←map_sub,←map_sub]; exact (plane_cost M B S h _ _).trans (((X i).le_opNorm _).trans_eq (by rw [dist_eq_norm]))
   rw [dist_eq_norm,←ContinuousLinearMap.sub_apply]; exact (ContinuousLinearMap.le_opNorm (_-_:A.Op) a').trans (mul_le_mul_of_nonneg_left (((X i).le_opNorm _).trans (mul_le_mul_of_nonneg_left (film_cost M B S h x a b X t _ _) (norm_nonneg _))) (norm_nonneg _)) -- unknown notation
end YM.SelectionAnalysis.Regularizing
