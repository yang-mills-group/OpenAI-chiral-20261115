import YM.SU5.Relativistic.EnvelopSmear
/-!
# Point regression, operational on the indicated chart, not pointlike insertions.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Set Filter Metric MeasureTheory
open MeshClock Germ Vacancy _root_.YM.SelectionAnalysis Analysis
open scoped Topology Classical BigOperators NNReal ENNReal InnerProductSpace
variable {M : Mesh}

def nub (M:Mesh) (v:Axis→ Stamp M)(n:ℕ):Packet M:= ⟨n,v,(1:(Axis→ℝ)→ℂ),continuousOn_const⟩
local notation "A" n:max=> (Axis→ Fin (M.L^n))
local notation "U"=> Axis → Stamp M
local notation "W"=> Axis→ ℝ
local notation "π" u:max=> fun i:Axis=> ((u i:Stamp M):ℝ)
def Settler (g:ℕ→Packet M) (v:Axis→ℝ):Prop:=
    (∀ (ε:ℝ), 0<ε→ ∀ᶠ i in atTop,∀ u∈ UBox Axis, dist ((g i).region u) v < ε) ∧ ∀ i,(g i).weight=1
lemma adjusts (v:ℕ→ (Axis→Stamp M))(u:Axis→ℝ) (p:Tendsto (fun i=> (fun j:Axis=> ((v i j:Stamp M):ℝ))) atTop (𝓝 u)) : Settler (fun i=> nub M (v i) i) u := by
 refine ⟨?_,fun _=>rfl⟩; intro ε h
 let b:ℕ → (Axis→ℝ):= fun i => π (v i)
 have ht:Tendsto (fun i=> (mill M i:ℝ)) atTop (𝓝 0):=NNReal.tendsto_coe.mpr (vanishes M)
 filter_upwards [ht.eventually (gt_mem_nhds (half_pos h)),Metric.tendsto_nhds.mp p (ε/2) (half_pos h)] with i (k:(mill M i:ℝ)<ε/2) (hu:dist (b i) u<ε/2) x hx
 apply lt_of_le_of_lt (dist_triangle _ (b i) _)
 refine (add_lt_add_of_le_of_lt ?_ hu).trans_eq (add_halves _)
 apply le_trans ?_ k.le
 apply (dist_pi_le_iff (show 0≤(mill M i:ℝ) from (mill M i).property)).mpr; intro j
 change dist (b i j + x j*(mill M i:ℝ)) (b i j)≤_
 rw [Real.dist_eq,add_sub_cancel_left, abs_mul, abs_of_nonneg (show 0 ≤ x j from hx.1 j), abs_of_nonneg (show 0≤ (mill M i:ℝ) from (mill M i).property)]; exact mul_le_of_le_one_left (mill M i).property (hx.2 j)
lemma adjusts_mesh (v:Axis→Stamp M) : Settler (fun i=> nub M v i) (π v):= adjusts (fun _=>v) _ tendsto_const_nhds
lemma converge_approach (M:Mesh) (u:Axis→ℝ):∃ g: ℕ→ Axis→Stamp M,Tendsto (fun i=>fun j:Axis=> (g i j:ℝ)) atTop (𝓝 u) := by
 choose t h p using fun i:Axis=> mem_closure_iff_seq_limit.mp (MeshClock.daylight M (u i))
 exact ⟨fun n i=> ⟨t i n,h i n⟩,tendsto_pi_nhds.mpr fun i => p i⟩
lemma Settler.advances (M:Mesh) (u:Axis→ℝ):∃ g:ℕ→Packet M, Settler g u:=by
 obtain ⟨g,p⟩:= converge_approach M u; exact ⟨_,adjusts g u p⟩

-- strict padding of entire closed survey tile
abbrev safely (j:Axis) (S T:Slab M) (u:Axis→ℝ): Prop := (T.lower:ℝ) < (S.lower:ℝ)+u j ∧ (S.upper:ℝ)+u j<(T.upper:ℝ)
lemma safe_open (j:Axis) (S T:Slab M): IsOpen {u: W | safely j S T u}:= (isOpen_lt continuous_const (continuous_const.add (continuous_apply _))).inter (isOpen_lt (continuous_const.add (continuous_apply _)) continuous_const)
variable (j:Axis) (S T:Slab M) (g:ℕ→Packet M) (u:Axis→ℝ)
lemma safe_with (h:safely j S T u)(p:Settler g u) : ∀ᶠ i in atTop, ∀ v∈ UBox Axis,safely j S T ((g i).region v):=by
 obtain ⟨ε,x,t⟩:=Metric.isOpen_iff.mp (safe_open j S T) u h
 filter_upwards [p.1 ε x] with i hi v hv; exact t (hi v hv : dist _ u < ε)
section gate
variable {H:Hilbert} (P:Sunbelt j (marks M) H)(E:OS.Semigroup H j)
variable (e:∀ i,∀ (z : marks M) (t:ℝ≥0), ((P.track.crew i).play z).comp (E.E t)=(E.E t).comp ((P.track.crew i).play z))
local notation "L"=> P.track.Realm P.list
local notation "X"=> P.track.aviator P.list
local notation "G"=> glass P (daylight M) E e
variable (B:H.Op)
local notation "E₀" n:max => envelop P E e B S T (g n)
local notation "Φ" v:max u:max=> envelope P E e B S T u v
lemma not_far (p:Settler g u) (i:ℕ) : ‖E₀ i‖ ≤ ‖B‖:=by
 apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _); intro x
 have hq: ‖(E₀ i) x‖ ≤ 1*‖B‖*‖x‖:=by
    apply assembled_cost P E e B S T (g i) x
    intro t y; unfold Packet.score; rw [p.2 i]; simp
 rwa [one_mul] at hq
lemma collecting_point (p:Settler g u) (x:L) : Tendsto (fun i=> (E₀ i) x) atTop (𝓝 (envelope P E e B S T u x)) := by
 apply Metric.tendsto_nhds.mpr; intro ε v
 let f(v:Axis→ℝ):L:=envelope P E e B S T v x
 obtain ⟨δ,h,t⟩:= Metric.continuousAt_iff.mp (show ContinuousAt f u from (envelope_cont P E e B S T x).continuousAt) (ε/2) (half_pos v)
 filter_upwards [p.1 δ h] with i hi
 have hP(k:ℕ)(y: A k) : dist ((g i).score k y • (f ((g i).region (smallCorner _ y)))) (f u) ≤ ε/2 :=by
    unfold Packet.score; rw [p.2]; change dist ((1:ℂ)•_) _≤_; rw [one_smul]; exact (t (hi _ (Packet.lives (M:=M) k y))).le
 refine lt_of_le_of_lt ?_ (half_lt_self v)
 apply le_of_tendsto ((projected_collect P E e B S T (g i) x).dist tendsto_const_nhds)
 apply Eventually.of_forall; intro k
 haveI:=avg_lives M k; have hf:=Average.norm_dist (hP k); rw [Average.constant] at hf; exact hf
end gate
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.collecting_point
