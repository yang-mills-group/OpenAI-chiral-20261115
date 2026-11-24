import YM.SU5.Selected.Conveyance
import Mathlib.Order.Filter.Curry
/-!
# Infinitesimal smearing of positions, for checking C-projected costs of ORDERED lists
(with multiple orders).
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.SelectionAnalysis
open Function Set Filter Metric MeasureTheory
open CF.Buffered.Afterglow.Tower MeshClock Germ Vacancy
open scoped Topology InnerProductSpace NNReal ENNReal
variable {H:Hilbert} (M:Mesh)
namespace Filming
noncomputable def horizon : Filter (ℕ×ℕ) := (Filter.atTop (α:=ℕ)).curry Filter.atTop
lemma horizon_iff {p:(ℕ×ℕ)→Prop} : (∀ᶠ x in horizon, p x) ↔ ∀ᶠ x:ℕ in atTop,∀ᶠ y:ℕ in atTop,p (x,y):= Filter.eventually_curry_iff
instance horizon_neBot : Filter.NeBot horizon := by
 refine ⟨fun h=>?_⟩; have ht : ∀ᶠ x in horizon, False:= by rw [h]; simp
 obtain ⟨i,x⟩:= (horizon_iff.mp ht).exists; exact x.exists.elim fun _=> _root_.id
local notation "Γ"=> marks M
local notation "U"=> ℕ×ℕ
abbrev Cell (s : ℕ×ℕ) := Fin (M.L^s.2)
noncomputable def pebbles (u:U)(s:Cell M u): marks M:= notch M (u.1+u.2) (s.val:ℤ)
lemma crumbs(v:U)(s:Cell M v): |(pebbles M v s:ℝ)| ≤ ((mill M v.1):ℝ):=by
 obtain ⟨i,j⟩:=v; let E:= mill M i; have ht:whenly M (i+j) (M.L^j)=E:=by
    rw [whenly,Nat.cast_pow]; have t:=mill_finer M i (i+j) (by omega); rwa [show i+j-i=j by omega] at t
 change |bell M (i+j) (s.val:ℤ)| ≤ (E:ℝ); rw [natural_time,abs_of_nonneg (whenly M (i+j) _).property]; exact NNReal.coe_le_coe.mpr (((when_le M _ _ _).mpr s.isLt.le).trans_eq ht)
lemma crumbs_vanish {ε:ℝ} (e:0<ε) : ∀ᶠ v in horizon,∀ t:Cell M v,|(pebbles M v t:ℝ)| < ε:=by
 rw [horizon_iff]; have hp: Tendsto (fun i:ℕ=> (mill M i:ℝ)) atTop (𝓝 0):= NNReal.tendsto_coe.mpr (vanishes M)
 filter_upwards [hp.eventually (gt_mem_nhds e)] with i hi; exact Eventually.of_forall fun v k=> (crumbs M (i,v) k).trans_lt hi
noncomputable def fragment (v:U) (f : Cell M v → H) : H:= Average.center f -- maybe unused
lemma composed {δ :Type*}[TopologicalSpace δ] [RegularSpace δ] {f : (ℕ×ℕ)→δ} {g : ℕ→δ} {y:δ}(h:Tendsto g atTop (𝓝 y))(p:∀ (n:ℕ), Tendsto (fun i=> f (n,i)) atTop (𝓝 (g n))): Tendsto f horizon (𝓝 y):=by
 apply tendsto_def.mpr; intro s hs; obtain ⟨u,hu,x,hq⟩:= mem_nhds_iff.mp hs
 exact h.eventually (x.mem_nhds hq) |>.mono fun n hn=> (p n).eventually (mem_of_superset (x.mem_nhds (show g n∈u from hn)) hu)
variable (P:Players (marks M) H)
local notation "A" W:max v:max j:max=> ((P.play (pebbles M v j)).comp W).comp (P.play (-pebbles M v j))
noncomputable def displaced (W:H.Op)(v:U) : H.Op:= Average.center (fun j:Cell M v=> A W v j)
lemma displaces (W:H.Op) (v:U)(x:H): displaced M P W v x= Average.center (fun j:Cell M v=> (A W v j) x):= (Average.natural _ (ContinuousLinearMap.apply ℂ H.space x)).symm
lemma displace_unit (W:H.Op)(x:H)(v:U) : ‖displaced M P W v x‖≤ ‖W‖*‖x‖:=by
 rw [displaces]; haveI : Nonempty (Cell M v):= avg_lives M _; apply Average.norm_worth; intro i
 change ‖P.play _ (W (P.play _ x))‖≤ _; rw [P.wins]; exact (W.le_opNorm _).trans_eq (by rw [P.wins])
lemma disp_cost (W:H.Op) (v:U): ‖displaced M P W v‖≤ ‖W‖:= ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun _=> displace_unit ..)
lemma transported (W:H.Op)(x:H)(p:x∈ P.lives H): Tendsto (fun v:ℕ×ℕ=> displaced M P W v x) horizon (𝓝 (P.pi_c (W x))):=by
 let V(v:U):H:= Average.center (fun i:Cell M v=> P.play (pebbles M v i) (W x)); have hv(v:ℕ×ℕ) : V v=average M P (v.1+v.2) v.2 (W x):= (avgvalue M P _ _ (W x)).symm
 let G(v:ℕ):H:= roller M P v (W x); have ht:Tendsto V horizon (𝓝 (P.pi_c (W x))) := composed (rollers M P (W x)) (fun n=> (rolls M P n (W x)).congr fun i=> (hv (n,i)).symm)
 apply Metric.tendsto_nhds.mpr; intro ε e
 let b:= ‖W‖+1; let d:= ε/2/b; obtain ⟨δ,i,h⟩:= P.living.mp p d (by unfold d b; positivity)
 filter_upwards [crumbs_vanish M i,Metric.tendsto_nhds.mp ht (ε/2) (by positivity)] with v w s
 refine lt_of_le_of_lt (dist_triangle _ (V v) _) ((add_lt_add_of_le_of_lt ?_ s).trans_le (le_of_eq (add_halves ε)))
 rw [displaces]; haveI:= avg_lives M v.2; apply Average.norm_dist; intro i'
 rw [ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,P.rigid H,dist_eq_norm,←map_sub]; apply (W.le_opNorm _).trans; rw [←dist_eq_norm]
 refine le_trans (mul_le_mul (show ‖W‖≤b from ?_) ((h _ (show |((-pebbles M v i':Γ):ℝ)| < δ from ?_)).le) dist_nonneg (show 0≤b from ?_)) ?_ -- le_show fake
 · unfold b; linarith
 · rw [AddSubgroup.coe_neg,abs_neg]; exact w i'
 · unfold b; positivity
 exact (by unfold d; field_simp [show 0<b by unfold b; positivity]; rw [div_self (by unfold b; positivity)]) -- inequality field_simp
-- use on projected vectors even if at right further multiplications
lemma transports (W:H.Op)(x:U→ H)(y:H)(t:Tendsto x horizon (𝓝 y))(p:y∈ P.lives H): Tendsto (fun v=> displaced M P W v (x v)) horizon (𝓝 (P.pi_c (W y))):=by
 apply tendsto_of_tendsto_of_dist (transported M P W y p); have h: Tendsto (fun v=> ‖W‖* dist y (x v)) horizon (𝓝 0):=by simpa using ((tendsto_const_nhds (x:=y)).dist t).const_mul ‖W‖
 refine squeeze_zero' (Eventually.of_forall fun _=> dist_nonneg) (Eventually.of_forall fun i=>?_) h
 rw [dist_eq_norm,←map_sub,dist_eq_norm]; apply displace_unit M P W _ _

-- combine requests whose k-direction movement is continuous at all zero displacement
section
variable {I:Type*}[Fintype I]
local notation "Λ" v:max=> (I→Cell M v)
local notation "S" v:max u:max=> show I→ Γ from fun i=> pebbles M v (u i)
lemma crumbs_pi (s:Set (I→ Γ))(p:s∈𝓝 (0:(I→Γ))): ∀ᶠ v in horizon,∀ u:Λ v,(fun i=> pebbles M v (u i))∈s:= by
 obtain ⟨ε,e,q⟩:= Metric.mem_nhds_iff.mp p; filter_upwards [crumbs_vanish M e] with v h u
 apply q (Metric.mem_ball.mpr ((dist_pi_lt_iff e).mpr (fun i=>?_))); change dist (pebbles M v (u i):ℝ) 0<_; rw [Real.dist_eq,sub_zero]; exact h _
lemma crumbs_limit [DecidableEq I] {V: Type*} [NormedAddCommGroup V][NormedSpace ℂ V] (f : (I→Γ)→ V)(p: ContinuousAt f 0): Tendsto (fun i=> Average.center (fun u:Λ i=> f (S i u))) horizon (𝓝 (f 0)):=by
 classical
 refine Metric.tendsto_nhds.mpr (fun ε h=> ?_); filter_upwards [crumbs_pi M {v|dist (f v) (f 0)<ε/2} (show _ from (Metric.tendsto_nhds.mp p (ε/2) (by positivity)))] with i hi -- need set explicit
 haveI := avg_lives M i.2; have hv (u:Λ i) := hi u;
 apply lt_of_le_of_lt _ (half_lt_self h); nth_rw 1 [← Average.constant («A»:=Λ i) (f 0)]
 apply Average.norm_dist; intro u; exact (show dist (f _) (f 0) <_ from hv u).le
end
end Filming
end YM.SelectionAnalysis
#print axioms YM.SelectionAnalysis.Filming.transports
#print axioms YM.SelectionAnalysis.Filming.crumbs_limit
