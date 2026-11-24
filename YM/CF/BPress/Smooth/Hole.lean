import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
Tool to implement the Lipschitz fillings used in the cube skeleton algorithm of B-gate and
B-marker. In Euclidean target spheres, use the missing point argument. Uniform on arbitrar(il)y
fine boundary mesh (even if only a subset of the bounding faces yet has values).
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Smooth
open Function Metric Filter Set Module MeasureTheory
open scoped Topology NNReal ENNReal ContDiff InnerProductSpace RealInnerProductSpace BoundedContinuousFunction
variable {M : Type} [MetricSpace M]
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma compact_positive {s : Set M} (hs : IsCompact s) (f : M → ℝ) (p : ContinuousOn f s)
    (h : ∀ x ∈ s, 0<f x) : ∃ c:ℝ, 0<c ∧ ∀ x∈s, c ≤ f x := by
  rcases s.eq_empty_or_nonempty with e|e
  · exact ⟨1,zero_lt_one,fun x hx=>(Set.notMem_empty _ (e ▸ hx)).elim⟩ -- tune
  obtain ⟨i,x,v⟩:= hs.exists_isMinOn e p; exact ⟨f i,h i x,fun x hx=>v hx⟩
lemma lip_near {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {s : Set V} (hs : IsCompact s) {f : V → W} (p : ∀ x∈s, ContDiffAt ℝ 1 f x) :
    ∃ K : ℝ≥0, LipschitzOnWith K f s := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hs; intro x hx; obtain ⟨K,t,h,P⟩:= (p x hx).exists_lipschitzOnWith; exact ⟨K,t,nhdsWithin_le_nhds h,P⟩

local notation "ballE" => sphere (0:E) 1
lemma stereo_domain {v w : E} (p : ‖v‖=1) (q : ‖w‖=1) (h : w ≠ v) : ContDiffAt ℝ 1 (stereoToFun v) w := by
  let s:= {x : E | innerSL ℝ v x ≠ (1:ℝ)}; refine contDiffOn_stereoToFun.contDiffAt (s:=s) ((isOpen_ne.preimage (innerSL ℝ v|>.continuous)).mem_nhds (show w∈s from ?_)); intro e; change ⟪v,w⟫=1 at e; apply h; apply sub_eq_zero.mp; apply norm_eq_zero.mp; have ht:= norm_sub_sq_real v w; rw [p,q,e,norm_sub_rev v w] at ht; nlinarith
lemma dim_sphere_le (v : E) (hv : ‖v‖=1) (n:ℕ) (p : finrank ℝ E = n+1) :
    (n:ℝ≥0∞) ≤ dimH ballE := by
  let Y := ballE\{v}; let f:=stereoToFun v
  haveI : Fact (finrank ℝ E = n+1):=⟨p⟩
  have hx : finrank ℝ (ℝ ∙ v)ᗮ=n:= Submodule.finrank_orthogonal_span_singleton (norm_ne_zero_iff.mp (hv.symm ▸ one_ne_zero))
  have he : dimH (f '' Y) ≤ dimH ballE:=by
    refine le_trans ?_ (dimH_mono (show Y⊆ballE from sdiff_subset)); apply dimH_image_le_of_locally_lipschitzOn; intro x p; obtain ⟨K,s,S,Y⟩:= (stereo_domain hv (show ‖x‖=1 by simpa using (show x∈ballE from p.1)) (show x≠v from p.2)).exists_lipschitzOnWith; exact ⟨K,s,nhdsWithin_le_nhds S,Y⟩
  rw [show f '' Y=univ from Set.eq_univ_of_forall fun w=>?_, Real.dimH_univ_eq_finrank, hx] at he; exact he
  refine ⟨(stereoInvFun hv w).val, ⟨(stereoInvFun hv w).property, fun t=> stereoInvFun_ne_north_pole hv w (Subtype.ext t)⟩, stereo_right_inv hv w⟩

/-- Ambient extensions of **partial** Lipschitz data, with uniform norm on a prescribed compact.
 Nonempty seed. -/
lemma ambient_ext {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A : Set M} (p : IsCompact A) (R : ℝ) (L : ℝ≥0) :
    ∃ (C : ℝ), ∀ S ⊆ A, S.Nonempty → ∀ f : M → E, LipschitzOnWith L f S → (∀ i∈S, ‖f i‖≤R) → ∃ g : M → E,
    LipschitzWith (lipschitzExtensionConstant E * L) g ∧ EqOn f g S ∧ ∀ i∈A, ‖g i‖ ≤ C := by
  let K:=lipschitzExtensionConstant E * L; refine ⟨ K * diam A + R, fun S hs ne f x p'=>?_ ⟩; obtain ⟨g,h,w⟩:= x.extend_finite_dimension
  obtain ⟨s,z⟩:=ne; refine ⟨g,h,w,fun i hi=>?_⟩; have he: ‖g i-g s‖ ≤ (K:ℝ)* diam A:= by
    rw [←dist_eq_norm]; exact (h.dist_le_mul ..).trans (mul_le_mul_of_nonneg_left (dist_le_diam_of_mem p.isBounded hi (hs z)) K.property)
  have hx:= p' s z; rw [w z] at hx -- tune
  exact (norm_le_norm_sub_add (g i) (g s)).trans (add_le_add he hx)
lemma avoidance (v : E) (hv : ‖v‖=1) (X : Set M) (p : IsCompact X) (L : ℝ≥0)
    {n:ℕ} (e : finrank ℝ E=n+1) (h : dimH X < n) :
    ∃ ε : ℝ, ∃ u : Finset (sphere (0:E) 1), 0<ε ∧ ∀ (S : Set M), S ⊆ X → S.Nonempty → ∀ (f : M→E),
    LipschitzOnWith L f S → (∀ x∈S, ‖f x‖=1) → ∃ i ∈ u, ∀ x∈S, ε ≤ dist (f x) i.val := by
  letI : CompactSpace X:= isCompact_iff_compactSpace.mp p; letI : ProperSpace E:=FiniteDimensional.proper ℝ _; let K:=lipschitzExtensionConstant E * L; obtain ⟨C,t⟩:= ambient_ext (E:=E) p 1 L
  let D := (↑X →ᵇ E); let T : Set D:= {f : ↑X →ᵇ E| LipschitzWith K f ∧ ∀ (i : X), f i ∈ closedBall 0 C}
  have he(dim: ↑X →ᵇ E)(q : dim ∈ T): ¬ ballE ⊆ Set.range dim := by
    intro r; apply h.not_ge; have hd:= (show LipschitzWith K dim from q.1).dimH_range_le
    have he:= isometry_subtype_coe (s:=X)|>.dimH_image univ; simp only [image_univ,Subtype.range_coe] at he
    exact (dim_sphere_le v hv n e).trans ((dimH_mono r).trans (hd.trans_eq he.symm))
  have hc : IsCompact T := by
    apply BoundedContinuousFunction.arzela_ascoli₂ (closedBall 0 C) (isCompact_closedBall ..) T _ (fun f x h=> h.2 x) ((LipschitzWith.uniformEquicontinuous (fun i:T=>⇑(show ↑X →ᵇ E from i.val)) K (fun i=>i.property.1)).equicontinuous)
    apply IsClosed.inter ((isClosed_setOf_lipschitzWith K).preimage (BoundedContinuousFunction.continuous_coe (α:=↑X) (β:=E))) _
    change IsClosed {f : ↑X →ᵇ E| ∀ (i : X), f i∈ closedBall 0 C}; simp_rw [setOf_forall]; exact isClosed_iInter fun i=> isClosed_closedBall.preimage (ContinuousEvalConst.continuous_eval_const i)
  -- every candidate function in the compact set has a witness hole. pick finitely many.
  have hp (i:T) : ∃ u : sphere (0:E) 1, ∃ ε : ℝ, 0<ε ∧ ∀ x : X, ε ≤ dist (i.val x) u.val:= by
    obtain ⟨z,l,k⟩:= Set.not_subset.mp (he i i.property)
    obtain ⟨ε,h,H⟩:= compact_positive isCompact_univ (fun x:X=> dist (i.val x) z) (i.val.continuous.dist continuous_const).continuousOn (fun x _=> dist_pos.mpr (fun e=> k ⟨x,e⟩)); exact ⟨⟨z,l⟩,ε,h,fun x=> H x (mem_univ x)⟩
  choose W r a F using hp
  obtain ⟨J,P⟩:= hc.elim_finite_subcover (fun i : T=>ball i.val (r i/2)) (fun _=> isOpen_ball) (fun i e=> mem_iUnion.mpr ⟨⟨i,e⟩, mem_ball_self (half_pos (a _))⟩)
  have hz : ∃ ε : ℝ, 0<ε ∧ ∀ i∈J, ε ≤ r i/2:= by
    rcases J.eq_empty_or_nonempty with e|e; · exact ⟨1,zero_lt_one,by simp [e]⟩
    exact ⟨J.inf' e (fun i=> r i/2),(Finset.lt_inf'_iff ..).mpr fun i _=> half_pos (a _),fun i hi=> Finset.inf'_le _ hi⟩
  classical
  obtain ⟨ε,b,g⟩:= hz; refine ⟨ε,J.image W,b,fun S l ne f a m=>?_⟩; obtain ⟨u,c',B,D⟩:= t S l ne f a (fun x hx=> (m x hx).le)
  let f' : ↑X → E:= fun i=> u i.val; have hf : LipschitzWith K f':= c'.restrict _
  let h := BoundedContinuousFunction.mkOfCompact ⟨f',hf.continuous⟩; obtain ⟨j,hj,q⟩:= mem_iUnion₂.mp (P (show h∈T from ⟨hf,fun i=> by rw [Metric.mem_closedBall,dist_zero_right]; exact D i.val i.property⟩)); refine ⟨W j,Finset.mem_image_of_mem _ hj,fun x hx=>?_⟩
  let k : X:=⟨x,l hx⟩; have he:= dist_triangle (j.val k) (h k) (W j).val; have hv: dist (j.val k) (h k)≤ r j/2:= by rw [dist_comm]; exact (BoundedContinuousFunction.dist_coe_le_dist _).trans (mem_ball.mp q).le
  rw [B hx]; change _ ≤ dist (h k) _; linarith [g j hj,F j k]
end YM.CF.BPress.Smooth
