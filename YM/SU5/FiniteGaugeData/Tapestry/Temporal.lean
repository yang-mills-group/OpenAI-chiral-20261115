import YM.SU5.FiniteGaugeData.Tapestry.Wardrobe
import YM.SU5.FiniteGaugeData.Tapestry.Fashion
import YM.Push.BETA_TRANSPORT.Block
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin Haro
attribute [local instance] opCStarAlgebra
open Pastry Tap Nacre Ember Pec
open Push.BetaTransport

/-!
# Every period. Continuity result at native level w.r.t. beta, wave

Uniform on Ward (operator norm). This suffices in any election where they are
arranged to converge (for the genuine participating steps) at each fixed level
and period. Don't infer that the gains of this particular estimate can pay
uniformly in the period!
-/
set_option quotPrecheck false
variable {N P:Side}

lemma weightTemporal (A:StepData (More N) (More P))(h:A.patch.Branches A.kernel SU.group)(W:Pane P)(V:Pane N){a b C:ℝ}(p:|a|≤ C)(q:|b|≤ C) :
   ‖A.density a W V-A.density b W V‖≤ noiseCap A*noiseCost A C*‖a-b‖:=by
  let X:= density_estimate A h
  apply (convex_Icc (-C) C).norm_image_sub_le_of_norm_hasDerivWithin_le (f:= (fun b=>A.density b W V)) (f':=fun β=> densitySlope A β W V) (fun x hx=> (density_hasDerivAt A x W V).hasDerivWithinAt) (fun x hx=> (X.slope x (W,V)).trans (mul_le_mul_of_nonneg_left (X.le (abs_le.mpr hx) (W,V)) (noiseCap_nonneg _))) (abs_le.mp q) (abs_le.mp p)
lemma temporalPrice (A:StepData (More N) (More P))(h:A.patch.Branches A.kernel SU.group)(z:ℝ) : ∀ ε:ℝ,0<ε→∀ᶠ u:ℝ in 𝓝 z,∀ W: Pane P,∀ V:Pane N,‖A.density u W V-A.density z W V‖≤ ε:=by
  intro ε e; let c:= noiseCap A* noiseCost A (|z|+1)
  have t : Tendsto (fun x:ℝ=> c * ‖x-z‖) (𝓝 z) (𝓝 0):= by convert (show Continuous (fun x:ℝ=> c * ‖x-z‖) from by fun_prop).continuousAt.tendsto (x:=z) using 1; simp -- tune
  filter_upwards [eventually_abs_bound z,t.eventually (gt_mem_nhds e)] with b u h' W V; exact (weightTemporal A h W V (show |b| ≤ _ from u) (le_add_of_nonneg_right zero_le_one)).trans (show c*‖b-z‖< ε from h').le
lemma canopyPrice (A:StepData (More N) (More P))(h:A.patch.Branches A.kernel SU.group)(z:ℝ): ∃ D:ℝ,0<D∧ ∀ᶠ u:ℝ in 𝓝 z,∀ W:Pane P,∀ V:Pane N, ‖A.density u W V‖ ≤ D:= ⟨noiseCost A (|z|+1),noiseCost_pos .., (Filter.eventually_iff.mpr (eventually_abs_bound z)).mono fun i p W V=> by rw [Real.norm_of_nonneg (StepData.density_positive ..)]; exact (density_bounds A h p W V).2 ⟩ -- tune

lemma frameFee (b: Bool): Continuous (fun x:Haro.SpaceM=> feeL b N x.val) := by
  have he: Continuous (fun x:Haro.SpaceM=> plankP N x.val):= by
    unfold plankP headW; let Z:=Fir.Aop-(1/2:ℂ) • 1; let G(i:SpaceM):Op (Model N):=jump (Equiv.refl _) (fun _=> Z ⊗ₖ i.val); have he:Continuous G:=by
       unfold G; apply continuous_matrix; intro a b; change Continuous fun i:SpaceM=> if a.1=b.1 then _ else _; split; swap; · exact continuous_const
       exact continuous_const.mul (continuous_subtype_val.matrix_elem _ _)
    exact (love N).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional.comp he
  letI : NormedAlgebra ℚ (Op (Single N)):=NormedAlgebra.restrictScalars ℚ ℂ _
  cases b
  · exact exp_continuous.comp he.neg
  exact exp_continuous.comp he

variable (G:Ratio N P)(j:ℕ)(M:Male)(ho: Odd G.count.val)
variable {R:ℕ}(p:LaurentRadius j G.count R)
include p
lemma frameMode (b:Bool)(v) : Continuous (fun x:Haro.SpaceM× Nom N P=> byMode G j x.1.val M x.2 b v):=by
  simp_rw [byMode_eq]
  refine LinearMap.continuous_of_finiteDimensional _|>.comp ((acts_cont.comp ((cloth_cont G j p M).comp continuous_snd)).clm_apply ?_)
  exact LinearMap.continuous_of_finiteDimensional _|>.comp ((acts_cont.comp ((frameFee (N:=N) b).comp continuous_fst)).clm_apply continuous_const)
lemma frameStroke (i:Single N): Continuous (fun x:Haro.SpaceM× Nom N P=> stroke G j x.1.val M x.2 i):= by
  unfold stroke; split
  · exact create_cont.comp (frameMode G j M p ..)
  exact (create_cont.comp (frameMode G j M p ..)).star
include ho
lemma frameString (u:Finset (Single N)): Continuous (fun x:Haro.SpaceM × Nom N P=> (stringS G j x.1.val M ho x.2).tag u):=by
  induction u using Finset.induction_on with
  | empty=> simp_rw [Poly.tag_void]; exact continuous_const
  | insert i s e ih=> simp_rw [Poly.tag_any _ _ _ e]; exact (continuous_const (y:=parity i s)).smul ((frameStroke G j M p _).mul ih)
variable (q:Chi)(d:ℝ) (a:0<d)(b:2*d<firstRadius SU.group)
omit p ho
-- helper: avoiding diamonds and metric on Fields
lemma holdingCompact {D Z T:Type*}[TopologicalSpace Z][TopologicalSpace D][NormedAddCommGroup T](f:D→Z→T)(h:Continuous (Function.uncurry f)) (x:D){S:Set Z}(s:IsCompact S) : ∀ ε:ℝ,0<ε→∀ᶠ y in 𝓝 x,∀ z∈ S, ‖f y z-f x z‖≤ ε:=by
  intro ε e
  obtain ⟨U,hU,v⟩:= s.mem_uniformity_of_prod h.continuousOn (Set.mem_univ x) (Metric.dist_mem_uniformity e)
  rw [nhdsWithin_univ] at hU
  filter_upwards [hU] with y h z w; exact le_of_lt (by rw [← dist_eq_norm]; exact v y h z w)
-- small lemmas, before plugging `Nom` and `FC`.
lemma subCompactBudget {D Z T:Type*}[TopologicalSpace Z][NormedAddCommGroup D][ProperSpace D][NormedAddCommGroup T][CompactSpace Z](f:Z→D→T)(h:Continuous (Function.uncurry f)): ∃ C:ℝ, 0<C ∧ ∀ z d,‖d‖ ≤1→ ‖f z d‖ ≤ C:=by
  let S:= Set.univ (α:=Z) ×ˢ Metric.closedBall (0:D) 1; obtain ⟨b,u⟩:= ((show IsCompact S from isCompact_univ.prod (isCompact_closedBall ..)).image h.norm).bddAbove
  exact ⟨max b 1,zero_lt_one.trans_le (le_max_right ..),fun z d v=> (u ⟨(z,d), ⟨Set.mem_univ _,mem_closedBall_zero_iff.mpr v⟩,rfl⟩).trans (le_max_left ..)⟩
lemma tollMean {c f:Side}{G:Ratio c f}{X:Type*}[NormedRing X][NormedAlgebra ℝ X][Nonempty (Forest G)] {u:Forest G→X}{C:ℝ}(h:∀ i,‖u i‖ ≤ C): ‖avgF u‖ ≤ C:=by
  let z:= (Fintype.card (Forest G):ℝ); have e:0<z:=by unfold z; positivity
  change ‖z⁻¹ • _‖ ≤ _; rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr e.le)]; have ht:(∑ i:Forest G,C)= z*C:=by rw [Finset.sum_const,nsmul_eq_mul,Finset.card_univ]
  apply (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum fun i _=> h i)) (inv_nonneg.mpr e.le)).trans; rw [ht, ←mul_assoc,inv_mul_cancel₀ e.ne',one_mul]
-- inputs with coefficient bound
lemma boundEach {I:Type*}[Fintype I]{X:Type*}[TopologicalSpace X][CompactSpace X]{Z:Type*}[NormedAddCommGroup Z](F:I→X→Z)(h:∀ i,Continuous (F i)): ∃ D:ℝ,0 ≤D ∧ ∀ i x, ‖F i x‖ ≤ D:=by
  obtain ⟨C,u⟩:= (isCompact_iUnion (f:=fun i=> (fun x=>‖F i x‖) '' Set.univ) fun i=> isCompact_univ.image (h i).norm).bddAbove
  exact ⟨max C 0,le_max_right ..,fun i x=> (u (Set.mem_iUnion.mpr ⟨i, x, Set.mem_univ _,rfl⟩)).trans (le_max_left ..)⟩
lemma boundFull {I:Type*}[Fintype I]{X:Type*}[NormedAddCommGroup X][NormedSpace ℂ X](v:I→ℂ)(x:I→X){C:ℝ}(h:∀ i, ‖v i‖≤1)(g:∀ i,‖x i‖≤ C): ‖∑ i:I, v i • x i‖ ≤ Fintype.card I*C:= (norm_sum_le ..).trans ((sum_le_sum fun i (w:i∈Finset.univ) => (by rw [norm_smul]; exact (mul_le_of_le_one_left (norm_nonneg _) (h i)).trans (g i) : ‖v i • x i‖ ≤ C)).trans_eq (by rw [sum_const,nsmul_eq_mul,Finset.card_univ]))
include p ho
omit p in
lemma subColor (Q:Haro.SpaceM)(u v): subF G j Q.val M ho u v=∑ i:Finset (Single N), crumb (twist (star (flake (Tset N)ᶜ)) v) i • (stringS G j Q.val M ho u).tag i:= rfl
omit p ho in
lemma crumbCost (v:FC (Single N))(i): ‖crumb (twist (star (flake (Tset N)ᶜ)) v) i‖ ≤ ‖v‖ := (norm_entry _ _ _).trans_eq (twist_norm ..)
lemma subTime (C:Haro.SpaceM): ∀ ε:ℝ,0<ε→∀ᶠ Q: Haro.SpaceM in 𝓝 C,∀ z:Nom N P,∀ y:FC (Single N), ‖y‖ ≤1 → ‖subF G j Q.val M ho z y-subF G j C.val M ho z y‖ ≤ ε:=by
  let W(i: Finset (Single N))(Q:SpaceM)(z:Nom N P):= (stringS G j Q.val M ho z).tag i; intro ε e; let K:= (Fintype.card (Finset (Single N)):ℝ); have ck:0<K:=by unfold K; positivity
  have t:∀ᶠ Q in 𝓝 C,∀ i : Finset (Single N),∀ z:Nom N P,‖W i Q z-W i C z‖≤ ε/K:= Filter.eventually_all.mpr fun i=> (holdingCompact (W i) (frameString G j M ho p i) C isCompact_univ (ε/K) (by positivity)).mono fun Q H z=> H z (Set.mem_univ _)
  filter_upwards [t] with Q h z y h'; rw [subColor,subColor,←sum_sub_distrib]; simp_rw [←smul_sub]; refine ((boundFull _ (fun i=> W i Q z-W i C z) (fun i=>(crumbCost y i).trans h') (fun i=> h i z)).trans_eq ?_); change K * (ε/K)=_; field_simp
lemma subBill (C:Haro.SpaceM):∃ D:ℝ, 0<D ∧ ∀ X:Nom N P,∀ Y,‖Y‖ ≤ 1→ ‖subF G j C.val M ho X Y‖ ≤ D := by
  obtain ⟨U,h,z⟩:= boundEach (fun (i:Finset (Single N)) (x: Nom N P)=> (stringS G j C.val M ho x).tag i) (fun i=> Advance.string_cont G j C.val M ho p i) -- order? #check
  let D:ℝ:=Fintype.card (Finset (Single N))*U; refine ⟨D+1,by unfold D; positivity,fun x y hC=>?_⟩; rw [subColor]; refine (boundFull _ _ (fun i=>(crumbCost y i).trans hC) fun i=>z i x).trans (le_add_of_nonneg_right zero_le_one)
set_option maxHeartbeats 1300000 in
lemma rationTemporal (C:Haro.SpaceM): ∀ ε:ℝ,0<ε→∀ᶠ Q in 𝓝 C,∀ x:Ward N,‖x‖ ≤1→∀ U V,‖gathered G j Q.val M ho q d (attire x) U V-gathered G j C.val M ho q d (attire x) U V‖≤ ε:=by
  intro ε e; filter_upwards [subTime G j M ho p C ε e] with u v x A X Y
  unfold gathered avgF; rw [← smul_sub,← Finset.sum_sub_distrib]
  letI : Nonempty (Forest (ratio G)):= Tree.select (ratio G) ho
  exact tollMean (u:=fun i=> before G j u.val M ho q d (attire x) i X Y - before G j C.val M ho q d (attire x) i X Y) fun i=> v (middle G q d i X Y) (attire x Y) ((Ward.pay x Y).trans A)
set_option maxHeartbeats 1300000 in
lemma tollFixed (C:Haro.SpaceM): ∃ D:ℝ, 0<D ∧ ∀ x:Ward N, ‖x‖≤ 1→∀ U V, ‖gathered G j C.val M ho q d (attire x) U V‖ ≤ D:=by
  obtain ⟨D,e,h⟩:= subBill G j M ho p C
  letI : Nonempty (Forest (ratio G)):= Tree.select (ratio G) ho
  exact ⟨D,e,fun x v U V=> tollMean fun i=> h (middle G q d i U V) (attire x V) ((Ward.pay x V).trans v)⟩
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.rationTemporal
#print axioms YM.CF.Buffered.Afterglow.Tapestry.temporalPrice
#print axioms YM.CF.Buffered.Afterglow.Tapestry.tollFixed
