import YM.SU5.FiniteGaugeData.Tapestry.Habanera
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 470000
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
# Native dominated-deck compactness

At WHOLE participating torus. No need for more space at that same period to
understand all the inner limits, even when only the local price on a `followBox`
has an effective bound in the period (Library etc). Use the unit ball of Ward
again. This lemma is rather ROBUST under changes of uniform-price models, but
not claiming any deterministic/effective rank formulas.
-/
set_option quotPrecheck false
section
variable {N P: Side}{I:Type*}(V:I→ Pane N)(A:StepData (More N) (More P))(h:A.patch.Branches A.kernel SU.group)
include h
lemma weightingMenu (β:ℝ): Menu (I:=I) (T:=fun _=> ℝ) (fun i (x:Fields P)=> A.density β x.1 (V i)):=by
  apply Menu.total (I:=I) (T:=fun _=> ℝ) (X:= Fields P) _ (fun t i x=> A.likelihood x.fst t * A.noise β (A.prediction x.fst t) (V i)); intro t _
  have p (z:Pane P): 0 ≤ A.likelihood z t∧ A.likelihood z t ≤ 1:= ⟨A.likelihood_pos z _, (Finset.single_le_sum (f:=A.likelihood z) (fun i _=> A.likelihood_pos z _) (Finset.mem_univ t)).trans_eq (A.chosen h z)⟩
  have hx: Menu (I:=I) (T:=fun _=> ℝ) (fun _ (x:Fields P)=> A.likelihood x.fst t):= ⟨deal_of_one ((A.likelihood_meas h t).comp measurable_fst) (A:=Set.Icc 0 1) isCompact_Icc (fun x=>p x.fst),1,zero_le_one,fun i x=>abs_le.mpr ⟨(by exact (neg_nonpos.mpr zero_le_one).trans (p x.fst).1), (p x.fst).2⟩⟩ -- arg A not s
  have q: Deal (I:=I) (T:=fun _=> Pane N) (fun _ (x:Fields P)=> A.prediction x.fst t):= deal_of_one ((A.prediction_meas h t).comp measurable_fst) isCompact_univ (fun x=>Set.mem_univ _)
  exact hx.mul (Menu.post (q.prod (Deal.pure (T:=fun _:I=>Pane N) V)) (A.noise_cont β)) -- explicit SU
end
section
variable {N P:Side}{I:Type*}(G:Ratio N P)(j:ℕ)(M:Male)(ho: Odd G.count.val)(x:Tariff)(q:Chi)(d:ℝ)
variable (U:I→ Fields N) (W:I→ Ward N) (h:∀ i,‖W i‖≤ 1)
variable {R w:ℕ}(p:LaurentRadius j G.count R) (a:0<d)(b:2*d<firstRadius SU.group)
local notation "σ"=> (fun i=> attire (W i) (U i))
include p h a b
lemma eventMenu (F:Forest (ratio G)) : Menu (I:=I) (T:=fun _=> FC (Single P)) (fun i v=> before G j x.snd.val M ho q d (attire (W i)) F v (U i)):=by
  let X(i:I)(v:Fields P):=middle G q d F v (U i);
  have he: Deal (I:=I) (T:=fun _=> Pane P) (X:=Fields P) (fun _ x=>x.snd):= deal_of_one measurable_snd isCompact_univ (fun _=>Set.mem_univ _)
  have hl: Deal (I:=I) (T:=fun _=>Pane N) (X:=Fields P) (fun i _=> (U i).snd):= Deal.pure _
  have hx: Deal (I:=I) X := ((he.prod hl).post (brake G q d F a b)).prod hl
  -- avoid huge whnf with (U × X × FC) input; expand as finite combo constant scalar * string.
  let V(i:I):= attire (W i) (U i); let Ψ:= Finset (Single N)
  let O(u:Ψ)(i:I):= crumb (twist (star (flake (Tset N)ᶜ)) (V i)) u
  apply Menu.congr (f:= fun i v=> ∑ u:Finset (Single N), O u i • ((stringS G j x.snd.val M ho (X i v)).tag u)) ?_ (fun i v=> (subColor G j M ho x.snd (X i v) (V i)).symm)
  apply Menu.total; intro u t -- may fail
  exact (Menu.cnst (T:=fun _=>ℂ) (X:=Fields P) (O u) zero_le_one (fun i=> (crumbCost ..).trans ((Ward.pay (W i) (U i)).trans (h i)))).scale (Menu.post hx (Advance.string_cont G j x.snd.val M ho p u))

lemma gatherBudget : Menu (T:=fun _=> FC (Single P)) (I:=I) (fun i v=> gathered G j x.snd.val M ho q d (attire (W i)) v (U i)):=
  let r:ℝ:=(Fintype.card (Forest (ratio G)):ℝ)⁻¹; (Menu.cnst (T:=fun _ : I=>ℝ) (X:=Fields P) (fun _=> r) (norm_nonneg r) (fun _=> le_rfl)).scale (Menu.total (T:=fun i:I=> FC (Single P)) _ (fun (F:Forest (ratio G)) i v => before G j x.snd.val M ho q d (attire (W i)) F v (U i)) (fun F _=>eventMenu G j M ho x q d U W h p a b F))

omit p h a b
lemma menuSuture {X D I V:Type*}[NormedAddCommGroup D][NormedSpace ℝ D][MeasurableSpace X][MeasurableSpace V] (μ:Measure V)[IsProbabilityMeasure μ] (f:I→ X→ V→D)(m:Menu (T:=fun _=>D) (fun (t:I×V) x=> f t.1 x t.2))(u:∀ i x, Integrable (f i x) μ): Menu (T:=fun _=> D) (fun i x=> ∫ y, f i x y∂μ):=by
  obtain ⟨Z,h,b⟩:= m.budget
  have hh(i x): ‖∫ t,f i x t∂μ‖≤ Z:=by simpa using norm_integral_le_of_norm_le_const (μ:=μ) (f:=f i x) (Filter.Eventually.of_forall fun t=> b (i,t) x)
  refine ⟨?_,Z,h,hh⟩; intro ε e; obtain ⟨P,w,p⟩:= m.deal _ (half_pos e); refine ⟨P,w,fun x y t i=>?_⟩; rw [dist_eq_norm,←integral_sub (u i x) (u i y)]
  have he(v:V): ‖f i x v-f i y v‖ ≤ ε/2 := (dist_eq_norm (f i x v) (f i y v)) ▸ (p x y t (i,v)).le
  exact (norm_integral_le_of_norm_le_const (C:=ε/2) (μ:=μ) (Filter.Eventually.of_forall he)).trans_lt (by simpa using half_lt_self e) -- precedence

variable (l:Loom N)(A:StepData (More N) (More P))(u:A.ratio=ratio G)
  (e:Measurable l)(v:LoomLaw l w)(g:A.patch.Branches A.kernel SU.group)
local notation "β" => tune G j M ho l q d A p u a b e v g
include h p a b
lemma tempoMenu : Menu (I:=I) (T:=fun _=> FC (Single P)) (fun i=> attire (β x (W i))):=by
  let f(i:I)(v:Fields P)(z:Orbit N):FC (Single P):= A.density x.fst v.1 z.1 • gathered G j x.snd.val M ho q d (attire (W i)) v (drawn l z)
  apply Menu.congr (f:=fun i x=>∫ z,f i x z∂city N) _ (fun i v=> (outright G A j x.snd.val M ho q d x.fst l p e g a b (attire (W i)) (Ward.signs (W i)).env v).symm)
  exact menuSuture (city N) f ((weightingMenu (fun i:I×Orbit N=> i.2.1) A g x.fst).scale (gatherBudget G j M ho x q d (fun i:I× Orbit N=> drawn l i.2) (fun i=>W i.1) (fun i=> h i.1) p a b)) fun i v'=> pushIntegrable G A j x.snd.val M ho q d x.fst l (attire (W i)) p e g a b (Ward.signs (W i)).env v' v'.1
omit h p a b
lemma wardrobeTB {f:I→ Ward N}(u:Menu (T:=fun _=>FC (Single N)) (fun i x=> attire (f i) x)): TotallyBounded (Set.range f):= by
  -- similar paletteTB
  apply capture f; intro ε e; let δ:= ε/4; have d: 0<δ:=by unfold δ; linarith
  obtain ⟨K,k,t⟩:= u.deal _ d
  let T (a:K.Sign):Fields N:= if p:∃ v,K.idT v=a then Classical.choose p else (1,1); let V(i:I)(a:K.Sign):= attire (f i) (T a)
  obtain ⟨C,c,t'⟩:= u.budget
  refine ⟨K.Sign→FC (Single N),inferInstance,V,δ,d,(isCompact_closedBall (0:K.Sign →FC (Single N)) C).totallyBounded.subset ?_,?_⟩
  · rintro _ ⟨i,rfl⟩; rw [mem_closedBall_zero_iff]; exact (pi_norm_le_iff_of_nonneg c).2 fun y=> t' i (T y)
  intro i j ij; rw [dist_eq_norm]; apply lt_of_le_of_lt _ (show 3*δ< ε from by unfold δ; linarith)
  apply Ward.save; intro x
  let k:= K.idT x; let z:=T k; have he : K.withZ x z:= K.id_spec x z (by have w: ∃ y,K.idT y=k:=⟨x,rfl⟩; unfold z T; rw [dif_pos w]; exact (Classical.choose_spec w).symm)
  have v(r:I): dist (attire (f r) x) (V r k)< δ:= t x z he r
  change ‖attire (f i) x-attire (f j) x‖≤ _; rw [←dist_eq_norm]; apply (dist_triangle _ (V i k) _).trans; have hv:= (dist_triangle (V i k) (V j k) (attire (f j) x)); rw [dist_comm (V j k)] at hv; linarith [v i,v j,(dist_pi_lt_iff d).mp ij k]
include p a b
lemma compactRhythm : IsCompactOperator (tune G j M ho l q d A p u a b e v g x):=by
  let T:= Metric.closedBall (0:Ward N) 1; let f:=β x
  have t: TotallyBounded (Set.range (fun z:T=> f z.val)):= wardrobeTB (tempoMenu G j M ho x q d (fun i:T=> i.val) (fun i=>mem_closedBall_zero_iff.mp i.property) p a b l A u e v g)
  let Q:= closure (Set.range (fun z:T=> f z.val)); apply (isCompactOperator_iff_image_closedBall_subset_compact (f.toLinearMap) (r:=1) zero_lt_one).2
  exact ⟨Q, t.closure.isCompact_of_isComplete isClosed_closure.isComplete, fun y (b:y∈f '' T)=> by obtain ⟨y,hz,rfl⟩:= b; exact subset_closure (Set.mem_range_self (⟨y,hz⟩:↑T))⟩
end
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.compactRhythm
