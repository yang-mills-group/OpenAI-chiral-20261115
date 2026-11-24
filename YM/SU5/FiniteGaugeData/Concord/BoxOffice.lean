import YM.SU5.FiniteGaugeData.Concord.PaletteMenu
import Mathlib.Analysis.Normed.Operator.Completeness
/-!
# One-step kernels precompact in local operator norm

Ability to approximate ALL inputs -> finite ticket criterion in the expensive norm topology.
Also record compactness as individual maps. No period law agreement/id hypotheses.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 580000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Concord
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
  Topology ComplexOrder Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent
  Next.Free Bloch Drapes Spire Lifted Skye Precision Tree Push.SectorMeasure Next.SectorChange Fock
open Afterglow Afterglow.Common Afterglow.Sound Afterglow.Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale
section general
variable {I X Y J:Type} [PseudoMetricSpace X]
lemma precompact (f:I→X) 
    (h:∀ε:ℝ,0<ε → ∃ s:Finset I,∀ i,∃ j∈s,dist (f i) (f j)<ε): TotallyBounded (Set.range f) := by
  refine Metric.totallyBounded_iff.mpr (fun ε e=> ?_); obtain ⟨s,v⟩:= h ε e
  refine ⟨f '' (s:Set I), Set.Finite.image _ s.finite_toSet,?_⟩; rintro _ ⟨i,rfl⟩
  obtain ⟨k,h,u⟩:=v i; simp only [Set.mem_iUnion]; exact ⟨_,⟨k,h,rfl⟩,mem_ball.mpr u⟩
lemma sample_domain (f:I→ X)(h:TotallyBounded (Set.range f))(ε:ℝ)(e:0<ε) :
    ∃ s:Finset I, ∀ i,∃ j∈s,dist (f i) (f j)<ε:=by
  obtain ⟨a,t,p,u⟩:= Metric.finite_approx_of_totallyBounded h ε e
  letI : Fintype a:= p.fintype; choose b v using fun i:↥a=>t i.property
  refine ⟨Finset.univ.image b,fun i=>?_⟩; specialize u (Set.mem_range_self (f:=f) i)
  simp only [Set.mem_iUnion] at u; obtain ⟨y,k,w⟩:=u; let j:↥a:=⟨y,k⟩
  refine ⟨b j,mem_image_of_mem b (mem_univ j),?_⟩; rw [v]; exact mem_ball.mp w

lemma screen_pi [Fintype J][CompleteSpace X](f:J→ I→X)(h:∀ i,TotallyBounded (Set.range (f i))): TotallyBounded (Set.range (fun (i:I)(t:J)=> f t i)):= by
  apply (isCompact_pi_infinite (fun i=> (h i).closure.isCompact_of_isClosed isClosed_closure)).totallyBounded.subset
  rintro _ ⟨i,rfl⟩; exact fun t=> subset_closure (Set.mem_range_self _)

lemma buy_spaces (S:Finset Cover)(f:I→ swatches S)(h:Menu (fun i=>tint S (f i))): TotallyBounded (Set.range f):=by
  obtain ⟨u,C,v,w⟩:=h
  refine precompact f ?_
  intro ε e
  have he:0<ε/4:=by linarith
  obtain ⟨P,p,z⟩:= u _ he
  let r (s:P.Sign): PairsC := if h:(P.room s).Nonempty then Classical.choose h else (1,1)
  have m(x:PairsC): P.withZ x (r (P.idT x)):= by
     apply P.id_spec
     have n:(P.room (P.idT x)).Nonempty:=⟨x,rfl⟩; unfold r; rw [dif_pos n]; exact (show _=_ from Classical.choose_spec n).symm
  let F(i:I)(y:P.Sign) := tint S (f i) (r y)
  obtain ⟨A,B⟩:= sample_domain F (((ProperSpace.isCompact_closedBall (0:P.Sign→ℂ) C).totallyBounded).subset
    (show _ from (by rintro _ ⟨i,rfl⟩; apply mem_closedBall_zero_iff.mpr; exact (pi_norm_le_iff_of_nonneg v).mpr (fun y=> w i _)))) (ε/4) he
  refine ⟨A,fun i=>?_⟩; obtain ⟨j,q,b⟩:=B i; refine ⟨j,q,?_⟩
  rw [dist_eq_norm]; apply lt_of_le_of_lt _ (by linarith : 3*(ε/4)<ε)
  refine (swatches_norm_le S (by linarith)).2 (fun x=> ?_)
  rw [tint_sub,Pi.sub_apply,←dist_eq_norm]; let l:= P.idT x
  apply (dist_triangle4 (tint S (f i) x) (F i l) (F j l) (tint S (f j) x)).trans
  have hl : dist (tint S (f i) x) (F i l) < ε/4:= z x _ (m x) i
  have hh : dist (tint S (f j) x) (F j l) < ε/4:= z x _ (m x) j
  rw [dist_comm (F j l)]
  linarith [lt_of_le_of_lt (dist_le_pi_dist (F i) (F j) l) b]

lemma crating {Y:Type}[NormedAddCommGroup Y][CompleteSpace Y][NormedSpace ℂ Y]
    {Z:Type}[NormedAddCommGroup Z][NormedSpace ℂ Z](g:I→Z→L[ℂ] Y)
    (h:∀x,TotallyBounded (Set.range (fun i:I=>g i x)))
    (d:∀ ε:ℝ,0<ε→ ∃ V:Finset Z,∀ x:Z,‖x‖=1→∃ y∈ V,∀ i,dist (g i x) (g i y) ≤ ε):
    TotallyBounded (Set.range g):=by
  refine precompact g ?_; intro ε e
  have he:0<ε/4:=by linarith
  obtain ⟨V,H⟩:= d _ he
  obtain ⟨Z',hZ⟩:= sample_domain (fun i (x:↥V)=>g i x.val) (screen_pi (fun (x:↥V) i=>g i x.val) (fun i=>h i.val)) _ he
  refine ⟨Z',fun i=>?_⟩; obtain ⟨j,z,h⟩:= hZ i; refine ⟨j,z,lt_of_le_of_lt ?_ (by linarith : 3*(ε/4)<ε)⟩
  rw [dist_eq_norm]; refine ContinuousLinearMap.opNorm_le_of_unit_norm (by linarith) (fun x p=> ?_)
  rw [ContinuousLinearMap.sub_apply,←dist_eq_norm]; obtain ⟨y,t,v⟩:= H x p
  apply (dist_triangle4 _ (g i y) (g j y) _).trans; have hg: dist (g i y) (g j y)<ε/4:=lt_of_le_of_lt (dist_le_pi_dist (fun (x:V)=>g i x.val) (fun x:V=>g j x.val) ⟨y,t⟩) h
  rw [dist_comm (g j y)]; linarith [v i,v j]
end general

variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)
variable (S:Finset Cover)(s:ℕ)
local notation "κ"=> (local_post_bound Y H S s).choose
local notation "Ψ"=> screen Y H S s
local notation "S₁" => swept Λ l S
local notation "Jx"=> Matinee Y H S s
local notation "Tq"=> plaza (Λ:=Λ) S
local notation "C"=> (VolumeCape.Dream.plot l).C
local notation "K"=> (VolumeCape.Dream.plot l).K

lemma output_cart {I:Type} (t:I→Matinee Y H S s)(f:I→Palette S){q:ℝ}(p:0≤q)(h:∀i,‖f i‖≤q) : TotallyBounded (Set.range (fun i=> screen Y H S s (t i).1.1 (t i).1.2 (f i))):=by
  simp_rw [house Y H S s (t _).property] -- simplify
  exact screen_pi (X:=swatches S₁) (J:=Evens S₁) (fun v i=> present Y H S s _ _ (t i).property (f i) v)
    (fun i=> buy_spaces (swept Λ l S) _ (palette_house Y H S s t f p h i))

lemma row_debt (u:Evens S) : ∀ ε:ℝ,0<ε → ∃ Y':Finset (swatches S),∀ f:swatches S, ‖f‖ ≤1→ ∃ g∈ Y',∀ i:Jx,
    dist (Ψ i.val.1 i.val.2 (flyer S u f)) (Ψ i.val.1 i.val.2 (flyer S u g))≤ ε := by
  -- use Patrons style nets on the *Touch unit ball*. Not a net for sup topology!
  -- scale into that ball. use Debt to pay immediately on the one step.
  intro ε e; let r (g:swatches S) (y:Courses C Tq) (q:Hall C Tq) := amount C K Tq (tint S g) y q
  have hr(g y): Envelope (r g y):= amount_env C K Tq ((toPurse S g).property.mono (liner_here ..)) _
  let L:= (Fintype.card (Courses C Tq):ℝ)+1; have hL:0<L:=by unfold L; positivity
  let g(f:swatches S):=(L⁻¹:ℂ) • f
  let A:= Satin.edition Y S s (tagWord S u.val)
  obtain ⟨Z,B,N⟩:= approximate_fleet (Common.law C Tq) r hr (upholstery Y S s (tagWord S u.val)) (die_env Y S s (tagWord S u.val)) (ε/L) (by positivity)
  let z(f:swatches S):=(L:ℂ) • f
  refine ⟨Z.image z, fun f p=>?_⟩
  have hp(k x) : ‖r (g f) k x‖ ≤ L⁻¹ := by
    let s:PairsC:= Common.pairs C K Tq k x; change ‖((L:ℂ)⁻¹) • tint S f s‖ ≤ _
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hL.le]; exact mul_le_of_le_one_right (inv_pos.mpr hL).le ((tint_bound ..).trans p)
  obtain ⟨a,w,H'⟩:= N (g f) (by
    refine le_trans (sum_le_sum (s:=univ) (g:=fun _=>L⁻¹) (fun (i:Courses C Tq) _=> ((integral_mono_of_nonneg (Eventually.of_forall (fun x=> norm_nonneg _)) (g:=fun x=>L⁻¹) (integrable_const _) (Eventually.of_forall (fun _=> hp i _))).trans_eq (show ∫ (_x:Hall C Tq), L⁻¹ ∂Common.law C Tq= _ from (by simp))))) ?_; rw [sum_const,card_univ,nsmul_eq_mul, ←div_eq_mul_inv,div_le_one hL]; exact le_add_of_nonneg_right zero_le_one)
  refine ⟨z a,mem_image_of_mem z w,?_⟩; intro i
  obtain ⟨⟨x,k⟩,p⟩:= i; let R':Jx:=⟨(x,k),p⟩; let b:= Ψ x k
  have hx:Nonempty (Courses C Tq):=by
    obtain ⟨μ,hp,_,_⟩:= (Y.voyage x).craft s; exact Nonempty.map (chooseCourse C Tq (side Y x s)) (nonempty_of_isProbabilityMeasure μ)
  let t: Page Y S s:= ⟨⟨(x,k),p.timely⟩,1,(Classical.choice hx),1⟩
  let Q:= g f; let Z0:= flyer S u Q; let V:=flyer S u a; let A₀:= b Z0; let B₀:= b V
  have he: ‖A₀-B₀‖ ≤ ε/L:=by
    refine cost_palette Y H x (s+1) (swept Λ l S) _ (Eq.mp (congrArg (Hosp S₁) (terrain Y H (Y.ir x) (s+1))) (roomy p.main.bigger)) ?_; intro i
    let d:= debt Y S s (tagWord S u.val) H (bracketV ..) (x:=toPurse S Q) (y:=toPurse S a) t p.main.lower (ε/L) (fun t r=> le_of_lt (H' t r))
    have ht(f:swatches S): nativeHere Y H x (s+1) S₁ (b (flyer S u f))= haul Y s x k (Satin.knot (side Y x s) (tagWord S u.val) (tint S f)):=by unfold b; rw [house Y H S s p, repertoire,with_fly]
    rw [show A₀-B₀=b (flyer S u (Q-a)) from (by unfold A₀ B₀ Z0 V; simp [← map_sub, flyer, Pi.single_sub]),ht]
    exact d i
  change dist (b (flyer S u f)) (b (flyer S u (z a))) ≤ ε
  have hq:z Q=f:= by unfold z Q g; rw [smul_smul,mul_inv_cancel₀,one_smul]; exact_mod_cast hL.ne'
  rw [dist_eq_norm]; nth_rw 1 [←hq]; unfold z; rw [flyer_smul S u a, flyer_smul S u Q, map_smul b (L:ℂ) (flyer S u a), map_smul b (L:ℂ) (flyer S u Q),←smul_sub,norm_smul,Complex.norm_real,Real.norm_of_nonneg hL.le]; exact le_trans (mul_le_mul_of_nonneg_left he hL.le) (le_of_eq (mul_div_cancel₀ _ hL.ne'))

lemma gate_debt : ∀ ε:ℝ,0<ε→ ∃ Z:Finset (Palette S),∀ x: Palette S,‖x‖=1→∃ y∈ Z,∀ i:Matinee Y H S s,
    dist (screen Y H S s i.val.1 i.val.2 x) (screen Y H S s i.val.1 i.val.2 y) ≤ ε:=by
  intro ε e; let v:= ε/(count S+1); have he:=count_nonneg S; have h:0<v:=div_pos e (by linarith)
  choose F P using fun u:Evens S=> row_debt Y H S s u v h
  let z(x:∀ i, ↥(F i)) : Palette S := fun i=> (x i).val
  refine ⟨univ.image z, fun x p=>?_⟩; choose y B U using fun i=> P i (x i) ((norm_le_pi_norm x i).trans_eq p)
  let y':∀ i, ↥(F i):= fun i=>⟨y i,B i⟩; refine ⟨y,mem_image_of_mem z (mem_univ y'),fun i=>?_⟩
  rw [dist_eq_norm,all_fly S x, all_fly S y,map_sum,map_sum, ←sum_sub_distrib]; apply (norm_sum_le ..).trans
  refine le_trans (sum_le_sum (g:=fun _=>v) (fun a _=> ?_)) ?_
  · rw [←dist_eq_norm]; exact U a i -- metavars
  rw [sum_const,card_univ,nsmul_eq_mul]; change count S*v≤_; exact (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) h.le).trans_eq (mul_div_cancel₀ _ (by linarith : count S+1≠0))

lemma crate : TotallyBounded (Set.range (fun i:Matinee Y H S s=> screen Y H S s i.val.1 i.val.2)):=
  crating _ (fun x=> output_cart Y H S s id (fun _=>x) (norm_nonneg x) (fun _=>le_rfl)) (gate_debt Y H S s)

theorem boxOffice : IsCompact (closure (Set.range (Function.uncurry (screen Y H S s)))) := by
  refine TotallyBounded.isCompact_of_isClosed (TotallyBounded.closure (TotallyBounded.subset ?_ ((totallyBounded_insert 0).mpr (crate Y H S s)))) isClosed_closure
  rintro b ⟨⟨i,k⟩,rfl⟩
  by_cases p: SeasonPass Y H S s i k; swap; · exact Set.mem_insert_iff.mpr (Or.inl (stall Y H S s p))
  exact Set.mem_insert_iff.mpr (Or.inr ⟨⟨(i,k),p⟩,rfl⟩)
end YM.CF.Buffered.Concord
#print axioms YM.CF.Buffered.Concord.boxOffice
