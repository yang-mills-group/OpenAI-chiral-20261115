import YM.SU5.Registration.Postcards.Viewpoint

/-!
 # Euclidean crossing (116) by finite averages escaping to infinity.
 
 Enough in this version to run many usual *Eu boost-plane* tests. No full-cone estimate
 used in the cluster pricing, in E or in M! (Need equality of unconditioned point-moment at the indicated
 tests as structural angular estimate.) Our method uses real-angle co-rotation even
 in the payments evaluating (116). Works with REAL displacements large even in every axis,
 need not supply time-ground projector equality to joint projection of unconditioned.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinWFixed.Passage
open Boundary Mink Analysis Function Set Filter OS.Semigroup
open scoped Topology BigOperators InnerProductSpace NNReal ENNReal
open CF.Buffered.Afterglow.Tower.VacuumSelection
open CF.Buffered.Afterglow.Hierarchy.Seld
open CF.Buffered.Afterglow.Hierarchy.Seld.Poin
open Carton
variable {H : Hilbert} (S : OS.Semigroup H timeAxis)
open ContinuousLinearMap MeasureTheory Small
variable {S} {V : Type*}[AddCommGroup V][Module ℂ V] (B:Carton S V){n m:ℕ}
-- use Postcards/ bridge with temporal fare subtracting before pricing
local notation "T" => TrainJ V
variable {X:Type*} [TopologicalSpace X][MeasurableSpace X][OpensMeasurableSpace X][CompactSpace X] (μ:Measure X)[IsFiniteMeasure μ]
variable {H₀:X→Hilbert}{S₀:∀ x,OS.Semigroup (H₀ x) timeAxis}
-- continuation in angle at purchase. via `tuple_sort` with proof, E & M API.
variable (R:Courts V)(L:Ortho)(F:InkWaves V) (q:F.Region)
open Courts
set_option linter.unusedSectionVars false
variable (i:SpaceAxis)
lemma plane_curve (x:Points n): Continuous fun t=> logo (plane i t) x :=
 (PiLp.continuousLinearEquiv 2 ℝ _).symm.continuous.comp (continuous_pi (fun j:Fin n=> continuous_iff_continuousAt.mpr (fun t=> (Work.A13.hasDerivAt_move _ _ t).continuousAt))) -- tune
lemma plane_neg (t:ℝ): plane i (-t)=(plane i t)⁻¹:=by apply eq_inv_of_mul_eq_one_left; unfold plane; rw [← parameter_add]; simp [oneParameter_zero]
lemma curves_label (r:ℝ)(v:V): GearContinuity (fun t=> R.eu (plane i t) v) r:=by
 obtain ⟨k,g,c,e,h⟩:= (R.euD i (R.eu (plane i r) v)).gear
 refine ⟨k,g,fun i t=> c i (t-r),fun i=>ContinuousAt.comp (x:=r) (f:=fun t=>t-r) (g:=c i) (by simpa using e i) (continuous_id.sub continuous_const|>.continuousAt),?_⟩ -- `(y:=_` param?
 filter_upwards [(show Tendsto (fun x:ℝ=> x-r) (𝓝 r) (𝓝 0) by simpa using (continuousAt_id (x:=r)).tendsto.sub_const r).eventually h] with t h; rw [←h]; exact DFunLike.congr_fun (congrArg R.eu (show plane i t=plane i (t-r)*plane i r from by rw [← parameter_add, sub_add_cancel])) v |>.trans (R.euMul _ _ (proper_param ..) (proper_param ..) _) -- precedence
include q
noncomputable def hospitality (F:InkWaves V)(q:F.Region) (R:Courts V)(i:SpaceAxis): AddSubgroup ℝ where
 carrier := {r | Writes R (plane i r) F}
 zero_mem' := by rw [Set.mem_setOf, show plane i 0=1 from oneParameter_zero _]; exact Writes.identity F R
 add_mem' := fun {x y} hx hy=> by change Writes R (Ortho.oneParameter _ (x+y)) F; rw [parameter_add]; exact Writes.race F q hx hy
 neg_mem' := by intro t h; change Writes R _ F; rw [plane_neg]; exact Writes.back F h
lemma house_tilt (p: Dense (hospitality F q R i:Set ℝ)) (t:ℝ): Writes R (plane i t) F:=by
 refine ⟨proper_param ..,?_⟩; intro n x hx hw v
 let L(u:ℝ):= logo (plane i u) x; let f(s:ℝ):= sortMom F (L s); let g(s:ℝ):= chic R (plane i s) v; let C:= (hospitality F q R i); have hm(y:Fin n→V): ContinuousAt (fun u=> f u y) t:= ContinuousAt.comp (x:=t) (g:=fun u=>sortMom F u y) (f:=L) (text_cont F q hw y) (plane_curve i x).continuousAt; have hv : ContinuousAt (fun u=> f u (g u)) t:= GearContinuity.paid t f g (fun j=> curves_label R i t (v j)) hm
 let K:= 𝓝[(C:Set ℝ)] t; have hK:K.NeBot:= mem_closure_iff_nhdsWithin_neBot.mp (p t)
 have hu:∀ᶠ s in K, f s (g s)= sortMom F x v:=by
    filter_upwards [self_mem_nhdsWithin, (plane_curve i x).continuousAt.tendsto.mono_left nhdsWithin_le_nhds |>.eventually ((slick_open n).mem_nhds hw)] with s h b; exact Eq.symm ((show Writes R (plane i s) F from h).2 n x hx b v)
 exact tendsto_nhds_unique ((tendsto_const_nhds (x:=sortMom F x v)).congr' ((show (fun u=> f u (g u)) =ᶠ[K] (fun _=> sortMom F x v) from hu).symm)) (hv.tendsto.mono_left nhdsWithin_le_nhds)
omit q
variable {F₀:X→InkWaves V}{J:JMap V}{U:∀ x,Carton (S₀ x) V} (h:Album μ F₀ U J)
-- main new estimate shape - unconditioned only; orbit-count costs proper any. only need small real angle tests. no uniform on the angle variation or arity order, but DOES require (globally indicated quantifier) ALL field-orders & inputs at each rotating angle posing. May also reduce to single *irrational* rotation if recurrence long etc - not done here.
def Corridor :Prop:= ∀ c:SpaceAxis, ∀ᶠ i:ℕ in atTop, SpinsAt μ R (plane c (cruise i)) F₀ ∧ Gratuity R J (plane c (cruise i))
variable [Measure.IsOpenPosMeasure μ]
include h
lemma Album.sees_portrait (p:Corridor (F₀:=F₀) (J:=J) μ R) (x:X) (i:SpaceAxis)(t:ℝ): Writes R (plane i t) (F₀ x):= by
 let F:= F₀ x; have hp:F.Region:= (U x).defined_region (h.accounts x)
 refine house_tilt R F hp i (?_) t -- order
 let d:= hospitality F hp R i
 have he:Tendsto cruise atTop (𝓝 0):= tendsto_const_div_atTop_nhds_zero_nat _
 apply AddSubgroup.dense_of_not_isolated_zero d; intro ε w
 obtain ⟨N, ⟨P,s⟩, a,b,e⟩:= ((p i).and ((he.eventually (eventually_compass i)).and ((he.eventually (gt_mem_nhds (half_pos w))).and (eventually_gt_atTop 0)))).exists
 let z:=cruise N; obtain hz:0<z:=(div_pos (mul_pos two_pos Real.pi_pos) (Nat.cast_pos.mpr e))
 have hm:= h.annuals μ (R:=R) i N e z a s P (cruise_period i N e) x -- syntax
 rw [show plane i z^2=plane i (z+z) from (by rw [pow_two]; exact (parameter_add _ z z).symm)] at hm
 exact ⟨z+z,hm, mem_Ioo.mpr ⟨add_pos hz hz, by linarith only [show z<ε/2 from b]⟩⟩
omit h
open Apso (Rho gift)
-- generate whole SO. reuse pinned Dally but no dependence on its sector restoration hypotheses.
lemma rotations_all (Q:Set Ortho)(p:(1:Ortho)∈Q)(h:∀ a∈Q,∀ b∈Q,a*b∈Q)(t:∀ (i:SpaceAxis)(u:ℝ),plane i u∈Q)(T':Ortho)(v:official T'): T'∈Q:=by
 let R:= (ContinuousLinearEquiv.unitsEquiv ℝ E4).symm (T'.motion.toContinuousLinearEquiv); let l:SO:=⟨R,(show R∈North from ⟨v,fun _=> T'.move_norm _⟩)⟩
 have hz(S:SO): ∃ U:Ortho,U∈ Q ∧ ∀ x:E4,Ortho.move U x=gift S x:=by
    let hG:= Apso.sheen S; induction hG with
    | one=> exact ⟨1,p,fun x=> Ortho.move_one _⟩
    | chain x y _ _ hx hy=> obtain ⟨u,p,t⟩:=hx; obtain ⟨v,r,f⟩:=hy; exact ⟨u*v,h _ p _ r, fun x=>by rw [Ortho.move_mul,f,t]; rfl⟩
    | turn i r=> refine ⟨plane i (-r),t i (-r),fun x=>?_⟩
                 apply Mink.ext_by; obtain ⟨a,b,c⟩:=Work.A13.plane_givens (show timeAxis≠i.castSucc from (Fin.castSucc_ne_last i).symm) x (-r); apply PiLp.ext; intro j; change Ortho.move (plane i (-r)) x j.castSucc = gift (Rho i r) x j.castSucc; by_cases u:i=j;
                 · subst j; rw [show Ortho.move (plane i (-r)) x i.castSucc=_ from b, Apso.warpS]; simp [YM.time, add_comm]
                 rw [c _ (Fin.castSucc_ne_last _) (by simpa using Ne.symm u),Apso.warpQ i j r x (Ne.symm u)] -- `u.symm` not
                 rw [show YM.time (Ortho.move (plane i (-r)) x)= _ from (Work.A13.plane_givens (show timeAxis≠i.castSucc from (Fin.castSucc_ne_last i).symm) x (-r)).1, Apso.warpT]; simp [YM.time,sub_eq_add_neg]
 obtain ⟨Z,b,h⟩:= hz l; exact (Ortho.ext Z T' h) ▸ b
-- unconditioned → elected at every gamma here.
include h
lemma Album.world_frame (p:Corridor (F₀:=F₀) (J:=J) μ R) (x:X) (u:Ortho)(q:official u) : Writes R u (F₀ x):= rotations_all (fun L=> Writes R L (F₀ x)) (Writes.identity _ _) (fun _ P _ W=> Writes.race (F₀ x) ((U x).defined_region (h.accounts x)) P W) (h.sees_portrait μ R p x) u q
lemma Album.sendsLoc (p:Corridor (F₀:=F₀) (J:=J) μ R) (x:X) : R.Carriage (F₀ x) := by
 intro n T' v y he hv z u w; let L:=T'.1; let f:= F₀ x; let s:= T'.2; have t:= (h.world_frame μ R p x T'.1 v).2 n y (priced_slick he) (wheeled_slick s u) w
 change _=_ at t; rw [callback f (logo L y) (wheeled_slick s u) _ s u,text_here f y (priced_slick he) w] at t; exact t.symm.trans (by rw [figures_here _ _ ((chron_slots ..).2 hv),slots_read])
end YM.SatinWFixed.Passage
open YM.SatinWFixed.Passage
#print axioms Album.world_frame
#print axioms Album.sendsLoc
#print axioms rotations_all
