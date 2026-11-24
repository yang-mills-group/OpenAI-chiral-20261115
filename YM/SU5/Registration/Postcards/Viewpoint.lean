import YM.SU5.Registration.Postcards.FrameShift
import YM.SU5.Registration.LineUp.Pocket

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
lemma slick_open (n:ℕ) : IsOpen {x:Points n|Injective (lineK x)} :=by
 let f(i j:Fin n):= {x:Points n| lineK x i ≠ lineK x j}; have h(i:Fin n): Continuous fun x:Points n=>lineK x i:= (continuous_apply i).comp line_cont; rw [show {x:Points n| _} = ⋂ i:Fin n,⋂ j:Fin n,⋂ _:i≠j,f i j from ?_]; refine isOpen_iInter_of_finite (fun i=> isOpen_iInter_of_finite fun j=> isOpen_iInter_of_finite fun _=> isOpen_ne_fun (h i) (h j))
 ext x; simp only [Set.mem_setOf,Set.mem_iInter]; exact ⟨fun h i j p=> h.ne p,fun h i j p=>by_contra (fun w=> h i j w p)⟩
noncomputable def sortMom (x:Points n): MultilinearMap ℂ (fun _:Fin n=>V) ℂ:=
 (F.entrance (Points.rearrange (Tuple.sort (lineK x)) x)).domDomCongr (Tuple.sort (lineK x))
lemma sorted_here (x:Points n)(q:Injective (lineK x)): Points.rearrange (Tuple.sort (lineK x)) x∈ Wheeled n:= (Tuple.monotone_sort (lineK x)).strictMono_of_injective (q.comp (Tuple.sort (lineK x)).injective)
lemma text_here (x:Points n)(q: Injective (lineK x))(v:Fin n→V): sortMom F x v=Figures F (slots x v):=by
 unfold sortMom Figures; rw [all_scheduled x q _ (sorted_here x q) v,slots_read]; rfl
lemma callback (x:Points n)(q: Injective (lineK x))(v : Fin n→V)(t:Equiv.Perm (Fin n))(h:Points.rearrange t x∈Wheeled n): sortMom F x v= F.entrance (Points.rearrange t x) (v∘t):=by rw [text_here F x q v,Figures, all_scheduled x q t h,slots_read]
lemma wheeled_slick {x:Points n}(U:Equiv.Perm (Fin n))(h: Points.rearrange U x∈Wheeled n):Injective (lineK x):=by
 let z:=Points.rearrange U x; have hz:= (show StrictMono (lineK z) from h).injective.comp U.symm.injective; rw [show lineK x=lineK z ∘ U.symm from funext fun i=>by simp [z]]; exact hz
-- reFrame & logo actions; proper-any.
lemma logo_real : (fun x: Points n => logo L x) = (podium (L,(1:Equiv.Perm (Fin n)))):=by ext x i; simp [podium,reFrame,logo]; try rfl
lemma logo_generic (n:ℕ)(r:Ortho): ∀ᵐ x:Points n, logo r x∈generic n:=by let h:= (podium (r,(1:Equiv.Perm (Fin n)))).measurePreserving.quasiMeasurePreserving.ae (Extraction.almostGeneric n); exact h.mono (fun x p=> (show _ from (congrFun (logo_real r) x).symm ▸ p))
include q
lemma text_cont {x:Points n}(t:Injective (lineK x))(v:Fin n→V): ContinuousAt (fun p=>sortMom F p v) x:=by
 let A:= (Tuple.sort (lineK x)); let u:= Points.rearrange A; have hu:Continuous u:=by rw [show u= (podium (1,A)) from (by ext x i j; simp [podium,Points.move, reFrame, u])]; exact (podium _).continuous
 let w:= sorted_here x t; refine (((entrance_cont F q (v∘A) (u x) w).continuousAt ((wheel_open n).mem_nhds w)).comp hu.continuousAt).congr_of_eventuallyEq ((hu.continuousAt.tendsto.eventually ((wheel_open n).mem_nhds w)).mono ?_); intro y p; exact callback F y (wheeled_slick A p) v A p
omit q
-- eligible times. Wheel all-frame reconstruction. Keep only positions all axes for M questions BEFORE limits.
def Writes : Prop:= official L ∧ ∀ (n:ℕ)(x:Points n), Injective (lineK x)→ Injective (lineK (logo L x)) → ∀ (v:Fin n→V),sortMom F x v = sortMom F (logo L x) (chic R L v)
set_option quotPrecheck false
variable {R L}
include q
lemma writes_points (p:official L)(t:∀ (n:ℕ)(v:Fin n→V), ∀ᵐ x:Points n, sortMom F x v = sortMom F (logo L x) (chic R L v)) : Writes R L F:=by
 refine ⟨p,?_⟩; intro n x hx hv v; let U:= {x:Points n| Injective (lineK x)}; let A:= U ∩ logo L ⁻¹' U; have hc: Continuous (logo (n:=n) L):=by rw [show logo (n:=n) L=(podium (L,1)) from logo_real _]; exact (podium _).continuous
 let q0 := (slick_open n).inter ((slick_open n).preimage hc); let f:= fun x=> sortMom F x v; let g:= fun x:Points n=>sortMom F (logo L x) (chic R L v); have hg:EqOn f g A:=Measure.eqOn_open_of_ae_eq (ae_mono (Measure.restrict_le_self (μ:=volume)) (t n v)) q0 (fun x t=> (text_cont F q t.1 v).continuousWithinAt) (fun x t=> ((text_cont F q t.2 (chic R L v)).comp hc.continuousAt).continuousWithinAt); exact hg ⟨hx,hv⟩
omit q
lemma priced_slick {x:Points n}(h:x∈generic n): Injective (lineK x):=h _
lemma logo_more (x:Points n)(M:Ortho): logo (L*M) x=logo L (logo M x):= PiLp.ext fun i=> Ortho.move_mul L M (x i)
lemma chic_more (M:Ortho)(p:official L)(t:official M)(v:Fin n→V): chic R (L*M) v = chic R L (chic R M v):= funext fun i=> R.euMul L M p t (v i)
@[simp] lemma logo_one (x:Points n) : logo 1 x=x:= PiLp.ext fun _=> Ortho.move_one _
@[simp] lemma chic_one (R:Courts V)(v:Fin n→V): chic R 1 v=v:= funext fun _=> R.eu1 _
lemma Writes.identity (R:Courts V) : Writes R 1 F:= ⟨proper_one,fun _ _ _ _ _=>by rw [logo_one,chic_one]⟩
include q
lemma Writes.race {M:Ortho}(u:Writes R L F)(w:Writes R M F): Writes R (L*M) F:=by
 refine writes_points F q (proper_mul u.1 w.1) (?_); intro n v; filter_upwards [Extraction.almostGeneric n, logo_generic n M,logo_generic n (L*M)] with p f g s
 -- don't rewrite x inside more; preserve t
 rw [w.2 _ p (priced_slick f) (priced_slick g) v, u.2 n _ (priced_slick g) (priced_slick ((logo_more p M) ▸ s))]; rw [logo_more p M,chic_more M u.1 w.1]
omit q
lemma Writes.back (u: Writes R L F): Writes R L⁻¹ F:=by
 refine ⟨proper_inv u.1,?_⟩; intro n x b a v; let r:=L⁻¹; have h:logo L (logo r x)=x:=by rw [← logo_more x r,mul_inv_cancel,logo_one];
 have hb: Injective (lineK (logo L (logo r x))):= h.symm ▸ b; have hu:= u.2 n (logo r x) a hb (chic R L⁻¹ v); rw [h,← chic_more r u.1 (proper_inv u.1),mul_inv_cancel,chic_one] at hu; exact hu.symm
variable [Measure.IsOpenPosMeasure μ]
-- point q continuity all. derive only when actual moment hypothesis spun.
variable {J:JMap V}{U:∀ x,Carton (S₀ x) V}{F₀:X→InkWaves V}
lemma Album.annuals (p:Album μ F₀ U J)(i:SpaceAxis)(N:ℕ)(e:0<N)(r:ℝ)(θ:∀ j:sizedStep,ampleStep (Ortho.move (plane i r) (compass j))) (z:Gratuity R J (plane i r))(t:SpinsAt μ R (plane i r) F₀)(f:plane i r^N=1)(x:X): Writes R (plane i r^2) (F₀ x):=by
 let L:=plane i r; refine writes_points (F₀ x) ((U x).defined_region (p.accounts x)) (element_year _ (proper_param ..) _) ?_ -- pay θ not here
 intro n v; filter_upwards [(ae_all_iff.mpr (fun k:ℕ=>logo_generic n (L^k)))] with y t₁
 let a:=slots y v; have hp(k:ℕ): Auction (advert R (L^k) a):= (graphic R (L^k) y v).symm ▸ ((auction_slots (chic R (L^k) v) _).2 (t₁ k)); have hf : y∈generic n:= by simpa using t₁ 0
 rw [text_here _ _ (priced_slick hf) v,text_here _ _ (priced_slick (t₁ 2)), ← graphic]; exact (p.finite_orbit μ R i r N e θ z t a hp f x).symm
end YM.SatinWFixed.Passage
open YM.SatinWFixed.Passage
#print axioms Album.annuals
#print axioms Writes.back
#print axioms Writes.race
