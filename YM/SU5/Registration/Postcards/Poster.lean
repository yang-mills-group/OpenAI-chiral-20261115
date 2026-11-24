import YM.SU5.Registration.Postcards.Billboard

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
open Courts
variable (R:Courts V)(L:Ortho) (J:JMap V)(F:X→InkWaves V)
abbrev official (L:Ortho):Prop:=Lorentz.properTurn L
-- keep sharp test positions under rotation of theta axes in this hypothesis.
def Gratuity (R:Courts V)(J:JMap V)(a:Ortho):Prop:= ∀ v,R.eu a (J (R.eu a v))=J v -- for t− mixing
abbrev shiftedTag (v:T):T:=(R.eu L v.1,Ortho.move L v.2)
noncomputable def advert (L:Ortho)(l:List (TrainJ V)):=l.map (shiftedTag R L)  -- binder shadow? local notation V OK
lemma portraits (c:E4)(l:List T) : advert R L (moveCaps l c)=moveCaps (advert R L l) (Ortho.move L c):=by
 unfold moveCaps advert; rw [List.map_map,List.map_map]; congr 1; funext x; exact Prod.ext rfl (L.motion.map_add _ _)
@[simp] lemma advert_append (l t:List T) : advert R L (l++t)=advert R L l++advert R L t:=List.map_append ..
@[simp] lemma advert_none (l:List T): advert R 1 l=l:=by unfold advert; rw [show shiftedTag R 1=id from funext fun i=> Prod.ext (R.eu1 _) (Ortho.move_one _),List.map_id]
abbrev logo (k:Ortho)(x:Points n) := Points.move k x
abbrev chic (k:Ortho)(u:Fin n→V) := R.eu k ∘ u
lemma graphic (x:Points n)(v:Fin n→V): advert R L (slots x v)=slots (logo L x) (chic R L v):= by unfold advert slots; rw [List.map_ofFn]; rfl
lemma perm_advert {a b:List T}(p:List.Perm a b): List.Perm (advert R L a) (advert R L b):= p.map _
lemma project_ag (h:official L){L':Ortho}(t:official L') (a:List (TrainJ V)): advert R (L*L') a= advert R L (advert R L' a):=by
 unfold advert; rw [List.map_map]; congr 1; funext i; exact Prod.ext (R.euMul _ _ h t _) (Ortho.move_mul ..) -- tune proof args
lemma element_year (h:official L)(n:ℕ) : official (L^n) :=by induction n with
 | zero=> rw [pow_zero]; exact proper_one
 | succ n ih=> rw [pow_succ]; exact proper_mul ih h
lemma compass_compare (R:Courts V)(F:X→InkWaves V)(T':∀ l:List T, Auction l → Auction (advert R L l) → meanFig μ F l=meanFig μ F (advert R L l)) (p:∀ i : sizedStep, ampleStep (Ortho.move L (compass i))) (A B:List (TrainJ V))(a:Auction A)(b:Auction B)(k:Auction (advert R L A))(g:Auction (advert R L B)) {d:E4} (h:SweepAhead A B d)(r:SweepAhead (advert R L A) (advert R L B) (Ortho.move L d)) :
 ∀ i:ℕ, touringCosts μ F A B d compass i = touringCosts μ F (advert R L A) (advert R L B) (Ortho.move L d) (Ortho.move L ∘ compass) i:=by
 intro i; unfold touringCosts postmark; let L₀:= advert R L A; let L₁:=advert R L B; let X₁:= Ortho.move L
 have hp(n:ℕ){d:E4}(h:SweepAhead A B d)(r:SweepAhead L₀ L₁ (X₁ d)) : shipping compass n (fun u=>meanFig μ F (A++moveCaps B u)) d= shipping (X₁ ∘ compass) n (fun u=> meanFig μ F (L₀++moveCaps L₁ u)) (X₁ d):=by
    induction n generalizing d with
    | zero=>
       have e: L₀++moveCaps L₁ (X₁ d) = advert R L (A++moveCaps B d):=by rw [advert_append,portraits];
       change _ = meanFig μ F _; rw [e]; exact T' (A++moveCaps B d) (h.auction a b) (e ▸ r.auction k g)
    | succ n ih=> unfold shipping; congr 1; refine Finset.sum_congr rfl (fun i y=>?_); have hm:X₁ (d+compass i)=X₁ d+X₁ (compass i):= L.motion.map_add ..; exact Eq.trans (ih (h.more (ample_sick _ (aim_compass i))) (hm.symm ▸ r.more (ample_sick _ (p i)))) (by rw [hm]; rfl)
 congr 1; exact Finset.sum_congr rfl fun i _=> hp i h r
-- mirror anti-linear acting, turnSpec includes reverse.but price even at unsorted so can use it exactly
lemma plane_trips (i:SpaceAxis)(p:ℝ)(x:E4): let k:=plane i p; Ortho.move k (mirror (Ortho.move k x))=mirror x:=by
 intro k
 let v:= i.castSucc; let f:= mirror; let y:= Ortho.move k x
 have he : timeAxis ≠ v:= (Fin.castSucc_ne_last i).symm
 have h(u:E4):= Work.A13.plane_givens he u p; let Z:= f y; let T':= Ortho.move k Z;
 have hy: Z timeAxis= -(Ortho.move k x timeAxis):=mirror_time _; have hr(j:Axis)(e:j≠timeAxis)(u:E4):f u j=u j:=by unfold f mirror; rw [Signed.mirrored]; exact if_neg e
 change T'= _; apply PiLp.ext; intro j; by_cases p':j=timeAxis
 · subst j; rw [show T' timeAxis=_ from (h Z).1,hy,show Z v=y v from hr v he.symm y, show y v= _ from (h x).2.1, show Ortho.move k x timeAxis =_ from (h x).1,show mirror x timeAxis= -x timeAxis from mirror_time x]; linear_combination -(x timeAxis)* Real.sin_sq_add_cos_sq p
 by_cases g:j=v; · rw [g,show T' v= _ from (h Z).2.1,show Z v=y v from hr v he.symm y,hy, show y v=_ from (h x).2.1,show Ortho.move k x timeAxis=_ from (h x).1,show mirror x v=x v from hr v he.symm x]; linear_combination (x v)*Real.sin_sq_add_cos_sq p
 rw [(h Z).2.2 j p' g, show Z j=y j from hr j p' _, (h x).2.2 j p' g,show mirror x j=x j from hr j p' _]
lemma turn_advert (i:SpaceAxis)(p:ℝ)(h:Gratuity R J (plane i p))(l:List T): let L:=plane i p; advert R L (turnSpec J (advert R L l)) = turnSpec J l:=by
 intro L; simp only [advert,turnSpec,List.map_reverse,List.map_map]; congr 2; funext u; exact Prod.ext (h u.1) (plane_trips i p u.2)
noncomputable def inkCross (l t:List (TrainJ V)):=∫ x, star (Figures (F x) l)* Figures (F x) t ∂μ
def SpinsAt : Prop := ∀ l:List (TrainJ V), Auction l → Auction (advert R L l) → meanFig μ F l=meanFig μ F (advert R L l)
variable {J F} (A B:List (TrainJ V)) {U:∀ x,Carton (S₀ x) V}(p:Album μ F U J)
include p
-- (116)'s LHS 
lemma keeps_across (v:∀ i:sizedStep,ampleStep (Ortho.move L (compass i)))(t:SpinsAt μ R L F)(h:Auction A)(f:Auction B)(h':Auction (advert R L A))(f':Auction (advert R L B)): fullFig μ F A B=fullFig μ F (advert R L A) (advert R L B):=by
 obtain ⟨C,g,u⟩:= ((spending_ahead A B).and (spending_ahead (advert R L A) (advert R L B))).exists
 obtain ⟨x,y,z⟩:= high_fee L (compass none) (aim_compass _) (v _) C; let hx:=g _ y; let hz:=u _ z; let Ψ:= Ortho.move L ∘ compass; exact tendsto_nhds_unique_of_eventuallyEq (p.clusters_any compass aim_compass compact_cost h f hx) (p.clusters_any Ψ v (compact_turn _ compact_cost L) h' f' hz) (Eventually.of_forall (compass_compare μ L R F t v A B h f h' f' hx hz))
lemma inkCross_corner (v:Auction A) :inkCross μ F A B=fullFig μ F (turnSpec J A) B:= integral_congr_ae (Eventually.of_forall fun i=> congrArg (· * _) (figure_turn (p.accounts i) _ v.sal _ (p.keep i)))
lemma across_theta (i:SpaceAxis)(r:ℝ)(h:∀ j:sizedStep,ampleStep (Ortho.move (plane i r) (compass j)))(z:Gratuity R J (plane i r))(t:SpinsAt μ R (plane i r) F)(hA:Auction A)(hB:Auction B)(h':Auction (advert R (plane i r) A))(f':Auction (advert R (plane i r) B)): inkCross μ F (advert R (plane i r) A) B=inkCross μ F A (advert R (plane i r) B):=by
 rw [inkCross_corner μ (advert R (plane i r) A) B p h',inkCross_corner μ A _ p hA]; let L:= plane i r; rw [←turn_advert R J i r z A]; exact keeps_across μ R L (turnSpec J (advert R L A)) B p h t (salient_mirror _ h' J) hB ((turn_advert R J i r z A).symm ▸ salient_mirror A hA J) f'
end YM.SatinWFixed.Passage
open YM.SatinWFixed.Passage
#print axioms plane_trips
#print axioms across_theta
#print axioms compass_compare
