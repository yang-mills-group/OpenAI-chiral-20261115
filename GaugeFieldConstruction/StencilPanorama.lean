import YM.SU5.Registration.Sectors.Panoramic
import GaugeFieldConstruction.StencilPanCore
import GaugeFieldConstruction.StencilClockRoute
/-! # Positive-pad equivalence on the word Hilbert sector (version-sensitive. Not claiming the whole ManyF)
 Uses criterion much stronger than equality of Eu moments of the two fields: operator relation at every insertion on the full WORD domain of the realized Shelf, AND expression of the target operator on all radial-H domain (not necessarily dense in any rapid topology) as local test-polynomials' sums of the primary Carton fields. Then adjoint word density & heat closes identification. Independent of a possible station constructed from `T` alone.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.SatinWFixed.Carton
open Function Filter MeasureTheory Measure Set Complex Submodule SatinRegistration
open Boundary Probe Mink Multiplier Roy Spectral OS.Semigroup SatinEdge.RealSheet
open CF.Buffered.Afterglow.Hierarchy.Seld
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder ComplexConjugate Classical
variable {H: Hilbert}{S: OS.Semigroup H timeAxis}{V W:Type*}[AddCommGroup V][Module ℂ V][AddCommGroup W][Module ℂ W]
local notation "D"=> radial S
variable {B: Carton S V} {T:Carton S W}(J:JMap V)(z:Remembers B J)
local notation "Q"=> B.pointShelf
include z
private lemma pay_dead_st (t: Module.End ℂ D) (p:t∈Submodule.span ℂ (Set.range B.activate)) (e:∀ L:MarkWords V, t (B.row L)=0) (x:D)(g:x.1∈ (Q)) : t x=0:=
 let h:(Q) = PanSt.sectorSt B.row:= B.span_shelf
 PanSt.pay_dead_st B.activate B.row (fun i x p=>(h ▸ B.light_invariant J z i x (h.symm ▸ p))) (opTag J) (fun i=>B.sharp J z i) _ p e x (h ▸ g)
variable {A:V}{U:W}
include z
private lemma payWord_st (b:∀ f:Test4,T.operator U f ∈ Submodule.span ℂ (range B.activate)) (a:∀ (f:Test4)(x:MarkWords V), B.operator A f (B.row x)= T.operator U f (B.row x)) (f:Test4)(x:D)(t:x.1 ∈ Q): T.operator U f x=B.operator A f x:= sub_eq_zero.mp (pay_dead_st J z (T.operator U f-B.operator A f) ((Submodule.span ..).sub_mem (b f) (Submodule.subset_span (show B.operator A f ∈range B.activate from ⟨(A,f),rfl⟩))) (fun L=> sub_eq_zero.mpr (a _ _).symm) x t)
structure StationPaysSt (B:Carton S V)(T:Carton S W)(x:V)(y:W):Prop where
 field (f:Test4)(v:D)(h:v.1∈ B.pointShelf) : B.operator x f v=T.operator y f v
 heat (s:ℝ≥0)(p:0<s)(v:H)(u:v∈ B.pointShelf): B.bar s x v=T.bar s y v -- not assuming v rapid. No neutralSlabs claim.
 functional (v:D)(u:v.1∈ B.pointShelf)(f:Test4) : (T.operator y f v).val∈ B.pointShelf
 word (v:D)(u:v∈B.words)(f:Test4) : T.operator y f v∈ B.words
 keeps(s:ℝ≥0)(p:0<s)(v:H)(u:v∈ B.pointShelf) : T.bar s y v∈B.pointShelf
-- core transfer
omit z in
private lemma warmth_st (p:H) : Tendsto (fun t=> S.E t p) (𝓝[>] (0:ℝ≥0)) (𝓝 p) :=
 ((DFunLike.congr_fun S.eZero p) ▸ (S.continuousE p).tendsto 0).mono_left nhdsWithin_le_nhds
lemma earn_station_st (x:V)(y:W) (w:∀ f:Test4,T.operator y f∈Submodule.span ℂ (range B.activate)) (t:∀ (f:Test4)(x':MarkWords V), B.operator x f (B.row x')= T.operator y f (B.row x')): StationPaysSt B T x y:=by
 let Y(s:ℝ≥0):= valise S (B.bar s x); let Z(s:ℝ≥0):= valise S (T.bar s y); have he(f:Test4)(v:D)(p:v.val∈Q):= payWord_st J z w t f v p
 have hv(s:ℝ≥0)(p:0<s)(f:Test4)(v:D)(u:v.1∈Q): Z s f v.val=Y s f v.val:=by
    unfold Z Y; rw [← T.blue_apply,← B.blue_apply,T.blue_stove _ s p,B.blue_stove _ s p,show T.black y f _= _ from he f (stoveAt S s v) (B.warmMoves s _ u)]; rfl
 have h(s:ℝ≥0)(p:0<s)(f:Test4)(v:H)(u:v∈Q): Z s f v= Y s f v:=by
    apply tendsto_nhds_unique_of_eventuallyEq ((Z s f).continuous.continuousAt.tendsto.comp (warmth_st v)) ((Y s f).continuous.continuousAt.tendsto.comp (warmth_st v)); filter_upwards[self_mem_nhdsWithin] with t ht; exact hv s p f ⟨_, heat_domain S v ht⟩ (B.warmMoves t v u)
 have hh(s:ℝ≥0)(p:0<s)(v:H)(u:v∈ Q): B.bar s x v=T.bar s y v:= PanSt.valise_pays_enoughSt (B.bar s x) (T.bar s y) v (fun (f:Test4)=>(h s p f v u).symm)
 refine ⟨fun f x t=>(he f _ t).symm,hh,fun v u f=> ?_,fun v u f=>?_,fun s p v u=>?_⟩
 · rw [he f v u]; exact B.light_invariant J z (x,f) _ u
 · rw [he f v (B.inH.le_topologicalClosure (mem_map_of_mem u))]; exact B.written (x,f) v u
 rw [←hh _ p v u]; exact B.bar_invariants J z _ s p v u
open NSF.Boundary
variable {G:NSF.Gauge} {L:NSF.Register G} {A':NSF.Table L} {W:NSF.Boundary.Surface A'} {R:A'.Rotation}{j:A'.RealSpin}
variable (X:Wightman A'){B:Carton S A'.Union} (u:WordLiftSt X (H:=H) (radial S) B.row B.activate)(h:X.Realizes (W:=W) R j)
omit z
local notation "W#"=> X.operators
include h u
lemma word_range_st : LinearMap.range u.pocket.toLinearMap=B.words:= PanSt.pocket_span_st X u h
lemma ray_range_st : LinearMap.range u.rays.toLinearMap=B.pointShelf:= PanSt.ray_closes_st X u h
-- For the same common orientation and Πmeasure. Include positive spectrum (all B.pointShelf commute; actual W on that station).
lemma wordShift_st (t:E4)(p:(W#).H) : S.unit.translation t (u.rays p)=u.rays (X.action.orbit.translation t p):= PanSt.travelUnitSt X u h (fun t p=> congrArg (fun v:D=>v.val) (B.shifted_row t p)) t p
lemma rayPVM_st (s:Set E4)(w:MeasurableSet s)(x:(W#).H) : S.ℚmeasure.region s (u.rays x)= u.rays (X.momentum.region s x):= PanSt.travelRegionSt X u h (fun t p=> congrArg (fun v:D=>v.val) (B.shifted_row t p)) s w x
#print axioms rayPVM_st
#print axioms earn_station_st
#print axioms ray_range_st
end YM.SatinWFixed.Carton
end
