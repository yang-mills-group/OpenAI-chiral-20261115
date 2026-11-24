import GaugeFieldConstruction.SolitaMars
import GaugeFieldConstruction.StyriaRel.YM.Euclid.Pairing
/-!
 # complete formal derivative rows. Keep c and monomial prices explicit
# Extending RP values to tie configurations
-/
set_option autoImplicit false
set_option synthInstance.maxSize 10050
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Boundary Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Classical
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
open NSF.Table.Pairing
open scoped Uniformity InnerProductSpace
lemma LopeArcMars {T B:Type*}[TopologicalSpace T][TopologicalSpace B] {J:Hilbert} {i:T→ B}(h:IsDenseInducing i)(v:T→ J)(f:B× B→ ℂ)(F:Continuous f)(e:∀ t k,inner ℂ (v t) (v k)= f (i t,i k)): Continuous (h.extend v) ∧ ∀ a:T,h.extend v (i a)=v a:=by
 suffices t:∀ a:B,∃ j,Tendsto v (Filter.comap i (𝓝 a)) (𝓝 j) by exact ⟨h.continuous_extend t,h.extend_eq' t⟩
 intro a; haveI:=h.comap_nhds_neBot a
 let L:= comap i (𝓝 a); let q:=L ×ˢ L
 have ha:Tendsto (fun p:T×T=> i p.1) q (𝓝 a):=tendsto_comap.comp tendsto_fst
 have hb:Tendsto (fun p:T×T=> i p.2) q (𝓝 a):=tendsto_comap.comp tendsto_snd
 let V(x y z w:ℂ):ℝ:= Real.sqrt ‖x-y-z+w‖
 have hv(x y:T): dist (v x) (v y)= V (inner ℂ (v x) (v x)) (inner ℂ (v x) (v y)) (inner ℂ (v y) (v x)) (inner ℂ (v y) (v y)):=by
    unfold V; rw [show inner ℂ (v x) (v x)-inner ℂ (v x) (v y)-inner ℂ (v y) (v x)+inner ℂ (v y) (v y)=inner ℂ (v x-v y) (v x-v y) from (by rw [inner_sub_right,inner_sub_left, inner_sub_left]; abel),inner_self_eq_norm_sq_to_K]; simp [dist_eq_norm]
 apply cauchy_map_iff_exists_tendsto.mp
 apply cauchy_map_iff'.mpr; apply tendsto_uniformity_iff_dist_tendsto_zero.mpr
 change Tendsto (fun p:T×T=>dist (v p.1) (v p.2)) q (𝓝 0)
 simp_rw [hv,e]
 rw [show (0:ℝ)=V (f (a,a)) (f (a,a)) (f (a,a)) (f (a,a)) from by simp [V]]
 let Q(p:T×T→B)(t:Tendsto p q (𝓝 a))(r:T×T→B)(s:Tendsto r q (𝓝 a)):= (F.continuousAt (x:=(a,a))).tendsto.comp (t.prodMk_nhds s)
 exact (((((Q _ ha _ ha).sub (Q _ ha _ hb)).sub (Q _ hb _ ha)).add (Q _ hb _ hb)).norm).sqrt -- syntax
variable {n m:ℕ} {S: City} {P:Axis→Across} {L:Sheds S P} {C: Supplies L} {u:ℕ→Carat}
variable (p:Ticket u C) (Y:AreaQc S) {j:Axis}
abbrev TurnupMars (j:Axis)(F:ΧiMars):ΧiMars:= spinFrame four (Signed.mirror j) (shade four F)
abbrev BrightTapeMars (F:Fin n→ΧiMars) (G: Fin m→ΧiMars)(j:Axis): Points n×Points m→ℂ:= fun q=>TerraMars p Y (Fin.append (TurnupMars j ∘ F) G) (closedUp j q.1 q.2)
abbrev SimArchMars (j:Axis)(n:ℕ): Set (Points n):= {x | NSF.Table.Pairing.single x j}
lemma openArchMars (j:Axis)(n:ℕ):IsOpen (SimArchMars j n):=by
 refine isOpen_iff_mem_nhds.mpr (fun i e=>?_); change _ ∈ _; exact ((conf_open _).eventually_mem e.1).and (eventually_all.mpr (fun k:Fin n=> (show Continuous fun x:Points n=> x k j from by fun_prop).continuousAt.tendsto.eventually (lt_mem_nhds (show 0<_ from e.2 k))))
abbrev SawMars (j:Axis)(n:ℕ): Set (SimArchMars j n):= {x|Injective fun i=> x.val i j}
lemma denseArchMars (j:Axis)(n:ℕ): Dense (SawMars j n):=by
 refine dense_iff_inter_open.mpr (fun u v hu=>?_) -- inspect
 let S:=SimArchMars j n; let i:=fun p:S=>p.val
 obtain ⟨a,b,ha⟩:= (Dash.full n).exists_mem_open ((show IsOpenMap i from (openArchMars j n).isOpenEmbedding_subtypeVal.isOpenMap) u v) (hu.image i)
 obtain ⟨x,h,rfl⟩:=ha; exact ⟨x,h,b j⟩ -- tune
variable {J:Hilbert}
-- op input
structure PlayArchiveMars (p:Ticket u C)(Y:AreaQc S)(j:Axis)(J:Hilbert) where
    pipe {n:ℕ}(F:Fin n→ΧiMars): SawMars j n→ J
    worth {n m:ℕ}(F:Fin n→ΧiMars)(G:Fin m→ΧiMars) x y: inner ℂ (pipe F x) (pipe G y)= BrightTapeMars p Y F G j (x.val.val,y.val.val)
variable {p Y} (X:PlayArchiveMars p Y j J)
namespace PlayArchiveMars
abbrev emergeMars(F:Fin n→ΧiMars): SimArchMars j n→J:= (denseArchMars j n).extend (X.pipe F)
lemma entriesMars (F:Fin n→ΧiMars)(G: Fin m→ΧiMars)(p:Ticket u C)(Y:AreaQc S)(j:Axis): Continuous (fun q: SimArchMars j n ×SimArchMars j m=> BrightTapeMars p Y F G j (q.1.val,q.2.val)):=by
 apply ContinuousOn.comp_continuous (g:=TerraMars p Y _) (TerraSm p Y _).continuousOn (((pairIso (n:=n) (m:=m) j).symm.continuous).comp ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))) (fun i=> spans i.1.property i.2.property)
lemma emergedMars (F: Fin n→ΧiMars): Continuous (X.emergeMars F) ∧ ∀ a:SawMars j n,X.emergeMars F a.val=X.pipe F a := LopeArcMars (denseArchMars j n).isDenseInducing_val (X.pipe F) _ (entriesMars F F p Y j) (X.worth F F) -- tune order Variable {p Y}
lemma emergentMars (F:Fin n→ΧiMars)(G: Fin m→ΧiMars)(x:SimArchMars j n)(y:SimArchMars j m): inner ℂ (X.emergeMars F x) (X.emergeMars G y)=BrightTapeMars p Y F G j (x.val,y.val):=by
 have e:= (X.emergedMars F).1; have h:= (X.emergedMars G).1
 let S:=SawMars j n ×ˢ SawMars j m
 have hv:Dense S:= (denseArchMars j n).prod (denseArchMars j m)
 apply EqOn.closure (s:=S) (f:=fun q=>inner ℂ (X.emergeMars F q.1) (X.emergeMars G q.2)) _ ((e.comp continuous_fst).inner (h.comp continuous_snd)) (entriesMars F G p Y j) (hv (x,y))
 intro v hv; change inner ℂ _ _=_; rw [(X.emergedMars F).2 ⟨_,hv.1⟩,(X.emergedMars G).2 ⟨_,hv.2⟩]; exact X.worth F G ⟨_,hv.1⟩ ⟨_,hv.2⟩
#print axioms emergentMars
end PlayArchiveMars
end YM.GaugeFieldConstruction.Ember.Volumetric
