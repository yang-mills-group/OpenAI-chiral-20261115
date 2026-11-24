import YM.CF.DPress.FD.Warp.Carry
/-!
 Good subcomplex. Good frames delegated to the previous local transports;
 at simplex-grid queries coherence by using own-support anchor. `Clans` can buy *all*
 k≤4 simplexes of nearby sites, not just meshes that will be consulted at positive weights.
 No bounds here on number of those simplexes by a constant not depending on S (we price in
 radius, not number of colors; unlike total simplex prices). At any joint two adjacent queries,
 just use one simplex with all of their membership-weight supports. Later these estimates go into
 `Seam` bounds around that simplex, or the `Must` read on positive support. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Lattice Cash Bifold Deck Hue Geo Warm Frame Ramp Spire Skye SU Lat Scroll Tw Finset Con
open Cube (More)
open scoped Topology BigOperators ENNReal NNReal Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {n:Side}{r l m N:ℕ}{u:ℝ}
namespace Turf
abbrev Clove(n:Side)(m:ℕ):= leaf n m→ rug n
abbrev clove(n:Side)(m:ℕ):Tw n (Clove n m) := arr (pullW n m) (chart n)
lemma valid_v(s:Sweep n)(g:Clove n m)(x:leaf n m): (clove n m).mv s g x= Tw.Ω s (g (ωr s⁻¹ x)):=rfl
lemma η_v(s:Sweep n)(g:rug n)(x:Seat n): Tw.Ω s g (Sum.inl x)= windX s.charge (g (.inl (boxA s x))):=by change windX s.charge (g (.inl ((pos n).mv s⁻¹ x))) = _; rw [Tw.pos_y]
lemma η_w(s:Sweep n)(g:rug n)(i:Fin 5):Tw.Ω s g (.inr i)=windX s.charge (g (.inr i)):=rfl
lemma sane_M(s:Sweep n): Measurable ((clove n m).mv s):=by apply Continuous.measurable; refine continuous_pi fun i=>?_ ; exact (neat s).continuous.comp (continuous_apply (ωr s⁻¹ i))
-- classify. Define clan only distance (subsets closed); Book size separate. £ guards.
def Clan (l:ℕ)(S:Support (More n)):Prop:= ∀ i∈ S,∀ j∈ S, close l i j
def Grade (l:ℕ)(u:ℝ)(X:Pane n)(S:Support (More n)):Prop:=∀ i∈ S, Sound l u X i
-- halo utility included
variable {s:Sweep n} {S D T: Support (More n)} {X Y:Pane n}
lemma Clan.mono (p: Clan l S)(t:D⊆ S):Clan l D:=fun i x j y=> p i (t x) j (t y)
lemma Clan.rotate (p: Clan l S):Clan l (ζ s S):= by
 intro i x j y; obtain ⟨i,rfl⟩:= (boxA s).surjective i; obtain ⟨j,rfl⟩:= (boxA s).surjective j; unfold close; rw [sitT]; exact p i ((mem_s ..).1 x) j ((mem_s ..).1 y)
lemma Grade.mono(p:Grade l u X S)(t:D⊆S):Grade l u X D:=fun i x=> p i (t x)
lemma grade_u(s:Sweep n):Grade l u (flashA s X) S = Grade l u X (ζ s S):= by
 apply propext; unfold Grade; constructor
 · intro x i v; obtain ⟨i,rfl⟩:= (boxA s).surjective i; exact (sounds _ _).1 (x _ ((mem_s ..).1 v))
 intro t i y; exact (sounds _ _).2 (t _ ((mem_s ..).2 y))
lemma Grade.rotate(p:Grade l u X S): Grade l u (flashA s X) (ζ s⁻¹ S):=by rw [grade_u,ζ_rev]; exact p
lemma grade_M (l:ℕ)(u:ℝ)(S:Support (More n)):MeasurableSet {U:Pane n| Grade l u U S}:=by unfold Grade; simp_rw [Set.setOf_forall]; exact MeasurableSet.iInter fun i=> MeasurableSet.iInter (fun _=> sure i l u)
lemma end_h (g:D⊆S){r t:ℕ}(u:r≤ t):halo r D⊆ halo t S:=fun i x=> by obtain ⟨j,k,v⟩:=halo_spec.mp x; exact halo_spec.mpr ⟨j,g k,v.trans u⟩
lemma bit_h {i:Seat n} (v:i∈ S)(t:ℕ) :brim i t⊆ halo t S:= end_h (singleton_subset_iff.mpr v) le_rfl
lemma touch_B (p: Agrees (halo (globe l+5) S) X Y):Grade l u X S=Grade l u Y S:= by unfold Grade; refine propext (forall_congr' (fun i=>forall_congr' fun (u:i∈ S)=>?_)); rw [stableB i (agrees_mono p (Finset.coe_subset.mpr (bit_h u _)))]
-- picks reference in S, use same choice for all probes even if this facet occurs as
-- part of different simplexes. Law on orientation bits.
def SeatT (S:Support (More n))(η:Cotton n): Seat n:= tune (Dry Unit n) (pos n) (fun E _=>Sat.key E) (scale n) (η S) S ()
lemma grip (η:Cotton n)(p:S.Nonempty):SeatT S η∈ S:=by
 let s:= η S; have he: (ζ s⁻¹ S).Nonempty:=(ζL s⁻¹ S).1 p; have h:= Sat.tithe (ζ s⁻¹ S) he; unfold SeatT tune; rw [Tw.pos_y]; exact (mem_T s _ S).1 h
lemma reachP (η:Cotton n)(S:Support (More n))(s:Sweep n):SeatT (ζ s⁻¹ S) (act s η) = (boxA s).symm (SeatT S η):= tune_v (Dry Unit n) (pos n) s η (scale n) S (fun x:Support (More n)=> x) (by intro i; exact rfl) () (fun i _=> Sat.key i)
lemma grip_v (η μ:Cotton n)(p:η S=μ S):SeatT S η=SeatT S μ:=by unfold SeatT; rw [p]
end Turf
end YM.CF.DPress.FD
