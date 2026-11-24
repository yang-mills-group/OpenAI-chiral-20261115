import YM.SU5.Registration.Sectors.FilterHeat
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.LinearPMap
/-!
 # Actual operators on the sector.

 Preserve on the radial-domain-restricted intersection with Hpt. Word span
 will be used for a cyclic invariant common dense domain on Hpt. Even the
 unsmeared strictly-positive-pad point operators operate there (on whole sector
 at that pad, not asserting on `words`).
 Inspiration pinned `Fields/System` & `Work/C15`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinWFixed.Carton
open Function Filter MeasureTheory Measure Set Complex Submodule SatinRegistration
open Boundary Probe Mink Multiplier Roy Spectral OS.Semigroup SatinEdge.RealSheet
open CF.Buffered.Afterglow.Hierarchy.Seld
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
variable {H: Hilbert}{S: OS.Semigroup H timeAxis}{V:Type*}[AddCommGroup V][Module ℂ V]
local notation "D"=> radial S
local notation "T"=> S.E
variable (B:Carton S V)
local notation "Q"=> B.pointShelf
local notation "R"=> B.station
lemma written (t:MarkType V) (x:D)(h:x∈ B.words) : B.activate t x ∈ B.words:=by
 refine Submodule.map_le_iff_le_comap.mp (show B.words.map (B.activate t) ≤ B.words from ?_) h
 unfold words; rw [Submodule.map_span, ← Set.range_comp]; refine Submodule.span_le.mpr ?_
 rintro _ ⟨p,rfl⟩; exact B.words_exist (t::p)
variable (J:JMap V)(z:Remembers B J)
include z
-- functional analysis before P-point kernels. rigorous whether or not D restricted equals word span as dense domain.
lemma dark_invariant (t:MarkType V)(x:D)(p:x.1∈ Qᗮ): (B.activate t x).1∈ Qᗮ:= by
 unfold pointShelf; rw [orthogonal_closure]; intro i hi; rcases hi with ⟨w,u,rfl⟩;
 let X:= opTag J t; have ht:opTag J X=t:=by simp [X,opTag,Probe.bar_twice,z.both t.1];
 rw [← ht]; change inner ℂ w.1 (B.activate (opTag J X) x).1=_; rw [← B.sharp J z]; exact inner_right_of_mem_orthogonal (B.inH.le_topologicalClosure (mem_map_of_mem (B.written X w u))) p
omit z in
private lemma warmth_visits (p:H) : Tendsto (fun t=> T t p) (𝓝[>] (0:ℝ≥0)) (𝓝 p) :=
 ((DFunLike.congr_fun S.eZero p) ▸ (S.continuousE p).tendsto 0).mono_left nhdsWithin_le_nhds
lemma light_invariant (t:MarkType V)(x:D)(h:x.1∈ Q): (B.activate t x).val∈ Q:=by
 rw [← orthogonal_orthogonal (Q)]; refine (mem_orthogonal' _ _).2 (fun i g=>?_)
 let f(s:ℝ≥0):= inner ℂ (B.activate t x).val (T s i);
 refine tendsto_nhds_unique (f:=f) ((tendsto_const_nhds (x:=(B.activate t x).val)).inner (warmth_visits i)) (tendsto_const_nhds.congr' ?_)
 filter_upwards [self_mem_nhdsWithin] with s hs
 let y:D:= ⟨T s i, heat_domain S i hs⟩; exact (Eq.trans (B.sharp J z t x y) (inner_right_of_mem_orthogonal h (B.dark_invariant J z (opTag J t) y (B.registeredAway (costT S s) i g)))).symm
-- Exact-stove read used at ANY genuine Pad with phi.
lemma photon (v:V) (s:ℝ≥0) (p:0<s) (f:Test4) (x:D)(h:x.val∈Q): (B.blue v s f x).val∈ Q:=by
 rw [B.blue_stove v s p]; exact B.warmMoves s _ (B.light_invariant J z (v,f) (stoveAt S s x) (B.warmMoves s _ h))
lemma urges (v:V)(s:ℝ≥0)(p:0<s)(f:Test4)(x:H)(h:x∈ Q) : valise S (B.bar s v) f x∈ Q:=by
 refine B.inH.isClosed_topologicalClosure.mem_of_tendsto ((valise S (B.bar s v) f).continuous.tendsto _|>.comp (warmth_visits (S:=S) x)) ?_
 filter_upwards [self_mem_nhdsWithin] with t ht; let X:D:=⟨T t x, heat_domain S x ht⟩; change valise S (B.bar s v) f X.val∈ B.pointShelf; rw [←B.blue_apply]; exact B.photon J z v s p f X (B.warmMoves t x h)
omit z in
private lemma touched (g h : E4 → ℂ) (pg : Continuous g) (ph : Continuous h)
    (ht : ∀ f : Test4, (∫ x, f x * g x) = ∫ x, f x * h x) : g = h := by
  refine Measure.eq_of_ae_eq (μ := volume) (ae_eq_of_integral_contDiff_smul_eq
    pg.locallyIntegrable ph.locallyIntegrable ?_) pg ph
  intro f hf hf'
  let t : Test4 := (hf'.comp_left (show Complex.ofReal 0=0 by simp)).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hf)
  simpa only [Complex.real_smul, show (t : E4 → ℂ) = (fun x => (f x : ℂ)) from rfl] using ht t
lemma bar_invariants (v:V)(s:ℝ≥0)(p:0<s)(x:H)(h:x∈ Q) : B.bar s v x∈ B.pointShelf:=by
 rw [←orthogonal_orthogonal (Q)]; intro i hi
 let F(q:E4):= inner ℂ i (optx S (B.bar s v) q x); have hc:Continuous F:= continuous_const.inner (village S x (B.bar s v))
 have hF:= touched F (fun _=>0) hc continuous_const (?_); swap
 · intro f; let A:= B.bar s v; rw [show (∫ y,f y*F y)= _ from sell_in S i x A f]; simp only [mul_zero, integral_zero]; exact inner_left_of_mem_orthogonal (B.urges J z v s p f x h) hi
 have hp:F 0=0:= congrFun hF 0; unfold F at hp; rw [vroot] at hp; exact hp
lemma bar_exteriors (v:V)(s:ℝ≥0)(p:0<s)(x:H)(h:x∈ Qᗮ) : B.bar s v x ∈ Qᗮ:=fun i hi=> by rw [← ContinuousLinearMap.adjoint_inner_left,← z.bill]; exact inner_right_of_mem_orthogonal (B.bar_invariants J z _ _ p i hi) h
end YM.SatinWFixed.Carton
