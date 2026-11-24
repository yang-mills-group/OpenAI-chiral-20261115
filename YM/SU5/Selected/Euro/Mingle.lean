import YM.SU5.Selected.GaugeDescent
import YM.SU5.Selected.Euro.Ether

/-! # Apply averaging at *every* selected rank. Need not ANY relation across I/V/D other than
actual `Universal` here; averaging cost in total variation at sharp normalized arms then ν pair equality.
Also compact Ward on χ through this same E later. This lemma works on nonsmooth marks as far as
Tapestry allows (the envelope required is Borel and bounded actually!). -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 240000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Selection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
open RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
open scoped InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock
open Vacancy

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b)
  (Qc : Clipped Y H (i ∘ a) (k ∘ b))
  (j : Axis) (C : Arena Y H Q.circuit j 0 false)

open Tapestry
namespace Mingle
open Haro Tap Cascade Dial Nacre Pastry
variable {n:Side}
private def stamp (x: Phys n): FC (Single n)→L[ℂ] ℂ := LinearMap.toContinuousLinearMap (⟨⟨fun y=>letterRead y x,fun y z=> (mark_linear y z x 0).1⟩, fun c z=> (mark_linear z 0 x c).2⟩ : FC (Single n)→ₗ[ℂ] ℂ)
def boiled {ζ:Type*}[MeasurableSpace ζ] (μ:Measure ζ) (f: ζ→ Mark n) : Mark n:= fun x=> ∫ g,f g x  ∂μ
lemma course_boil {ζ:Type*}[MeasurableSpace ζ] (f: ζ→ Mark n) (w:Envelope f.uncurry) (μ:Measure ζ) [IsProbabilityMeasure μ]
    (l:Loom n)(t:Measurable l)(V:Orbit n→Phys n)(g: Integrable V (city n)) (q:ℂ):
    markedRead (boiled μ f) l V / q=∫ g, markedRead (f g) l V/q ∂μ := by
 obtain ⟨C,h⟩:= w.cost
 let ν:=city n; let τ:= (μ).prod ν
 let Z (g:ζ)(x:Orbit n):=f g (drawn l x)
 let X(a:ζ)(x:Orbit n):=letterRead (Z a x) (V x)
 have ht (x:Fields n): Integrable (fun a : ζ=> f a x) μ:= Env.integrableX (Env.along w (measurable_id.prodMk (measurable_const (a:=x)))) μ
 have hp : Integrable X.uncurry τ:=by
    have hY: Integrable (fun i:ζ × Orbit n=> V i.2) τ:= Integrable.comp_snd g (μ); let A(i:FC (Single n)×Phys n):= letterRead i.1 i.2; have hx:Continuous A:= (beamL n).continuous.comp ((acts_cont.comp continuous_fst).clm_apply continuous_snd)
    have hf:AEStronglyMeasurable Z.uncurry τ:= (w.meas.comp (measurable_fst.prodMk ((drawn_m l t).comp measurable_snd))).aestronglyMeasurable
    apply (hY.norm.const_mul C).mono' (hx.comp_aestronglyMeasurable (hf.prodMk hY.aestronglyMeasurable)); apply Filter.Eventually.of_forall; rintro ⟨a,b⟩; exact (mark_bound (Z a b) (V b)).trans (mul_le_mul_of_nonneg_right (h (a,_)) (norm_nonneg _))
 rw [integral_div]; apply congrArg (fun w:ℂ=>w/q); change (∫ x, stamp (V x) (∫ z, Z z x ∂μ) ∂ν)= (∫ z, ∫ x, X z x ∂ν  ∂μ); rw [integral_integral_swap hp]; exact integral_congr_ae (Filter.Eventually.of_forall (fun x=> ((stamp (V x)).integral_comp_comm (ht _)).symm))

open YM.CF.Pannier.Chancel
open Haro Tap Cascade Dial Nacre Pastry
-- cast period qualification for sharp. TapReader only if wanted
variable (s n u : ℕ)
local notation "γₑ" => exhibit Y H s n
local notation "σ" => Journey.sharp Y H s n u
local notation "M₀" => momentm Y n s
local notation "N" => (K).c (momentm Y n s)
local notation "Nt" => side Y n s
section qualification
variable {X : Type*} [MeasurableSpace X] (ν: Measure X) [IsProbabilityMeasure ν]
private lemma qual {F F':Side} (h:F=F')(Q: X→ Mark F)(g:Envelope Q.uncurry)(x: Mark F)(t:x=boiled ν Q):
    arrange _ _ h x=boiled ν (fun i=> arrange _ _ h (Q i)) ∧ Envelope (Function.uncurry (fun i=> arrange _ _ h (Q i))):=by subst F'; exact ⟨t,g⟩
lemma sharp_boiled (U: X→Family (tent Y H))(x:Family (tent Y H))(z: Tapestry.Pay Y s n u)
    (p: Envelope (Function.uncurry (fun g=> U g (momentm Y n s))))
    (h:x (momentm Y n s)= boiled ν (fun g=> U g (momentm Y n s))) :
    σ x=∫ g,σ (U g) ∂ν := by
 let u':X→Mark Nt:=fun i=> γₑ (U i)
 obtain ⟨hx,hz⟩:= qual ν (terrain Y H (Y.ir n) s) (fun g=> U g M₀) p (x M₀) h
 change γₑ x = boiled ν u' at hx; change Envelope u'.uncurry at hz
 simp_rw [actualRead]; rw [hx]; exact course_boil u' hz ν _ ((Y.voyage n).ownership s).paid.bill _ (Marks.can_read _ _ _ _ (Y.each_level n u s z.1 z.2)) _
-- Reflection & right multiplication special need integrable pure (harmony separately)

section Warm
variable {x:Type*}[MeasurableSpace x](ν: Measure x)[IsProbabilityMeasure ν] (K':Calibration)(w:x→ Family K')(f:Family K')
def Warm : Prop:= ∀ m:Side, Envelope (Function.uncurry (fun g=> w g m)) ∧ f m= boiled ν (fun g=> w g m)
private def swapper (n:Side)(j:Axis) (s:ℤ) : FC (Single n)→L[ℝ] FC (Single n) := LinearMap.toContinuousLinearMap
  (⟨⟨theta (carR j s n),theta_add _⟩,fun c x=> theta_rsmul _ x c⟩ : FC (Single n) →ₗ[ℝ] FC (Single n))
variable {ν K' w f}
lemma Warm.mir (u:Warm ν K' w f)(j:Axis)(s:ℤ): Warm ν K' (fun i=> mirror K' j s (w i)) (mirror K' j s f):= by
 intro m; let n₀:=K'.c m; obtain ⟨a,p⟩:=u m; let U:= reflFields (n:=n₀) j s; let V:= swapper n₀ j s
 have hc:Measurable U:= (Continuous.prodMap (fling_cont j s (n:=n₀)) (fling_cont j s (n:=n₀))).measurable
 -- cost reflector. use a.foot
 let A(t:x×Fields n₀):= w t.1 m t.2; let g:x×Fields n₀→ x×Fields n₀:=fun z=> (z.1,U z.2)
 have h: Envelope (fun i:x×Fields n₀=> A (g i)):= Env.along (X:=FC (Single n₀)) (F:=A) a (g:=g) (measurable_fst.prodMk (hc.comp measurable_snd))
 refine ⟨pole_w (fun i=> A (g i)) V V.continuous h, funext fun i=>?_⟩
 change V (f m (U i)) = ∫ t,V (w t m (U i))∂ν; rw [p]; exact (V.integral_comp_comm (μ:=ν) (φ:=fun a=> w a m (U i)) (Env.integrableX (Env.along a (measurable_id.prodMk (measurable_const (a:=U i)))) ν)).symm  -- μ notation conflict
lemma Warm.move (u:Warm ν K' w f)(j:Axis)(s:ℤ): Warm ν K' (fun i=> relocate K' j s (w i)) (relocate K' j s f) := (u.mir j 0).mir j _
lemma Warm.left (u:Warm ν K' w f)(y:Family K')(e:TestFamily K' true y) : Warm ν K' (fun i=> y*w i) (y*f):= by
 intro m; obtain ⟨a,p⟩:=u m; let n₀:=K'.c m; let X'(i: x×Fields n₀):=y m i.2; let Y'(i:x×Fields n₀):=w i.1 m i.2; have hx:Envelope X':= Env.along (e.paid.choose_spec.support m).env measurable_snd
 refine ⟨kitE X' Y' (· * ·) (Continuous.mul continuous_fst continuous_snd) hx a, ?_⟩; funext x; rw [Pi.mul_apply,p]; exact ((ContinuousLinearMap.mul ℝ (FC (Single n₀)) (y m x)).integral_comp_comm (φ:=fun t=> w t m x) (Env.integrableX (Env.along a (measurable_id.prodMk (measurable_const (a:=x)))) ν)).symm
end Warm
end qualification

-- generic usable warm and circular reads specialized to disjoint S,T. Allows relocated supported mark itself AND averaging at the initial positions. derive I, E identities.
variable {S T:Finset Cover}
variable {x x' y:Family (tent Y H)}
section compatible
lemma sharp_gauge (T:Cover→ SU.E)(h:Hosp S ( (K).c (momentm Y n s)))(z: Tapestry.Pay Y s n u)(hg:Circular S T x x') : σ x = σ x':= by
 have ht : N=Nt:= terrain Y H (Y.ir n) s
 obtain ⟨g,p⟩:= scoreTrace T ((ht ▸ h): Hosp S Nt)
 rw [actualRead,actualRead]; exact trueHarmony Y s n u z g (truePrinting _ _ Y H s n hg p)
variable {X: Type*} [MeasurableSpace X] {μ:Measure X} [IsProbabilityMeasure μ]
variable {v:X→Family (tent Y H)}
lemma sharp_admit (z: Tapestry.Pay Y s n u)(h:Hosp (S∪T) ((K).c (momentm Y n s))) (p:Disjoint S T)
    (xV:∀ g, ∃ u:Cover→ SU.E, Circular S u x (v g))(x':Family (tent Y H)) (uV:Warm μ (tent Y H) v x') (hy: InTest K true T false y) : σ (y*x) = σ (y*x'):=by
 let f:X→ Family K:=fun g=>y*v g
 have hv: Warm μ K f (y*x'):= uV.left y (aux_test hy)
 have he(g:X): ∃ t:Cover→SU.E, Circular (S∪T) t (y*x) (f g) := by
    obtain ⟨t,a⟩:= xV g; let c:Cover→ SU.E:=fun i=>if i∈S then t i else 1
    exact ⟨c,(largerGauge subset_union_right (trivial_gauge T c (fun i d=> if_neg (Finset.disjoint_right.mp p d)) hy)).mul c _ (largerGauge subset_union_left (circular_same S t c (fun i g=> if_pos g) a))⟩
 rw [sharp_boiled Y H s n u μ f _ z (hv M₀).1 (hv M₀).2]; simp_rw [show ∀g, σ (f g)=σ (y*x) from fun g=> (sharp_gauge Y H s n u _ h z (he g).choose_spec).symm]; simp
include V in
lemma E_admit (p:Disjoint S T)(xV:∀ g, ∃ u:Cover→ SU.E, Circular S u x (v g))(uV:Warm μ (tent Y H) v x')
    (hx: InTest K true S false x) (hx': InTest K true S false x') (hy : InTest K true T false y) : E s (y*x) = E s (y*x'):= by
 let L:= S∪T; have hu:S⊆L:= subset_union_left; have hg:T⊆L:= subset_union_right
 have he:= V.together s (y*x) (aux_test ((hy.mono hg).mul (hx.mono hu))); have he':= V.together s (y*x') (aux_test ((hy.mono hg).mul (hx'.mono hu)))
 have hi(n:ℕ)(p':Hosp L ((K).c (momentm Y n s))): I s (y*x) n = I s (y*x') n:=by
    apply tendsto_nhds_unique_of_eventuallyEq (he.inner n) (he'.inner n)
    exact (V.pick.pass Y H s n).mono fun j u=> sharp_admit Y H s n _ ⟨u.depth,u.enters⟩ p' p xV x' uV hy
 apply tendsto_nhds_unique_of_eventuallyEq he.periods he'.periods; exact ((V.pick.grow_i.tendsto_atTop).eventually ((momentum Y s).eventually (separates K L))).mono fun i v=> hi _ ⟨v⟩
end compatible
end Mingle
end YM.CF.Buffered.Afterglow.Tower.Selection
namespace YM.CF.Buffered.Afterglow.Tower.Selection.Mingle
#print axioms E_admit
#print axioms Warm.move
end YM.CF.Buffered.Afterglow.Tower.Selection.Mingle
