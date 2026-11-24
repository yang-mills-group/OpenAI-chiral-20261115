import Mathlib.MeasureTheory.Function.FactorsThrough
import YM.CF.BProof.Law.Flat
/-! Borel support projection-extension and rotational smoothing. Pointwise.
No assumption that every partial argument has an admissible completion! -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Veil
open Function Filter Lattice Finset NormedSpace MeasureTheory TopologicalSpace
open scoped Topology ContDiff BigOperators InnerProductSpace Classical
variable {s:Side}{D X:Type*}[m:MeasurableSpace D][n:MeasurableSpace X]
abbrev geo(s:Side):=Site s→ SU.E -- ambiguity import
structure RecN(s:Side)(D:Type*)[MeasurableSpace D] where
 snap: Support s→D→ D
 act: geo s→ D→D
 one(x):act 1 x=x
 comp(g h x):act (g*h) x=act g (act h x)
 trace_h {S T:Support s}:T ⊆ S →∀ {x y}, snap S x=snap S y→ snap T x=snap T y
 tw {S} (g) {x y} : snap S x=snap S y → snap S (act g x)=snap S (act g y)
 hol(T): Measurable (snap T)
 spin: Measurable (uncurry act)
namespace RecN
variable (p:RecN s D)(q:RecN s X)
def together : RecN s (D×X):=⟨fun S u=>(p.snap S u.1,q.snap S u.2),fun g u=>(p.act g u.1,q.act g u.2),fun x=>Prod.ext (p.one x.1) (q.one x.2), fun i j x=> Prod.ext (p.comp ..) (q.comp ..),@fun T S f x y h=>Prod.ext (p.trace_h f (congrArg Prod.fst h)) (q.trace_h f (congrArg Prod.snd h)),@fun _ g x y h=>Prod.ext (p.tw g (congrArg Prod.fst h)) (q.tw g (congrArg Prod.snd h)),fun i=> ((p.hol i).comp measurable_fst).prodMk ((q.hol i).comp measurable_snd), by apply Measurable.prodMk; exact p.spin.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd)); exact q.spin.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))⟩
def agree(S: Support s)(x y:D):Prop:= p.snap S x=p.snap S y
lemma onwards {S T:Support s}{x y:D}(h:p.agree T x y)(g:S ⊆ T): p.agree S x y:=p.trace_h g h
lemma waved {S:Support s}{x y:D}(h:p.agree S x y)(g:geo s):p.agree S (p.act g x) (p.act g y):=p.tw g h
structure TagF {T:Support s}(v:D→ℂ)(h:ℝ):Prop where
 pos:0≤h
 borel:Measurable v
 pays(x):‖v x‖≤h
 ruled{x y}: p.agree T x y→ v x=v y
def fixed(v:D→ℂ):=∀ g x,v (p.act g x)=v x
-- support extensions by projection and factoring lemma
lemma wid {c:ℝ}(hc:0≤c)[StandardBorelSpace D][StandardBorelSpace X] (T:Support s)(ρ:X→ D)(e:Measurable ρ)(v:X→ℂ)(u:Measurable v)(b:∀ i,‖v i‖≤c)(t:∀ x y,p.agree T (ρ x) (ρ y) → v x=v y) : ∃ ν:D→ℂ, TagF p (T:=T) ν c ∧∀ x,ν (ρ x)= v x:=by
 let w:=p.snap T; let f:=w ∘ ρ
 have ht:Measurable f:= (p.hol T).comp e
 have he:Measurable[m.comap f] v:=by
    letI := upgradeStandardBorel D
    intro A hA; let S:= v⁻¹' A; let U:=f '' S; let B:=f '' Sᶜ; have hs: MeasurableSet[n] S:= u hA
    have hd:Disjoint U B:= by rw [Set.disjoint_left]; rintro i ⟨j,a,rfl⟩ ⟨l,h,g⟩; apply h; unfold S; rw [Set.mem_preimage, t l j g]; exact a
    obtain ⟨k,H,L,V⟩:= (hs.analyticSet_image ht).measurablySeparable (hs.compl.analyticSet_image ht) hd
    refine ⟨k,V,?_⟩; ext i; constructor; intro a; by_contra b; exact Set.disjoint_left.mp L (Set.mem_image_of_mem f (show i∈ Sᶜ from b)) a; exact fun c=>H (Set.mem_image_of_mem f c)
 obtain ⟨v,hv,h⟩:= he.exists_eq_measurable_comp; -- tune shadow
 let G(x:D) := if ‖v (w x)‖≤c then v (w x) else 0; refine ⟨G,⟨hc, Measurable.ite ?_ (hv.comp (p.hol _)) measurable_const,?_,?_⟩,?_⟩; · exact measurableSet_le ((hv.comp (p.hol T)).norm) measurable_const
 · intro i; unfold G; split; assumption; rw [norm_zero]; exact hc
 · intro x y h; unfold G; rw [show w x=w y from h]
 intro x; rw [h]; have hz:= b x; rw [h] at hz; exact if_pos hz
end RecN
-- normalized Haar site-rotations
abbrev luke(s:Side):Measure (geo s):= Measure.pi (fun _=>SU.group.probHaar)
instance : IsProbabilityMeasure (luke s):= by unfold luke; infer_instance
lemma rollL(g:geo s) : MeasurePreserving (fun h=>h*g) (luke s) (luke s):= measurePreserving_pi (fun _=>SU.group.probHaar) _ (f:=fun i t=>t*g i) (fun _=>measurePreserving_mul_right ..)
namespace RecN
variable (p:RecN s D)(T:Support s){v:D→ℂ}{c:ℝ}(h:TagF p (T:=T) v c)
def varnish (v:D→ℂ)(x:D):ℂ:=∫ g,v (p.act g x) ∂luke s
include T h
lemma colorCost(x:D): Integrable (fun g=>v (p.act g x)) (luke s):= Integrable.of_bound (h.borel.comp (p.spin.comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable c (Eventually.of_forall (fun _=> h.pays _)) -- tune
lemma even : TagF p (T:=T) (p.varnish v) c:=by
 refine ⟨h.pos,?_,fun x=> ?_, @fun x y u=>integral_congr_ae (Eventually.of_forall fun i=>h.ruled (p.waved u i))⟩; · exact (h.borel.comp (p.spin.comp measurable_swap)).stronglyMeasurable.integral_prod_right'.measurable -- tune
 unfold varnish; apply (norm_integral_le_integral_norm _).trans; rw [← show (∫ _ : geo s,c ∂luke s)=c from (by simp)]; exact integral_mono ((p.colorCost T h _).norm) (integrable_const _) (fun i=>h.pays _)
omit T h in
lemma evenFix : fixed p (p.varnish v):=by
 intro g x; unfold varnish; simp_rw [←p.comp]; exact (rollL g).integral_comp ((Homeomorph.mulRight g).measurableEmbedding) (fun g=>v (p.act g x))
lemma evenFree (x:D)(t:∀ g,v (p.act g x)=v x): (p.varnish v) x=v x:=by simp [varnish,t]
omit T h
lemma varnishList {U:Type*}[Fintype U](f:U→D→ℂ)(b:U→ℝ)(T:U→Support s)(x:D)(l:∀ i,TagF p (T:= T i) (f i) (b i))(k:∀ g,∑ i,f i (p.act g x)=∑ i,f i x): (∑ i,p.varnish (f i) x)=∑ i,f i x:=by
 unfold varnish; rw [←integral_finsetSum]; simp_rw [k]; simp; exact fun i _=>p.colorCost _ (l i) x
end RecN
end YM.CF.BProof.Veil
