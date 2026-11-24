import YM.SU5.Selected.Pack.Wine

/-! # Mollifying the pricing frame at BOTH halves

Sharp Ward at each visiting pair (Pay). Independent gauge shifts are allowed on the two
positions, because supports are disjoint. Use for variance since `Voucher` represents
`molasses (frame-1)`, not the unshifted mark. Compass actually integrates *these* words,
with no prices/E substituted until after registration. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option maxHeartbeats 420000
noncomputable section
namespace YM.CF.Pannier.Chancel.Survival
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Cliplet RG Brace Scree
open Window (mem_Tset family)
open Py.Rate.Pannier Lifted Push.SectorMeasure
open Reed (Fine)
open Afterglow
open Haro Tap Cascade Dial Mir Girt Nacre Pastry Phase RP Advance Tapestry
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {n:Side}{T:Finset (Seat n)} (j:Axis) {F:Mark n}
local notation "ρ" => reflMark j 0
private lemma trueCover (K : Calibration) (S : Finset Cover) (m : Side) (t:n=K.c m)
    (x:AtSupport false (Satin.region S n) F)(p: Roomy S n) (g u: Zodiac n)
    (h : ∀ i ∈ Satin.region S n,u i=g i) :
    AtSupport false (Satin.region S n) (getBack F g) ∧ Harmony u F (getBack F g) := by
 subst n
 -- family existence via render at m
 obtain ⟨f,q,e⟩:= show ∃ f: Buffered.Family K, InTest K true S false f∧f m=F from ⟨render S K (mend S K m p x),texture ..,appear_mend S K m p x⟩ -- order
 subst F
 let G:=g ∘ wrap (More (K.c m)); have ht: TraceGauge S G g:=fun _ _=>rfl
 obtain ⟨F,v,l⟩:= reColor G q
 have he:getBack (f m) g=F m:=funext fun i=> (twist (atelier g)).injective ((trueBack (f m) g i).symm.trans (l m g ht i))
 rw [he]; exact ⟨v.support m,l m u (fun i p=>h _ (mem_image_of_mem _ p))⟩
private lemma multiplies {F G V W: Mark n} (u:Zodiac n) (p:Harmony u F G) (q:Harmony u V W) : Harmony u (F*V) (G*W):= by intro x; change F _*V _=twist _ (G _ * W _); rw [p x,q x,map_mul]
private lemma swap_v {n:Side} (x:Seat n): (plane j 0).anon n ((plane j 0).anon n x)=x:= by
 -- alias lemma?
 exact fling_there j 0 x
lemma separated_harmony (K : Calibration) (S : Finset Cover) (m : Side) (t:n=K.c m)
    (p : Roomy S n) (f : AtSupport false (Satin.region S n) F)
    (q:Disjoint (hyphen j 0 (Satin.region S n)) (Satin.region S n)) (u v:Zodiac n) :
    ∃ g: Zodiac n,Harmony g (ρ F * F) ((ρ (getBack F u))*getBack F v) := by
 let S':=Satin.region S n; let A:= (plane j 0).anon n
 let g: Zodiac n:= fun i=>if i∈ S' then v i else u (A i)
 have h: ∀ i∈S',(g ∘ A) i=u i:= fun i p=> by
    have h:A i∉S':= fun e=>Finset.disjoint_left.mp q (mem_image_of_mem _ p) e
    change (if _ then _ else _)=_; rw [if_neg h,show A (A i)=_ from swap_v j i]
 have t':= trueCover K S m t f p u (g∘A) h
 exact ⟨g,multiplies g (reflectHarmony j 0 t'.2 t'.1) (trueCover K S m t f p v g (fun i hl=> if_pos hl)).2⟩
private def θ₀ : FC (Single n)→L[ℝ] FC (Single n) := LinearMap.toContinuousLinearMap
  (⟨⟨theta (carR j 0 n),theta_add _⟩,fun c x=> theta_rsmul _ x c⟩ : FC (Single n) →ₗ[ℝ] FC (Single n))
-- Mark blend distributes all supported vols.
private def stamp (x: Phys n): FC (Single n)→L[ℂ] ℂ := LinearMap.toContinuousLinearMap (⟨⟨fun y=>letterRead y x,fun y z=> (mark_linear y z x 0).1⟩, fun c z=> (mark_linear z 0 x c).2⟩ : FC (Single n)→ₗ[ℂ] ℂ)
def boiled (f: Zodiac n→ Mark n) : Mark n:= fun x=> ∫ g,f g x ∂domeLaw n
lemma course_boil (f: Zodiac n→ Mark n) (w:Continuous f.uncurry)
    (l:Loom n)(t:Measurable l)(V:Orbit n→Phys n)(g: Integrable V (city n)) (q:ℂ):
    markedRead (boiled f) l V / q=∫ g, markedRead (f g) l V/q∂domeLaw n := by
 obtain ⟨C,h⟩:= (Env.compact w).cost
 let μ:=domeLaw n; let ν:=city n; let τ:= (domeLaw n).prod ν
 let Z (g:Zodiac n)(x:Orbit n):=f g (drawn l x)
 let X(a:Zodiac n)(x:Orbit n):=letterRead (Z a x) (V x)
 have ht (x:Fields n): Integrable (fun a : Zodiac n=> f a x) μ:= (w.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
 have hp : Integrable X.uncurry τ:=by
    have hY: Integrable (fun i:Zodiac n × Orbit n=> V i.2) τ:= Integrable.comp_snd g (domeLaw n); let A(i:FC (Single n)×Phys n):= letterRead i.1 i.2; have hx:Continuous A:= (beamL n).continuous.comp ((acts_cont.comp continuous_fst).clm_apply continuous_snd)
    have hf:AEStronglyMeasurable Z.uncurry τ:= (w.measurable.comp (measurable_fst.prodMk ((drawn_m l t).comp measurable_snd))).aestronglyMeasurable
    apply (hY.norm.const_mul C).mono' (hx.comp_aestronglyMeasurable (hf.prodMk hY.aestronglyMeasurable)); apply Filter.Eventually.of_forall; rintro ⟨a,b⟩; exact (mark_bound (Z a b) (V b)).trans (mul_le_mul_of_nonneg_right (h (a,_)) (norm_nonneg _))
 rw [integral_div]; apply congrArg (fun w:ℂ=>w/q); change (∫ x, stamp (V x) (∫ z, Z z x∂μ) ∂ν)= (∫ z, ∫ x, X z x ∂ν ∂μ); rw [integral_integral_swap hp]; exact integral_congr_ae (Filter.Eventually.of_forall (fun x=> ((stamp (V x)).integral_comp_comm (ht _)).symm))
-- class of bilinear pricing on both z's
variable {F F' : Mark n}
-- generic equality for melt (helps elaboration with non-Euclidean metrics)
private lemma blend_equal {X T R:Type} [TopologicalSpace X] [TopologicalSpace T][MeasurableSpace T][OpensMeasurableSpace T]
    [CompactSpace T][T2Space T][SecondCountableTopology T] [NormedRing R][NormedAlgebra ℝ R][CompleteSpace R]
    {f:(X→R)→ℂ}(μ:Measure T) [IsProbabilityMeasure μ](x y:X→R)(a b:T→X→R)
    (hp:∀ k:T→X→R,Continuous k.uncurry→ f (fun i=>∫ t,k t i∂μ)=∫ t,f (k t)∂μ)
    (hv:Continuous y) (u:Continuous a.uncurry)(v:Continuous b.uncurry)(t:∀ i,x i=∫ j,a j i∂μ)(k:∀ i,y i=∫ j,b j i∂μ)
    (L:ℂ)(p:∀ i j,f (a i*b j)=L): f (x*y)=L := by
 have ht (x:T): f (a x*y)= L:=by
    let g (i:T):= a x * b i
    have hg : Continuous g.uncurry := ((u.comp (continuous_const.prodMk (continuous_id (X:=X)))).comp continuous_snd).mul v -- expected Continuous g uncurry but norm.tc using equality
    have he : a x*y= fun i:X=>∫t,g t i∂μ:= funext fun i=> (congrArg (fun z=> a x i * z) (k i)).trans
      ((ContinuousLinearMap.mul ℝ R (a x i)).integral_comp_comm (φ:=fun t=> b t i) ((v.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).symm
    rw [he,hp g hg]; simp_rw [show ∀i, f (g i)=L from fun i=>p x i]; simp
 let g (i:T):= a i*y
 have he : x*y= fun i:X=>∫t,g t i∂μ:= funext fun i=> (congrArg (fun z=> z * y i) (t i)).trans
      (((ContinuousLinearMap.mul ℝ R).flip (y i)).integral_comp_comm (φ:=fun t=> a t i) ((u.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).symm
 have hg: Continuous g.uncurry:= u.mul (hv.comp continuous_snd)
 rw [he,hp g hg]; unfold g; simp_rw [ht]; simp
private lemma integration_price(p:Continuous F)(x:Fields n): Integrable (fun g:Zodiac n=> getBack F g x) (domeLaw n) := ((costsBack F p).comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
private lemma reflect_f : Continuous (reflFields (n:=n) j 0) := Continuous.prodMap (fling_cont j 0 (n:=n)) (fling_cont j 0 (n:=n))
private lemma cheaper_comp {X Y Z:Type} [TopologicalSpace X][TopologicalSpace Y][TopologicalSpace Z](f:X×Y→Z)(g:Z→Z)(P:Y→Y)(h: Continuous f)(t:Continuous g)(p:Continuous P): Continuous (fun w:X×Y=>g (f (w.1,P w.2))) := t.comp (h.comp (continuous_fst.prodMk (p.comp continuous_snd)))
private lemma reflective_budget(p:Continuous F): Continuous (fun w: Zodiac n × Fields n=>ρ (getBack F w.1) w.2):=
 cheaper_comp (X:=Zodiac n ) (Y:=Fields n ) (Z:=FC (Single n)) (Function.uncurry (getBack F)) (theta (carR j 0 n)) (reflFields j 0) (costsBack F p) (theta_cont _) (reflect_f j)
private lemma reflection_pending(p:Continuous F)(x:Fields n): ρ (molasses F) x = ∫ u,ρ (getBack F u) x ∂domeLaw n := ((θ₀ (n:=n) j).integral_comp_comm (integration_price p (reflFields j 0 x))).symm
lemma lawful_both (p:Continuous F)(f:Mark n→ℂ) (H': ∀ g:Zodiac n→Mark n, Continuous g.uncurry→ f (boiled g)=∫ i, f (g i) ∂domeLaw n)
    (q:∀ u v:Zodiac n,f (ρ (getBack F u)*getBack F v)=f (ρ F*F)) : f (ρ (molasses F)*molasses F)=f (ρ F*F):=by
 let χ:= getBack F; let μ:= domeLaw n
 have χt: Continuous χ.uncurry:=costsBack F p
 exact blend_equal (T:=Zodiac n) (X:=Fields n) (R:=FC (Single n)) (f:=f) (domeLaw n) (ρ (molasses F)) (molasses F)
   (fun u=> ρ (χ u)) χ H' (sweet p) (reflective_budget j p) χt (reflection_pending j p) (fun i=>rfl) _ q
lemma add_sugar (p:Continuous F): 1+molasses (F - 1)=molasses F := by
 funext x; change (1:FC (Single n)) + _=_
 unfold molasses; simp_rw [show ∀ u: Zodiac n, getBack (F - 1) u x=getBack F u x-1 from fun u=> by unfold getBack; rw [Pi.sub_apply]; simp]
 rw [integral_sub (f:=fun u=> getBack F u x) (g:=fun (_u: Zodiac n)=> (1:FC (Single n))) (((costsBack F p).comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (integrable_const _)]; simp
end YM.CF.Pannier.Chancel.Survival
