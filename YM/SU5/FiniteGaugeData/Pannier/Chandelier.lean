import YM.SU5.FiniteGaugeData.Pannier.Seedpod
import YM.SU5.FiniteGaugeData.Tapestry.Oriflamme
/-! # Repack: Haar here averages fields of the *actual gauge* at one
period. Keeps singlet identity, Anchor support and bounds; not
another prescription. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Cliplet RG Brace Scree
open Window (mem_Tset family)
open Py.Rate.Pannier
open Lifted
open Push.SectorMeasure
open Reed (Fine)
open Afterglow
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {n:Side}{k:ℕ}{r:Fin k→Site n}{W:Window.Family}{D:Finset (Seat n)}{F:Mark n}
open Tapestry
abbrev Zodiac (n:Side):= Seat n→SU.E
def domeLaw (n:Side):Measure (Zodiac n):= Measure.pi (fun _=> SU.group.probHaar)
instance (n:Side) : Measure.IsMulRightInvariant (domeLaw n):=by unfold domeLaw; infer_instance

instance (n:Side): IsProbabilityMeasure (domeLaw n):=by unfold domeLaw; infer_instance
-- bounding & Harmony with one mark
abbrev atelier (g:Zodiac n):= quantU (tradew n g)
private lemma atelierComm (g:Zodiac n): star (atelier g)=atelier g⁻¹:=by
 unfold atelier; rw [← quantU_star]; let p:=tradew n g; have ht:p*tradew n g⁻¹=1:=by unfold p; rw [Hive.trade_c,mul_inv_cancel,Hive.trade_p] -- defeq unfold p; tune
 exact congrArg quantU (show star p=tradew n g⁻¹ from inv_eq_of_mul_eq_one_right ht)

def getBack (F:Mark n) (g:Zodiac n): Mark n:= fun x=> twist (star (atelier g)) (F (simultaneous g x))
lemma trueBack (F:Mark n)(g:Zodiac n): Harmony g F (getBack F g):=by
 intro x; unfold getBack; have h:=twist_inv (star (atelier g)) (F (simultaneous g x)); rw [star_star] at h; exact h.symm
lemma Back_consistency (F:Mark n)(a b:Zodiac n): getBack (getBack F a) b = getBack F (a*b):=by
 have p:= doubleHarmony (trueBack F a) (trueBack (getBack F a) b); funext x; exact (twist _).injective ((p x).symm.trans (trueBack F (a*b) x)) -- hole not inferred
private lemma sim_cont (n:Side): Continuous fun p: Zodiac n × Pane n=> Lattice.gauge p.1 p.2 := by
 apply continuous_pi; intro i; unfold Lattice.gauge; fun_prop
private lemma bothContour (n:Side) :Continuous (fun p: Zodiac n × Fields n=> simultaneous p.1 p.2):=by
 let f:= @Prod.fst (Zodiac n) (Fields n); have tF:Continuous f:= continuous_fst
 let q:= @Prod.snd (Zodiac n) (Fields n); have tQ:Continuous q:=continuous_snd
 have hx:Continuous (Prod.fst (α:=Pane n) (β:=Pane n) ∘ q):= continuous_fst.comp tQ
 have hu:Continuous (Prod.snd (α:=Pane n) (β:=Pane n) ∘ q):= continuous_snd.comp tQ
 let V₁: Zodiac n × Fields n→ Pane n:=fun p=> Lattice.gauge p.1 p.2.1
 let V₂: Zodiac n × Fields n→ Pane n:=fun p=> Lattice.gauge p.1 p.2.2
 have v:Continuous V₁ := (sim_cont n).comp (f:=fun i=>(f i,(Prod.fst ∘ q) i)) (tF.prodMk hx)
 have w:Continuous V₂ := (sim_cont n).comp (f:=fun i=>(f i,(Prod.snd ∘ q) i)) (tF.prodMk hu)
 exact v.prodMk w
private lemma capsContour (n:Side) : Continuous (fun p: Zodiac n=> (star (atelier p)).val):=by
 let T: Zodiac n→ FC (Single n):=fun p=> (atelier p).val
 have ht:Continuous T:= quant_cont.comp (trade_cont n); exact ht.star
private lemma butter (n:Side)(p:Zodiac n × Fields n)(F:Mark n) : getBack F p.1 p.2= (star (atelier p.1)).val* F (simultaneous p.1 p.2)*star ((star (atelier p.1)).val):= twist_formula ..
lemma costsBack (F:Mark n)(h:Continuous F): Continuous fun p:Zodiac n × Fields n=> getBack F p.1 p.2:=by
 let V: Zodiac n × Fields n→ FC (Single n):=fun p=> (star (atelier p.1)).val; have hu:Continuous V:= (capsContour n).comp continuous_fst; let T:= fun p: Zodiac n × Fields n=> F (simultaneous p.1 p.2); have ht:Continuous T:=h.comp (bothContour n); let W: Zodiac n × Fields n→ FC (Single n) := fun p=> star (V p)
 rw [show (fun p:Zodiac n × Fields n=>getBack F p.1 p.2) = V*T*W from funext (fun p=> butter n p F)]; exact (hu.mul ht).mul hu.star
lemma Back_remembers (p:AtSupport false D F)(a b:Fields n)(h:Agrees D a.1 b.1)(u:Agrees D a.2 b.2)(g:Zodiac n):getBack F g a=getBack F g b:= congrArg (twist (star (atelier g))) (p.dep (simultaneous g a) (simultaneous g b) (make h) (make u))
where make{x y:Pane n}(v:Agrees D x y):Agrees D (Lattice.gauge g x) (Lattice.gauge g y):= fun i u t=> by unfold Lattice.gauge; rw [v i u t]
lemma reserveHap (p:∀ x,F x∈ Hap W r D)(g:Zodiac n)(x:Fields n): getBack F g x∈ Hap W r D:=by rw [getBack,atelierComm g]; exact Hap_germ _ (p _)
def molasses(F:Mark n): Mark n:= fun x=>∫ g,getBack F g x∂ domeLaw n
lemma sweet (p:Continuous F): Continuous (molasses F):=by
 let f(x:Fields n)(g:Zodiac n):=getBack F g x; have ht:=continuous_parametric_integral_of_continuous (μ:=domeLaw n) (f:=f) ((costsBack F p).comp (f:=Prod.swap) (g:=_) continuous_swap) isCompact_univ; simp only [Measure.restrict_univ] at ht; exact ht
lemma Hapsen (p:Continuous F)(b:∀ x,F x∈ Hap W r D)(x:Fields n):molasses F x∈ Hap W r D:=by
 let V:=(Hap W r D).restrictScalars ℝ; refine V.convex.integral_mem V.closed_of_finiteDimensional (Filter.Eventually.of_forall (fun g=>reserveHap b g x)) (((costsBack F p).comp (continuous_id.prodMk (continuous_const (y:=x)))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) -- tune comp
lemma refines (p:Continuous F)(b:∀ x,F x∈ Hap W r D)(w:AtSupport false D F)(x:VolumeX r ⊆ D):AtSupport false D (molasses F):=by
 refine ⟨Env.compact (sweet p),fun a y h u=>?_ , fun y=> Hap_Fine x (Hapsen p b y)⟩; exact integral_congr_ae (Filter.Eventually.of_forall fun g=>Back_remembers w _ _ h u g)
lemma first_cook (w:∀ x y:Fields _,x.1=y.1→ F x=F y)(x y:Fields n)(h:x.1=y.1):molasses F x=molasses F y:= integral_congr_ae (Filter.Eventually.of_forall (fun g=>congrArg (twist (star (atelier g))) (w _ _ (congrArg (Lattice.gauge g) h))))
lemma sweet_budget {C:ℝ}(h:∀ x,‖F x‖≤C)(x:Fields n) : ‖molasses F x‖≤ C:= by
 unfold molasses; refine (norm_integral_le_of_norm_le_const (C:=C) ?_).trans_eq ?_; swap; · simp
 apply Filter.Eventually.of_forall; intro g; unfold getBack; rw [twist_norm]; exact h _
-- rearranging the right Haar translation
private def calmℝ (V:UNI (Single n)): FC (Single n) →L[ℝ] FC (Single n):= LinearMap.toContinuousLinearMap (twist (quantU V)).toAlgEquiv.toLinearMap
lemma preserves_s (p:Continuous F): covariant (molasses F):=by
 intro g x; let U:= getBack F; let N:=domeLaw n; unfold molasses; let X(g:Zodiac n):=U g x
 let Z:FC (Single n) →L[ℝ] FC (Single n):= calmℝ (tradew n g)
 let V(g':Zodiac n):=U g' (simultaneous g x); have h(g':Zodiac n): V g'= Z (X (g'*g)):=by
    unfold V X; have ht:= trueBack (getBack F g') g x; rw [Back_consistency] at ht; exact ht
 change (∫ i, V i∂N)=Z (∫ i,X i∂N); rw [show V=(fun i=>Z (X (i*g))) from funext h, integral_mul_right_eq_self (μ:=domeLaw n) (fun i=> Z (X i)) g]; exact Z.integral_comp_comm (((costsBack F p).comp (continuous_id.prodMk (continuous_const (y:=x)))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

-- melt through one actual course integral (using Fubini for gauge × orbit at that period)
open Haro Tap Cascade Dial Mir Girt Nacre Pastry Phase RP Advance
private def marcu(f:Phys n): FC (Single n)→L[ℂ] ℂ := LinearMap.toContinuousLinearMap (⟨⟨fun x=>letterRead x f,fun x y=> (mark_linear x y f 0).1⟩, fun x y=> (mark_linear y 0 f x).2⟩ : FC (Single n)→ₗ[ℂ] ℂ)
lemma heat_blur (p: Continuous F)(l:Loom n)(t:Measurable l)(V:Orbit n →Phys n)(g:Integrable V (city n)) : markedRead (molasses F) l V=∫ z: Zodiac n, markedRead (getBack F z) l V∂ domeLaw n:=by
 obtain ⟨C,h⟩:= (Env.compact p).cost; let f(a:Zodiac n)(x:Orbit n):= getBack F a (drawn l x); let X(a:Zodiac n)(x:Orbit n):=letterRead (f a x) (V x); let μ:=domeLaw n; let ν:= city n; let τ:= (domeLaw n).prod ν
 have hp : Integrable X.uncurry τ:=by
    have hY: Integrable (fun i:Zodiac n × Orbit n=> V i.2) τ:= Integrable.comp_snd g (domeLaw n); let A(i:FC (Single n)×Phys n):= letterRead i.1 i.2; have hx:Continuous A:= (beamL n).continuous.comp ((acts_cont.comp continuous_fst).clm_apply continuous_snd) -- tune
    have hf:AEStronglyMeasurable f.uncurry τ:= ((costsBack F p).measurable.comp (measurable_fst.prodMk ((drawn_m l t).comp measurable_snd))).aestronglyMeasurable
    apply (hY.norm.const_mul C).mono' (hx.comp_aestronglyMeasurable (hf.prodMk hY.aestronglyMeasurable)); apply Filter.Eventually.of_forall; rintro ⟨a,b⟩; refine (mark_bound (f a b) (V b)).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)); unfold f getBack; rw [twist_norm]; exact h _
 change (∫ x, marcu (V x) (∫ z, f z x∂μ) ∂ν)= (∫ z, ∫ x, X z x ∂ν ∂μ); rw [integral_integral_swap hp]; exact integral_congr_ae (Filter.Eventually.of_forall (fun x=>by let y:=drawn l x; exact ((marcu (V x)).integral_comp_comm (((costsBack F p).comp (continuous_id.prodMk (continuous_const (y:=y)))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).symm))
end YM.CF.Pannier.Chancel
#print axioms YM.CF.Pannier.Chancel.heat_blur
#print axioms YM.CF.Pannier.Chancel.preserves_s
