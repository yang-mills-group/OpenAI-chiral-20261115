import YM.SU5.FiniteGaugeData.Pannier.Chandelier
import YM.SU5.FiniteGaugeData.Tapestry.Oriflamme
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.Ether
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

set_option quotPrecheck false
/-! Borel gauge-average, NOT integrating an arbitrary functional on the Borel sup-norm
Swatch. Need support-local coordinate integration. Resolutions intact. -/
lemma etherBack (F:Mark n)(h:Envelope F): Envelope (getBack F).uncurry:=by
 let V: Zodiac n × Fields n→ FC (Single n):=fun p=> (star (atelier p.1)).val
 have hu:Continuous V:= (capsContour n).comp continuous_fst
 let T:= fun p: Zodiac n × Fields n=> F (simultaneous p.1 p.2)
 have ht:Measurable T:=h.meas.comp (bothContour n).measurable
 let W: Zodiac n × Fields n→ FC (Single n) := fun p=> star (V p)
 obtain ⟨C,w⟩:= h.cost
 refine ⟨?_,C,fun x=>?_⟩
 · rw [show (getBack F).uncurry = V*T*W from funext (fun p=> twist_formula ..)]; exact (hu.measurable.mul ht).mul hu.star.measurable
 change ‖twist _ _‖ ≤ C; rw [twist_norm]; exact w _

private def blast (V: UNI (Single n)): FC (Single n) →L[ℝ] FC (Single n):= LinearMap.toContinuousLinearMap (twist (quantU V)).toAlgEquiv.toLinearMap
lemma preserves_s (p:Envelope F): covariant (molasses F):=by
 intro g x; let U:= getBack F; let N:=domeLaw n; unfold molasses; let X(g:Zodiac n):=U g x
 let Z:=blast (tradew n g)
 let V(g':Zodiac n):=U g' (simultaneous g x); have h(g':Zodiac n): V g'= Z (X (g'*g)):=by
    unfold V X; have ht:= trueBack (getBack F g') g x; rw [Back_consistency] at ht; exact ht
 change (∫ i, V i∂N)=Z (∫ i,X i∂N); rw [show V=(fun i=>Z (X (i*g))) from funext h, integral_mul_right_eq_self (μ:=domeLaw n) (fun i=> Z (X i)) g]; exact Z.integral_comp_comm (Env.integrableX (Env.along (etherBack F p) (measurable_id.prodMk (measurable_const (a:=x)))) N)

section pigments
open Satin Girt
variable (K:Calibration)(S:Finset Cover)(m:Side)(p:Hosp S (K.c m))(f:Swatch S)
include p
local notation "N" m:max => K.c m
abbrev repeats (n:Side) (g:Zodiac n) := g ∘ wrap (More n) -- local notation maybe expands binder type problem?
local notation "Χ" => Zodiac (K.c m)
local notation "T" g:max => repeats (K.c m) g
local notation "μ" => domeLaw (K.c m)
local notation "F" => appear S K m f
local notation "Fₛ" g:max => ocelli K S (T g) f
omit p in
lemma direct (g:Χ): appear S K m (Fₛ g) = getBack F g := funext fun i=> (twist _).injective ((decorates K S (T g) f m g (fun _ _=> rfl) i).symm.trans (trueBack F g i))
lemma hue_cost (i:Evens S): Envelope (fun x:Χ × PairsC=> daub S ((Fₛ x.1) i) x.2):=by
 simp_rw [← eye_readCover S K m p, direct]; let g:= replant S (K.c m)
 let v:Χ×PairsC→Χ×Fields (K.c m):=fun x=>(x.1,replant S (K.c m) x.2)
 let w:= getBack F
 have p':Envelope (fun x:Χ×PairsC=> (w.uncurry (v x))):= Env.along (A:=Χ×Fields (K.c m)) (X:=FC (Single (K.c m))) (etherBack F (appearSupport S K m f).env) (g:=v) (measurable_fst.prodMk ((replant_b S (K.c m)).comp measurable_snd))
 exact pole_w (fun x:Χ×PairsC=> w.uncurry (v x)) (eye S K m p i) (LinearMap.continuous_of_finiteDimensional _) p'

lemma hue_coeff (i:Evens S) : Coeff true S (fun x=>∫ a, daub S ((Fₛ a) i) x ∂μ):= by
 refine ⟨fun _=>by contradiction,Env.marginal (hue_cost K S m p f i) μ,?_⟩; exact fun x y g h=> integral_congr_ae (Eventually.of_forall (fun a=> (authentic S ((Fₛ a) i)).locus _ _ g h))

def naturalHue : Swatch S := fun i=> pigment S (hue_coeff K S m p f i)
local notation "fₛ" => naturalHue K S m p f
variable (l:Side)
lemma allPrint (x:Fields (K.c l)): appear S K l fₛ x=∫ g, appear S K l (Fₛ g) x∂μ:=by
 let y:= Prod.map (onC _) (onC _) x
 simp_rw [appearSpool]; unfold naturalHue; simp_rw [daub_pigment]
 rw [integral_finsetSum]; swap
 · intro i hi; exact (Env.integrableX (Env.along (hue_cost K S m p f i) (measurable_id.prodMk (measurable_const (a:=y)))) μ).smul_const _
 simp_rw [integral_smul_const]
include p
lemma hue_neutral : Neutral K (render S K fₛ) := onceNeutral (texture S K fₛ) p (by
 rw [appearRender,show appear S K m fₛ = molasses (appear S K m f) from funext fun x=>by rw [allPrint]; simp_rw [direct]; rfl]; exact preserves_s (appearSupport S K m f).env)
lemma after_hue (e: Neutral K (render S K f)): fₛ = f:= by
 apply appear_inj S K m p; funext x; rw [allPrint]; simp_rw [direct,show ∀ g:Χ,getBack F g x= F x from fun g=> (twist _).injective ((trueBack F g x).symm.trans (e m g x))]; simp -- note openness
lemma fixed_hue : naturalHue K S m p (naturalHue K S m p f)= naturalHue K S m p f:= after_hue K S m p (naturalHue K S m p f) (hue_neutral K S m p f)

lemma manyHue : Envelope ((fun g=> appear S K l (Fₛ g)) |> Function.uncurry):=by
 change Envelope (fun x:Χ × Fields (K.c l)=> _)
 have h(U:Evens S)(g:Χ):=authentic S ((Fₛ g) U)
 let D(v:Χ×Fields (K.c l)) (i:Evens S):= daub S ((Fₛ v.1) i) (Prod.map (onC (K.c l)) (onC (K.c l)) v.2)
 let Q(i:Evens S):=spool (K.c l) (tagWord S i.val)
 change Envelope (fun x:Χ×Fields (K.c l)=> appear S K l (Fₛ x.1) x.2); simp_rw [appearSpool]
 exact Env.total (X:=FC (Single (K.c l))) (g:=fun i v=> D v i • Q i) univ fun i=> (pole_w (X:=ℂ) (fun v=> D v i) (fun z=> z • Q i) (continuous_id.smul continuous_const) (Env.along (hue_cost K S m p f i) (measurable_fst.prodMk ((((on_cont _).prodMap (on_cont _)).measurable).comp measurable_snd))))
end pigments
end YM.CF.Pannier.Chancel.Ether
namespace YM.CF.Pannier.Chancel.Ether
#print axioms allPrint
#print axioms manyHue
#print axioms hue_neutral
end YM.CF.Pannier.Chancel.Ether
