import YM.SU5.Registration.Affine.Momentum
/-!
  # The Euclidean, late-consultation fields over our M4 map
  Unprojected ColorHil -> G uses coherence of this same elected character. G
  has powers w.r.t. actual physical clock, not arbitrary GNS Hilbert built per axis.
  Work with WPermit estimates on ANY stamped family with coefficients at its
  native printed height. Use to compute Schwinger prices and ordered transfer.
  Projection in pricing sharp readings from G is only qualified where authorized
  (`Ellis` & all-coordinate separations etc.).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
open SatinRegistration
namespace Spine
variable (P:Spine)
-- geometry ANY axes
local notation "Χ"=>P.Spectrum0
local notation "Θ"=>P.advocate 3
local notation "E₀"=>P.ColorHil
local notation "H₀"=>P.ManyF
local notation "qz"=>P.wealth
local notation "S₀"=>P.seasons
variable (x:P.Spectrum0 3)(a:Axis)
local notation "ξ"=>Θ x a
local notation "S"=>(P.seasons a (P.advocate 3 x a))
local notation "H"=>(P.ColorHil a (P.advocate 3 x a))
local notation "G"=>(P.ManyF a (P.advocate 3 x a))
local notation "pc"=>P.cartage a (P.advocate 3 x a)
local notation "T₀"=> (S).E
local notation "Ω"=> P.heaven a ξ
local notation "T"=> timeMesh P.par
open Swatch
-- word specified by arbitrary FINITE list & interpretation. Can repeat FIELD symbols but placements unique inside a strict order. Estimates simultaneous at that constellation; any choices of outer cuts strictly afford.
variable {I:Type*}(L:List I)(p:I→Vantage)
abbrev LightsCross := L.Pairwise (fun i j=> p i a<p j a)
abbrev Dressing (f g:I→ℝ) : Prop:= (∀ i∈L,f i<p i a ∧ p i a<g i)∧ ∀ a b t U,L=t++a::b::U → g a=f b
lemma sews [DecidableEq I] (h:LightsCross a L p) : ∃ f g,Dressing a L p f g:=by
 obtain ⟨V⟩:=choose_curtains (fun i=>p i a) (fun i=>p i a) L (h.imp (fun c p=>by rcases p with rfl; exact lt_irrefl _ c)) (weaves_sorted _ _ L h); exact ⟨V.first,V.last,fun i p=>⟨V.inside i p,V.outside i p⟩,V.joins⟩
lemma space_clear : IsOpen (setOf (LightsCross a L)):=by
 classical
 induction L with
 | nil=> rw [show setOf (LightsCross a ([] : List I))=Set.univ from eq_univ_of_forall (fun x=>List.Pairwise.nil)]; exact isOpen_univ
 | cons i l h=>
   let f:= setOf (LightsCross a l)
   let g(j:I):Set (I→Vantage):={p|p i a<p j a}
   have he: setOf (LightsCross a (i::l))=f∩⋂ j∈l.toFinset, g j:= by ext p; simp [LightsCross,f,g,and_comm]
   rw [he]; exact h.inter (isOpen_biInter_finset (fun j _=> isOpen_lt ((continuous_apply a).comp (continuous_apply i)) ((continuous_apply a).comp (continuous_apply j))))

/- Concatenate entries across one chart. RealPrice, possibly illegal outside it. -/
-- b:H'.Op projected. transport H isol. L only with strict clocks. Can later propagate cut formula independent.
variable (A:I→P.Swatch)
local notation "l̂" f:max=> f
local notation "SC" => P.Spectrum0 3
abbrev ChartOp (A:I→ℝ≥0→(P.ManyF a (P.advocate 3 x a)).Op)(p:I→Vantage)(f g:I→ℝ) : (G).Op:= (L.map (fun i=>P.orbitCut x a (A i) (f i) (g i) (p i))).prod
noncomputable def ChartPrice (B:I→ℝ≥0→(P.ManyF a (P.advocate 3 x a)).Op)(p:I→Vantage)(f g:I→ℝ):ℂ:= inner ℂ Ω (P.ChartOp x a L B p f g Ω)
abbrev RawOp (p:I→Vantage)(f g:I→ℝ)(σ:I→ℕ) : (G).Op:= (L.map (fun i=>(A i).scoop P x a (f i) (g i) (p i) (σ i))).prod
noncomputable def RawPrice (p:I→Vantage)(f g:I→ℝ)(σ:I→ℕ):ℂ:= inner ℂ Ω (P.RawOp x a L A p f g σ Ω)

noncomputable def Ancestral (p:I→Vantage)(σ:I→ℕ):ℂ:= (L.map fun i=> (A i).rate (σ i)).prod * P.memorial a (P.advocate 3 x a) (fun i=> (A i).fieldA (σ i)) L p
variable (v:∀ i,(A i).WPermit x a)
local notation "W"=>fun i=>(v i).atHeat -- parent use
variable (f g:I→ℝ)
local notation "Aσ" σ:max=> (fun i=> (A i).fieldA (σ i))
local notation "D'" p:max=> Dressing a L p f g
local notation "Lw" σ:max i:max=> (A i).fieldA (σ i)
abbrev WClassic (p:I→Vantage)(σ:I→ℕ):Prop:=(∀ i∈L,f i<P.porchY a (Aσ σ) p i ∧ P.resignY a (Aσ σ) p i<g i) ∧ ∀ a b t U,L=t++a::b::U → g a=f b
lemma classical_late {ι:Type*} (F₀:Filter ι){σ:ι→I→ℕ}(h:∀ i∈L,Tendsto (fun k=>σ k i) F₀ atTop){Y:ι→I→Vantage}(p0:∀ i∈L,Tendsto (fun j=>Y j i) F₀ (𝓝 (p i)))(z:Dressing a L p f g) (u:∀ i∈L,(A i).Finishes) : ∀ᶠ i in F₀,P.WClassic a L A f g (Y i) (σ i) :=by
 classical
 let F(i:I)(j:ι):= ((Lw (σ j) i).realWidth P a)
 -- uniform finite. parse notation Y conflict! remove notation up there L should filter ℕ
 have he(i:I)(c:i∈L): Tendsto (F i) F₀ (𝓝 0):=by
    unfold F; simp_rw [Apron.width_real]; exact NNReal.tendsto_coe.mpr ((u i c a).comp (h i c))
 let wC(i:I)(k:ι):Prop:= f i<P.porchY a (Aσ (σ k)) (Y k) i ∧ P.resignY a (Aσ (σ k)) (Y k) i < g i -- shadows p BUG
 have hp (i:I)(c:i∈L): ∀ᶠ k in F₀, wC i k:= by
    -- `hf` not use £
    have hX:=tendsto_pi_nhds.mp (p0 i c) a; let ht:= he i c
    filter_upwards [(hX.sub ht).eventually (lt_mem_nhds (by simpa using (z.1 i c).1 : f i<p i a-0)),(hX.add ht).eventually (gt_mem_nhds (by simpa using (z.1 i c).2 : p i a+0<g i))] with k u v
    exact ⟨u,v⟩
 refine ((L.toFinset.eventually_all).2 (fun i c=> hp i (List.mem_toFinset.mp c))).mono fun i hx=> ⟨fun k b=> hx k (List.mem_toFinset.mpr b),z.2⟩
-- note new universe prop argument parent P etc.

private lemma scaled_product {I:Type*}{H':Hilbert}(L:List I)(MZ:I→H'.Op)(Q:I→ℂ) : (L.map (fun i=> Q i • MZ i)).prod = (L.map Q).prod • (L.map MZ).prod:=by
 induction L with
 | nil=> exact (one_smul ℂ _).symm
 | cons i l h=> simp only [List.map_cons,List.prod_cons,h, Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul]; rw [mul_comm _ (Q i)]
lemma raw_classical (p':I→Vantage)(σ:I→ℕ)(h:P.WClassic a L A f g p' σ): P.RawPrice x a L A p' f g σ=P.Ancestral x a L A p' σ:=by
 unfold RawPrice RawOp Ancestral Swatch.scoop; rw [scaled_product,ContinuousLinearMap.smul_apply, inner_smul_right,P.pill_memorial a ξ _ L p' f g h.1 h.2]
lemma chart_prod (G':Hilbert){X:ℕ→I→G'.Op}(A:I→G'.Op)(h:∀ i∈L,Flying (fun n=>X n i) (A i)) : Flying (fun i:ℕ=> (L.map (X i)).prod) ((L.map A).prod):=by
 induction L with
 | nil=> exact Flying.still _
 | cons i l p=> simp only [List.map_cons,List.prod_cons]; exact (h i (List.Mem.head ..)).multiply (p fun i e=> h i (List.Mem.tail _ e))
-- purchase faster if all in frame share index (then anywhere later for actual widths). Here support independent (via moving σ). Use proof of stage_limit & amend with reindex
lemma flight_variants (H':Hilbert){X:ℕ→H'.Op}{V:H'.Op}(h:Flying X V){f:ℕ→ℕ}(p:Tendsto f atTop atTop) : Flying (X∘ f) V:=fun x=>⟨ (h x).1.comp p,(h x).2.comp p⟩
lemma variant_pose (A:P.Swatch)(u:A.WPermit x a) {p:Vantage}{b:ℕ→Vantage}(t:Tendsto b atTop (𝓝 p)) {f g:ℝ}(r:f<p a)(e:p a<g){σ:ℕ→ℕ}(v:Tendsto σ atTop atTop): Flying (fun i=> A.scoop P x a f g (b i) (σ i)) (u.sees P x a f g p) :=by
 let d:=min (p a-f).toNNReal (g-p a).toNNReal; let y:=d/2; have hz:0<(p a-f).toNNReal:=Real.toNNReal_pos.mpr (sub_pos.mpr r); have hz':0<(g-p a).toNNReal:=Real.toNNReal_pos.mpr (sub_pos.mpr e); have hp:0<d:= lt_min hz hz'; have hu:y<(p a-f).toNNReal:= (half_lt_self hp).trans_le (min_le_left ..); have hh:y<(g-p a).toNNReal:=(half_lt_self hp).trans_le (min_le_right ..); have z:0<y:=half_pos hp
 have h:=tendsto_pi_nhds.mp t a; have hx:Tendsto (fun i=> Real.toNNReal ((b i) a-f)) atTop (𝓝 ((p a-f).toNNReal)):=continuous_real_toNNReal.continuousAt.tendsto.comp (h.sub_const _); have hy:Tendsto (fun i=> Real.toNNReal (g-(b i) a)) atTop (𝓝 ((g-p a).toNNReal)):=continuous_real_toNNReal.continuousAt.tendsto.comp ((tendsto_const_nhds (x:=g)).sub h)
 unfold WPermit.sees; rw [P.orbitCut_precise x a _ u.delivery.isSound f g p y z hu.le hh.le]
 apply Flying.late (((Flying.heat S (hx.sub_const y)).multiply (P.cane_flies x a t (flight_variants G (u.arriving _ z) v))).multiply (Flying.heat S (hy.sub_const y)))
 filter_upwards [v.eventually ((u.thin a).eventually (ge_mem_nhds z)),hx.eventually (le_mem_nhds hu),hy.eventually (le_mem_nhds hh)] with i x' u h'
 exact (A.precision P x a f g (b i) (σ i) y x' ((Real.le_toNNReal_iff_coe_le' z).1 u) ((Real.le_toNNReal_iff_coe_le' z).1 h')).symm
include v
lemma chart_flies (h:Dressing a L p f g){σ:ℕ→I→ℕ}(t:∀ i∈L,Tendsto (fun k=>σ k i) atTop atTop){q:ℕ→I→Vantage}(u:∀ i∈L,Tendsto (fun k=> q k i) atTop (𝓝 (p i))) : Flying (fun i=> P.RawOp x a L A (q i) f g (σ i)) (P.ChartOp x a L W p f g):=by apply chart_prod; intro i e; exact P.variant_pose x a (A i) (v i) (u i e) (h.1 i e).1 (h.1 i e).2 (t i e)

lemma ancestry_flies (h:Dressing a L p f g){σ:ℕ→I→ℕ}(t:∀ i∈L,Tendsto (fun k=>σ k i) atTop atTop){q:ℕ→I→Vantage}(u:∀ i∈L,Tendsto (fun k=> q k i) atTop (𝓝 (p i))) : Tendsto (fun i=> P.Ancestral x a L A (q i) (σ i)) atTop (𝓝 (P.ChartPrice x a L W p f g)):=by
 have he:Tendsto (fun i=>P.RawPrice x a L A (q i) f g (σ i)) atTop (𝓝 (P.ChartPrice x a L W p f g)):= tendsto_const_nhds.inner ((P.chart_flies x a L p A v f g h t u) Ω).1
 exact he.congr' ((P.classical_late a L p A f g atTop t u h (fun i _=> (v i).thin)).mono fun i w=> P.raw_classical x a L A f g _ _ w)
lemma history_price_independent (f' g':I→ℝ)(t:Dressing a L p f g)(p0:Dressing a L p f' g') : P.ChartPrice x a L W p f g=P.ChartPrice x a L W p f' g':=by
 let σ(n:ℕ)(_ : I):=n; exact tendsto_nhds_unique (P.ancestry_flies x a L p A v f g t (σ:=σ) (fun _ _=>tendsto_id) (q:=fun _=>p) (fun _ _=>tendsto_const_nhds)) (P.ancestry_flies x a L p A v f' g' p0 (fun _ _=>tendsto_id) (fun _ _=>tendsto_const_nhds)) -- tune call using `q` explicitly
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.classical_late
#print axioms Spine.variant_pose
#print axioms Spine.ChartPrice
#print axioms Spine.Ancestral
#print axioms Spine.ancestry_flies
#print axioms Spine.history_price_independent
