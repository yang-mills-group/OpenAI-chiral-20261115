import YM.SU5.Registration.Affine.Higher
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
/-!
 # Fields agree at changes of orientation

 Also get whole transfer (words then gauge-support momentum matters). These moment
 prices on the actual elected character — no requiring estimates or even rotation
 along generic configurations to pass these real-axis overlaps. Start all-axis
 estimates on primitive gauge, supplied unconditionally by M7; sell the mixed
 W labels at axis3; combine when all ports for given list.
-/
variable (A:I→P.Swatch)
variable (v:∀ i,(A i).WPermit x a)
local notation "W!"=> (fun i=>(v i).atHeat)
local notation "F!" σ:max=> fun i=>(A i).fieldA (σ i)
local notation "Tμ" σ:max p:max=> P.Turnstile a (F! σ) L p
local notation "uμ" p:max=>fun i=> p i a
open Classical
abbrev StarCluster (p:I→Vantage) :Prop:=∀ a:Axis, ∃ k:List I, L.Perm k ∧ LightsCross a k p
noncomputable def EuCost (B:I→ℝ≥0→(P.ManyF a (P.advocate 3 x a)).Op)(q:I→Vantage) : ℂ:= if h: LightsCross a L q then P.ChartPrice x a L B q (sews a L q h).choose (sews a L q h).choose_spec.choose else 0

lemma power_finishes (u:∀ i∈ L,(A i).Finishes) {s:Filter ℕ}{σ:ℕ→I→ℕ}(h:∀ i∈ L,Tendsto (fun k=> σ k i) s atTop){p':ℕ→I→Vantage}(hp:∀ i∈ L,Tendsto (fun k=> p' k i) s (𝓝 (p i)))(z: LightsCross a L p): ∀ᶠ i in s,P.Turnstile a (fun j=>(A j).fieldA (σ i j)) L (p' i):=by
 classical
 induction L with
 | nil=> exact Eventually.of_forall fun _=>List.Pairwise.nil
 | cons i l ih=>
    let V(j:I):= (fun n=> ((A j).fieldA (σ n j)).realWidth P a)
    let p0(j:I):= fun k=> p' k j a
    have he(j:I)(c:j∈i::l): Tendsto (V j) s (𝓝 0):=by unfold V; simp_rw [Apron.width_real]; exact NNReal.tendsto_coe.mpr ((u j c a).comp (h j c))
    have hx(j:I)(c:j∈l): ∀ᶠ n in s,p' n i a+V i n < p' n j a-V j n:= ((tendsto_pi_nhds.mp (hp i (List.Mem.head ..)) a).add (he i (List.Mem.head ..))).eventually_lt ((tendsto_pi_nhds.mp (hp j (List.Mem.tail _ c)) a).sub (he j (List.Mem.tail _ c))) (by simp only [add_zero,sub_zero]; exact (List.pairwise_cons.mp z).1 j c)
    filter_upwards [((l.toFinset.eventually_all).2 (fun i c=>hx i (List.mem_toFinset.mp c))),ih (fun i c=> u i (List.Mem.tail _ c)) (fun i c=> h i (List.Mem.tail _ c)) (fun i c=> hp i (List.Mem.tail _ c)) ((List.pairwise_cons.mp z).2)] with i u p
    exact List.pairwise_cons.mpr ⟨fun j c=> u j (List.mem_toFinset.mpr c),p⟩
lemma power_cluster (u:∀ i∈ L,(A i).Finishes) {σ:ℕ→I→ℕ}(h:∀ i∈ L,Tendsto (fun k=> σ k i) atTop atTop){p':ℕ→I→Vantage}(hp:∀ i∈ L,Tendsto (fun k=> p' k i) atTop (𝓝 (p i)))(z: StarCluster L p): ∀ᶠ i in atTop,P.Plenum (fun j=>(A j).fieldA (σ i j)) L (p' i):=by
 unfold StarCluster at z
 choose q b c using z
 refine ((eventually_all (p:=fun a i=> P.Turnstile a (F! (σ i)) (q a) (p' i))).mpr (fun a=>?_)).mono (fun i h=> ⟨fun a=> ⟨q a,b a,h a⟩⟩)
 exact P.power_finishes a (q a) p A (fun i e=> u i ((b a).mem_iff.mpr e)) (fun i e=> h i ((b a).mem_iff.mpr e)) (fun i e=> hp i ((b a).mem_iff.mpr e)) (c a)
include v
lemma Eu_pays (f g:I→ℝ)(h:LightsCross a L p)(u:Dressing a L p f g) : P.EuCost x a L W! p=P.ChartPrice x a L W! p f g:=by unfold EuCost; rw [dif_pos h]; exact P.history_price_independent x a L p A v _ _ _ _ (sews a L p h).choose_spec.choose_spec u
lemma Eu_budget (h:LightsCross a L p){σ:ℕ→I→ℕ}(t:∀ i∈L,Tendsto (fun k=> σ k i) atTop atTop){q:ℕ→I→Vantage}(u:∀ i∈L,Tendsto (fun k=> q k i) atTop (𝓝 (p i))) : Tendsto (fun i=>P.Ancestral x a L A (q i) (σ i)) atTop (𝓝 (P.EuCost x a L W! p)):=by
 classical
 obtain ⟨f,g,u'⟩:=sews a L p h; rw [P.Eu_pays x a L p A v _ _ h u']; exact P.ancestry_flies x a L p A v f g u' t u -- `_ _` cannot infer Tendsto witnesses via dots all placeholders; fix

lemma Eu_changes (J:P.Ellis 3 x)(K:List I)(a':Axis)(q':∀i,(A i).WPermit x a')(h:LightsCross a L p)(u: LightsCross a' K p)(v':L.Perm K) : P.EuCost x a L W! p = P.EuCost x a' K (fun i=>(q' i).atHeat) p:=by
 let Z(n:ℕ)(_ : I):=n
 have t(i:I): Tendsto (fun k=> Z k i) atTop atTop:=tendsto_id
 refine tendsto_nhds_unique_of_eventuallyEq (P.Eu_budget x a L p A v h (fun i _=>t i) (q:=fun _=>p) (fun i _=>tendsto_const_nhds)) (P.Eu_budget x a' K p A q' u (fun i _=>t i) (q:=fun _=>p) (fun i _=>tendsto_const_nhds)) ?_
 have pL(b:Axis)(l:List I)(u:LightsCross b l p): ∀ᶠ i in atTop,P.Turnstile b (F! (Z i)) l p:=P.power_finishes b l p A (fun i _=>(v i).thin) (fun i _=>t i) (p':=fun _=>p) (fun i _=>tendsto_const_nhds) u
 filter_upwards [pL _ _ h,pL _ _ u] with i h u; change (P.Ancestral x a L A p (Z i))=P.Ancestral x a' K A p (Z i); unfold Ancestral; exact congrArg₂ HMul.hMul (v'.map _|>.prod_eq) (P.unanimous 3 x _ L p a a' K h u v' J)

-- EuCost continues throughout any chart (even across another chart's ties as just proved).
omit v in
lemma hot_price_cont [Finite I] (B:I→ℝ≥0→(P.ManyF a (P.advocate 3 x a)).Op) (t:∀ i∈ L,SatinRegistration.Sound S (B i))(f g:I→ℝ) (h:∀ i∈ L,f i<p i a ∧ p i a<g i): ContinuousAt (fun q=> P.ChartPrice x a L B q f g) p:=by
 let X(q:I→Vantage):=P.ChartOp x a L B q f g
 classical
 -- FirstCountableTopology at finite. If arbitrary I within chart can later generalize via restriction to L.
 apply tendsto_of_seq_tendsto; intro v' v; refine Tendsto.inner (𝕜:=ℂ) (tendsto_const_nhds (x:=Ω)) ?_
 have ht:Flying (fun i=> X (v' i)) (X p) := chart_prod L G _ (fun i e=> P.orbitCut_flies x a (B i) (t i e) (tendsto_pi_nhds.mp v i) (h i e).1 (h i e).2)
 exact (ht Ω).1
omit v in
lemma dressed_stay : ∀ (f g:I→ℝ), Dressing a L p f g → ∀ᶠ q in 𝓝 p, Dressing a L q f g:=by
 intro f g u
 classical
 refine ((L.toFinset.eventually_all).2 (fun i c=>?_)).mono (fun i hx=>⟨fun k v=> hx k (List.mem_toFinset.mpr v),u.2⟩)
 have d:= u.1 i (List.mem_toFinset.mp c)
 exact (((continuous_apply a).comp (continuous_apply (A:=fun _ : I=>Vantage) i)).tendsto p).eventually (_root_.Ioo_mem_nhds d.1 d.2) -- tune Ioo. metavars tac?
lemma Eu_cont [Finite I] : ContinuousOn (P.EuCost x a L W!) (setOf (LightsCross a L)):=by
 classical
 intro q h
 obtain ⟨f,g,hg⟩:=sews a L q h
 apply ((P.hot_price_cont x a L q W! (fun i _=>(v i).delivery.isSound) f g hg.1).continuousWithinAt).congr_of_eventuallyEq ?_ (P.Eu_pays x a L q A v f g h hg) -- tune eq orientation
 filter_upwards [((dressed_stay a L q f g hg).filter_mono nhdsWithin_le_nhds), self_mem_nhdsWithin] with q t v₀; exact P.Eu_pays x a L q A v f g v₀ t

/-! Actual consultation at aligned refinements. All-coordinate separation requires a
 strict-permutation witness along EACH axis (word may change ordering!), positivity
 at any outer pads in given axes. Test itself is an actual Mark consultation.
-/
omit v
noncomputable def fullVisit (σ:I→ℕ)(r:I→ Cover)(n:ℕ):P.Test:= (L.map (fun i=> (A i).rate (σ i))).prod • P.fullScroll n (F! σ) r L
lemma full_visit_exact (J:P.Ellis 3 x)(σ:I→ℕ)(r:I→ Cover)(n:ℕ)(p':P.Turnstile a (fun i=>(A i).fieldA (σ i)) L (P.laysM ∘ (P.vtile n ∘ r)))(g:P.Plenum (F! σ) L (P.laysM ∘ (P.vtile n ∘ r))) (h:∀ i∈ L, ((A i).fieldA (σ i)).s ≤ n) : P.singleState 3 n x (P.fullVisit L A σ r n)=P.Ancestral x a L A (P.laysM ∘ (P.vtile n ∘ r)) σ:=by
 unfold fullVisit Ancestral; rw [map_smul, smul_eq_mul,← P.entirely_now 3 x (F! σ) L J a _ p' g,P.turn_purchase a ξ _ r n L p' h,P.single_agrees]
-- unconditional any obtained sequence pricing (including different widths than resolution t goes)
include v
lemma full_visit_limit (J:P.Ellis 3 x)(h:LightsCross a L p)(u:StarCluster L p){σ:ℕ→I→ℕ}(t:∀ i∈L,Tendsto (fun k=>σ k i) atTop atTop){r:ℕ→I→ Cover}{n:ℕ→ℕ}(p0:∀ i∈L,Tendsto (fun k=> P.laysM (P.vtile (n k) (r k i))) atTop (𝓝 (p i))) (g:∀ᶠ k in atTop,∀ i∈ L,((A i).fieldA (σ k i)).s ≤ n k) : Tendsto (fun k=>P.singleState 3 (n k) x (P.fullVisit L A (σ k) (r k) (n k))) atTop (𝓝 (P.EuCost x a L W! p)):=by
 let q(k:ℕ):=P.laysM ∘ (P.vtile (n k) ∘ (r k)); have v0:∀ i∈ L,Tendsto (fun k=>q k i) atTop (𝓝 (p i)):= p0
 apply (P.Eu_budget x a L p A v h t v0).congr' ?_
 let W₀:= fun i (_:i∈L)=> (v i).thin; filter_upwards [P.power_finishes a L p A W₀ t v0 h,P.power_cluster L p A W₀ t v0 u,g] with i h p g; exact (P.full_visit_exact x a L A J _ _ _ h p g).symm
omit v
-- not vacuous. take these perhaps later n as needed. Can even replace by direct point approxim if widths already allow t; no claim here
lemma full_visit_possible (σ:ℕ→I→ℕ) : ∃ (r:ℕ→I→ Cover)(n:ℕ→ℕ), Tendsto n atTop atTop ∧
   (∀ i∈ L,Tendsto (fun k=> P.laysM (P.vtile (n k) (r k i))) atTop (𝓝 (p i))) ∧
   ∀ k:ℕ,∀ i∈ L,((A i).fieldA (σ k i)).s ≤ n k:=by
 choose f hf using fun i:I=> P.vantage_approach (p i); let q(n:ℕ)(i:I):= f i n
 choose n r' g using (fun i:ℕ=> (((eventually_ge_atTop i).and (P.vmarks (F! (σ i)) L (q i)))).exists) -- shape ∃ n,n≥i∧ onMark
 choose r p0 h using g
 refine ⟨r,n,tendsto_atTop_mono r' tendsto_id,fun i e=> (hf i).congr fun k=> ?_,p0⟩
 exact congrArg P.laysM (h k i e).symm
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.Eu_changes
#print axioms Spine.full_visit_possible
#print axioms Spine.full_visit_limit
#print axioms Spine.Eu_cont
