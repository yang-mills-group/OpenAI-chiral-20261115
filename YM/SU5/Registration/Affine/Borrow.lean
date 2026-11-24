import YM.SU5.Registration.Affine.UChart
import YM.SU5.Registration.Affine.Collateral
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
local notation "τ" p:max=> Real.toNNReal (p:ℝ)
local notation "GOp" x:max=> (P.ManyF a (P.advocate 3 x a)).Op
local notation "Θ'" x:max=> P.seasons a (P.advocate 3 x a)
local notation "Φ"=>P.Spectrum0 3
/-! ## ModSpaces finances the all-$\gamma$ continuity in generic poses and (116) transfer

 Norm estimates on mean *compression* of each WHOLE FIELD WORD after passage to
 projected G in the necessary generic thermal estimates. Don't use uniform-in-$\gamma$
 SOT from stencils priced at approximately aligned spatial lattice points. Use only
 the given `ModSpace` and uniform operator costs, and alignment by real spatial movements
 on the arguments of ACTUAL all-axis generic powers. Then wear the *offset changes*
 also with uniform pricing, using estimates for ALL axes at this character.
-/
variable {I:Type*}(L:List I) (p:I→Vantage)(A:I→P.Swatch)
variable (f g:I→ℝ) (K:P.Register)(F:LightsCross a L p)(t:Dressing a L p f g)
variable {σ:ℕ→I→ℕ}(v:∀ i∈ L,Tendsto (fun k=>σ k i) atTop atTop)(u:StarCluster L p)(y:∀ i∈ L,P.ModSpaces a (A i))(z:∀ i∈ L,∀ b:Axis,P.ThresholdPrice b (A i))
variable {q:ℕ→I→Vantage}(p0:∀ i∈ L,Tendsto (fun k=> q k i) atTop (𝓝 (p i)))
lemma travel_heat (h l:ℝ≥0)(A B:(G).Op): dist (T₀ h*A*T₀ l) (T₀ h*B*T₀ l) ≤ dist A B:=by
 simp only [dist_eq_norm,← _root_.sub_mul,← mul_sub]; exact P.stoves_price ..
-- what can ask if ModSpace paid. Q chosen independently of σ. include receipt if now.
lemma ModSpaces.ticket (w:P.Swatch)(p:P.ModSpaces a w)(h:P.ThresholdPrice a w) (t:ℕ→ℕ)(z:Tendsto t atTop atTop)(q:Vantage)(f g:ℝ)(hf:f<q a)(hh:q a<g)(ε:ℝ)(e:0<ε) : ∃ (X:ℕ→Vantage) (D:∀ k:P.Spectrum0 3,(P.ManyF a (P.advocate 3 k a)).Op), Tendsto X atTop (𝓝 q) ∧ UpTo atTop (fun i k=> w.scoop P k a f g (X i) (t i)) (fun _ k=>D k) ε:=by
 obtain ⟨s,h',l,u⟩:=clock_enough f g (q a) hf hh
 let b:= τ (q a-f)-s; let b':=τ (g-q a)-s; let c:=ε/2; have hc:0<c:=half_pos e
 obtain ⟨G',D,v,Q⟩:= p.2 s h' c hc
 let X(i:ℕ):= q+G' (t i); let D'(k):= (Θ' k).E b * P.cane k a (D k) q * (Θ' k).E b'; have he:Tendsto X atTop (𝓝 q):=by simpa only [X,Function.comp_apply,add_zero] using (v.comp z).const_add q
 refine ⟨X,D',he,(add_halves ε) ▸ (((P.scoop_progress a w h p.1 f g s h' l u X t he z) c hc).chain (?_ : UpTo _ _ (fun _ k=> D' k) c))⟩ -- syntax nested `UpTo` with implicit X OK?
 filter_upwards [z.eventually Q] with i M k
 unfold D' X; refine (P.travel_heat k a b b' _ _).trans ?_; rw [← P.cane_join]; exact (P.cane_distance k a _ _ _).trans (M k)
include F K u y z v p0 t
-- alignment throughout. StarCluster true not just Crossing in our axis.
lemma bank_ancestry (d:ℝ)(U:0<d): ∃ Z:Φ→ℂ, UpTo atTop (fun i x=> P.Ancestral x a L A (q i) (σ i)) (fun _ x=>Z x) d:=by
 classical
 let tZ:=fun i (h:i∈L)=>(y i h).1
 let ya:= fun i (h:i∈L)=> z i h a
 obtain ⟨C,hc,x'⟩:= P.reach_cost a L p A f g t tZ ya
 let Y:=fun x:Φ=> GOp x; let ε:=d/2; have hε:0<ε:=half_pos U
 obtain ⟨B,hb,W⟩:= limit_ticket (s:=atTop) (J:=ℕ) L (fun k=> P.stoves_paidOne k a) C hc ε hε
 choose! r D tr h using (fun i (u:i∈L) => ModSpaces.ticket P a (A i) (y i u) (ya i u) (fun k=>σ k i) (v i u) (p i) (f i) (g i) (t.1 i u).1 (t.1 i u).2 B hb)
 let q'(n:ℕ)(i:I):=r i n
 have tp:∀ i∈L,Tendsto (fun n=>q' n i) atTop (𝓝 (p i)):=tr
 let D':=fun x=> (L.map (fun i=>D i x)).prod
 let Z:= fun x=>inner ℂ (P.heaven a (Θ x a)) (D' x (P.heaven a (Θ x a)))
 refine ⟨Z,(add_halves d) ▸ ((((P.throughout a K L p A v tZ p0 tp F u z).trans (P.wearing a L p A f g t v tZ tp)) ε hε).chain (?_ : UpTo _ _ (fun _ x=>Z x) ε))⟩
 let X:= fun i k (x:Φ)=> (A i).scoop P x a (f i) (g i) (q' k i) (σ k i)
 have he:UpTo atTop (fun (k:ℕ) (x:Φ)=> (L.map (fun i=> X i k x)).prod) (fun _ x=>D' x) ε:= W X (fun i _ x=> D i x) (fun i p=> x' i p (r i) (fun k=>σ k i) (tp i p) (v i p)) h
 exact he.verify (fun x=> P.heaven a (Θ x a)) (fun x=> P.stone_norm a _)
omit t
-- Program-level receipt for passing to Ground. Continuity in gamma follows because
-- at generic grid frame prelimit it's also Price on Marks at same consultation (holds
-- mechanically and uniformly for all gamma). Uniform-scalar certificate with the
-- SAME point Price.
omit F K u y z v p0
abbrev CoPays (A:I→P.Swatch)(T':∀ i x,(A i).WPermit x a)(L:List I)(p:I→Vantage) (σ:ℕ→I→ℕ)(q:ℕ→I→Vantage):Prop:= Agrees (b:=fun _=>ℂ) atTop (fun k (x:P.Spectrum0 3)=> P.Ancestral x a L A (q k) (σ k)) (fun k x=>P.EuCost x a L (fun i=>(T' i x).atHeat) p) -- wrapper not needed
include F K u y z v p0
lemma copass (T':∀ i x,(A i).WPermit x a) : P.CoPays a A T' L p σ q:=by
 classical
 obtain ⟨f,g,t⟩:= sews a L p F
 exact learns_price (fun x=> P.Eu_budget x a L p A (fun i=> T' i x) F v p0) (P.bank_ancestry a L p A f g K F t v u y z p0) -- implicit proof h
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.ModSpaces.ticket
#print axioms Spine.bank_ancestry
#print axioms Spine.copass
