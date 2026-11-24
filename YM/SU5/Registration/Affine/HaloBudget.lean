import YM.SU5.Registration.Affine.Scoria
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
/-
# Use stability on just the ancestral portion of the $A$ issue in purchasing
 another family (finite convex sums exactly recovered by the managed stamps).
 Then common-character ground Gram even on the new price portfolio.
-/
variable {I:Type*}(K:P.Register)(L:List I)(A B:I→P.Swatch)(v:I→ℕ→ Coalition)
variable (u:∀ i,P.Mantle a (A i) (B i) (v i))
variable (z:∀ i x,(B i).WPermit x a)(w:∀ i x,(A i).WPermit x a)(t:∀ i,(B i).Finishes)
-- narrow credential for this product & cluster; doesn't require all-angles or other charts
-- for this A except the bounding purchases issued for the substitute B on this call.
def Passport (A:I→P.Swatch)(u:∀ i x,(A i).WPermit x a) (p:I→ Vantage): Prop:=
   ∀ (σ:ℕ→I→ℕ) (q:ℕ→I→Vantage), (∀ i∈L,Tendsto (fun k=>σ k i) atTop atTop)→ (∀ i∈ L,Tendsto (fun k=> q k i) atTop (𝓝 (p i))) → P.CoPays a A u L p σ q
-- converge all possible mantle choices uniformly even if no spin. Use group-less stability and simple selection.
private lemma mass_ready {α:Type*}[Inhabited α](Q:ℕ→α→Prop)(p:∀ (f:ℕ→α),∀ᶠ i:ℕ in atTop,Q i (f i)) : ∀ᶠ i:ℕ in atTop,∀ x:α,Q i x:=by
 classical
 let f(i:ℕ):= if h:∃ x,¬Q i x then h.choose else default
 refine (p f).mono (fun i h x=> by_contra ?_); intro p; have ht: ∃ x,¬Q i x:= ⟨x,p⟩; have hn:¬ Q i (f i):= by unfold f; rw [dif_pos ht]; exact ht.choose_spec
 exact hn h
include u t
variable (p:I→Vantage)(h:LightsCross a L p)
local notation "ι"=> P.Spectrum0 3
local notation "W"=> fun (i:I)=> (w i x).atHeat -- macro hygiene avoid binder x collision. can't use
local notation "B₀"=> P.Ancestral
include h
lemma passport_coating (b: P.Passport a L B z p) : P.Passport a L A w p:=by
 classical
 intro σ q Lρ k; let v₀(x:P.Spectrum0 3):= P.EuCost x a L (fun i=> (z i x).atHeat) p
 have hy(x:P.Spectrum0 3): P.EuCost x a L (fun i=>(w i x).atHeat) p=v₀ x:=congrArg (fun q=> P.EuCost x a L q p) (funext fun i=> P.mantle_keeps x a (A i) (B i) (v i) (u i) (z i x) (w i x))
 unfold CoPays; simp_rw [hy]; obtain ⟨f,g,h0⟩:= sews a L p h; have hu:L.Nodup:=h.imp (fun c p=>by rcases p with rfl; exact lt_irrefl _ c)
 apply (P.wearing a L p A f g h0 Lρ (fun i _=>(u i).finishes) k).trans
 intro r ε
 let Q(i:ℕ)(α:I→ℕ):Prop:=∀ x:ι,dist (P.RawPrice x a L B (q i) f g (fun k=>σ i k + α k)) (v₀ x) ≤ r
 have hm(i:I)(p':i∈L): ∀ᶠ j:ℕ in atTop,∀ x:P.Spectrum0 3,(A i).scoop P x a (f i) (g i) (q j i) (σ j i)=offer (v i (σ j i)) (fun k=>(B i).scoop P x a (f i) (g i) (q j i) (σ j i+k)):= P.mantle_scope a _ _ _ (u i) (f i) (g i) (h0.1 i p').1 (h0.1 i p').2 (fun j=> q j i) (k i p') (fun k=>σ k i) (Lρ i p') (t i)
 have hQ:∀ᶠ i in atTop,∀ α:I→ℕ,Q i α:= by
    refine mass_ready Q fun x=>?_; let X(i:ℕ)(k:I):=σ i k+x i k; let p(k:I)(v₀:k∈L):=tendsto_atTop_mono (g:=fun i=>X i k) (fun i=>(Nat.le_add_right (σ i k) (x i k))) (Lρ k v₀) -- p shadow V using only h0
    exact (((P.wearing a L _ B f g h0 p (fun i _=> t i) k).symm).trans (b X q p k)) r ε
 filter_upwards [hQ,(L.toFinset.eventually_all.mpr fun i c=> hm i (List.mem_toFinset.mp c))] with n p m x
 let Y(i:I)(k:ℕ): (GOp x):=(B i).scoop P x a (f i) (g i) (q n i) (σ n i+k); let Z(i:I):= v i (σ n i); let Ω':= P.heaven a (Θ x a); let ψ:= ((innerSL ℂ Ω').comp (ContinuousLinearMap.apply ℂ (P.ManyF a (Θ x a)).space Ω')).toLinearMap; let T'(i:I):=(A i).scoop P x a (f i) (g i) (q n i) (σ n i); change dist (ψ (L.map T').prod) (v₀ x) ≤ r; rw [List.map_congr_left (g:=fun i=> SatinRegistration.offer (Z i) (Y i)) (show ∀ i∈ L,T' i=offer (Z i) (Y i) from fun i q=>m i (List.mem_toFinset.mpr q) x)] -- ambiguous
 exact taught (GOp x) L hu Z Y ψ (v₀ x) r (fun σ=>p σ x) -- tune `[NormedRing V]` Lean sees V induced opCStarAlgebra; might defeq conflict
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.passport_coating
#print axioms Spine.Mantle.card
#print axioms Spine.mantle_keeps
#print axioms Spine.mantle_scope
#print axioms Spine.mantle_threshold
