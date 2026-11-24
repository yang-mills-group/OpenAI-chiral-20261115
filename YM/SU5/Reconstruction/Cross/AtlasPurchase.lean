import YM.SU5.Reconstruction.Cross.Acquisition
import YM.SU5.Reconstruction.Cross.Rays
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Selected Tapestry Tapestry.Altitude Tapestry.Exhibition
open Set OS.Semigroup MeshClock Germ
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
local notation "L₀" => Λ.R.L.val
local notation "Μ" => timeMesh Λ
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ} {E : ℕ → Family (tent Y H) → ℂ}
  (V : Universal Y H i k I E)
  {D : ℕ→Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i:=i) (k:=k) (E:=E) Y H D a b) (Qt : Clipped Y H (i∘a) (k∘b))
  (s : ℕ) (j : Axis) (C : Arena Y H Q.circuit j 0 false) -- aim all even incl characters extension
variable (c : (displayAlgebra Y H V Q Qt j false C) →⋆ₐ[ℂ] ℂ)
local notation "𝔄" => driveAlgebra Y H V Q Qt j false C
local notation "ρ" => indoor Y H V Q Qt j false C c
local notation "Ρ" => procession Y H V Q Qt j false C c
local notation "Ω" => doorstep Y H V Q Qt j false C c
local notation "Eχ" s:max => Selected.response Y H V s Q Qt j false C c
local notation "Ex" => ride Y H V Q Qt j false C c
local notation "Φ" t:max => Tower.Field Y H t j 0 false
local notation "T" n:max => Selected.bud Y H V n Q Qt j false C c
/-!
# All chart readings certificate on chosen ground decomposition axes & coherent widths

Not asserting Spin(L) or Wightman Fields yet! Includes BOTH real (Euclidean) and
real-time kernel comparisons already achieved. On all Atlas queries measuring arbitrary
chart orderings of the local-resolution observables (actual law), show they determine
a single real-spacetime function (the Atlas above). Moreover all Mink time axis choices
take **their real/analytic contour from this same function**, no freedom at intersection (analytic theorem). More work required to identify even curves using different time axes, mixed analytic & spectrum, contact & Lorentz.
-/
variable (P : ∀ k : Axis,Arena Y H Q.circuit k 0 false)
section
variable {ι:Type*} [Fintype ι] (f:ι→ Marks (tent Y H) false) (x:List ι)
local notation "D₀" => arenaRegion Y H Q s f x
local notation "C'" k:max=> displacement Y H V Q Qt j false C c k (P k)
local notation "F" t:max=> fun i:ι=> upGrade Y H s Q false (f i) t
local notation "Gp" => timeMesh Λ
local notation "Λw" => ι→ Axis→ℝ
local notation "Tv" => gridChart (ι:=ι) Μ
local notation "S" => seeMesh (timeMesh Λ)
local notation "Z" => commonR Y H V Q Qt s j C c f x P
local notation "E'" t:max k:max => electedAtlas Y H V Q Qt t k (P k) (C' k) (F t)
local notation "R'" t:max k:max => rawTrace Y H V Q Qt t k (P k) (C' k) (F t)
local notation "ξ" t:max k:max=> requested Y H V Q Qt t k (P k) (C' k) (F t)
local notation "ψ" t:max k:max=>arrived Y H V Q Qt t k (P k) (C' k) (F t)
local notation "O" t:max k:max=>edgeArrival Y H V Q Qt t k (P k) (C' k) (F t)
local notation "Aq" t:max k:max=> viewing Y H t k (F t)
local notation "EP" t:max => Selected.response Y H V t Q Qt j false C c

structure ChartPurchase (x:List ι) : Prop where -- fix local notation using x implicit binder bug; better remove.
  continuous : IsOpen (arenaRegion Y H Q s f x) ∧ ContinuousOn (commonR Y H V Q Qt s j C c f x P) (arenaRegion Y H Q s f x)
  accepts (i:Axis) (A:AcceptFrom Y H Q s i f x):
     A.domain⊆ arenaRegion Y H Q s f x ∧ ∀ v∈A.domain,
       commonR Y H V Q Qt s j C c f x P v= (E' A.stage i) A.gate A.order v
  mesh {X:DecidableEq ι} : letI := X; ∀ i:Axis,∀ (A:AcceptFrom Y H Q s i f x) (v:ι → S), Tv v∈A.domain →
    Tendsto (smoothPositions (timeMesh Λ) ((R' A.stage i) A.gate A.order) v) nested (𝓝 (commonR Y H V Q Qt s j C c f x P (Tv v)))
  sharp (i:Axis)(A:AcceptFrom Y H Q s i f x)(v:ι→ S)(p:Tv v∈ A.domain)
      (t:ℕ)(s':A.stage≤t)(q:ι→ Cover)(e:v=grid Μ t∘q):
       (R' A.stage i) A.gate A.order v = (EP t) (orderWord Y H Q s f t x q)
  exact_cont (i:Axis)(A:AcceptFrom Y H Q s i f x) (v:ι → S)(p:Tv v∈A.domain)(ht:everywhere_axis Y H A.stage (F A.stage) A.order (Tv v)):
     commonR Y H V Q Qt s j C c f x P (Tv v)= (R' A.stage i) A.gate A.order v
  analytic (i:Axis) (A:AcceptFrom Y H Q s i f x) (v:ι → Axis→ℝ) : AnalyticOnNhd ℂ ((ξ A.stage i) A.gate A.order v) {z:ι→ℂ|viewing Y H A.stage i (F A.stage) A.gate A.order v z}
  sees (i:Axis) (A:AcceptFrom Y H Q s i f x) (v:ι→Axis→ℝ) (z:ι→ℝ) (p:realContour i v z∈A.domain):
     (ξ A.stage i) A.gate A.order v (fun i=>(z i:ℂ))=commonR Y H V Q Qt s j C c f x P (realContour i v z)
  edge (i:Axis) (A:AcceptFrom Y H Q s i f x) (v:ι→Axis→ℝ) (w:ι→ℂ) (p:viewing Y H A.stage i (F A.stage) A.gate A.order v w):
    (O A.stage i) A.gate A.order (realContour i v (fun i=>(w i).re), fun i=> -(w i).im)= (ξ A.stage i) A.gate A.order v w
  together (i:Axis)(A A':AcceptFrom Y H Q s i f x)(v:ι→Axis→ℝ)(w:ι→ℝ)(u:v∈ A.domain)(u':v∈ A'.domain):
    (ψ A.stage i) A.gate A.order v w=(ψ A'.stage i) A'.gate A'.order v w
  covers (Z₀:ι→ Finset Cover) (v:ι→ Axis→ℝ) (p:∀ k,InTest K true (Z₀ k) false (f k).val) (o:List ι)(vo:o.Perm x) (i:Axis)(start dest:ι→ℝ)(r:ℝ)(h:books start dest r o)
    (e:∀ k,start k<dest k∧∀ x∈silhouette Λ l s (Z₀ k), v k i+x i∈ Ioo (start k) (dest k)): ∀ᶠ t in atTop,∃ A: AcceptFrom Y H Q s i f x, A.stage=t∧A.order=o∧v∈ A.domain
lemma chartPurchased (p:x.Nodup): ChartPurchase Y H V Q Qt s j C c P f x:=by
 refine ⟨⟨arena_open Y H Q s f x,common_continuous Y H V Q Qt s j C c f x P p⟩,fun i A=>⟨in_chart Y H Q s i f x A,fun _=> enters_common Y H V Q Qt s j C c f x P p A _⟩,?_,?_,?_,fun i A v z=> window_complex Y H V Q Qt A.stage i (P i) (C' i) (F A.stage) A.gate A.order v z,?_,fun i A v w h=> (passage Y H V Q Qt A.stage i (P i) (C' i) _ A.gate A.order v w h).symm,fun i A A' v w=> connected_across Y H V Q Qt s i (P i) (C' i) f x A w A' p v,fun W v a e hz q M N b under h=>payment_geometry Y H Q s f x W e hz a h b under ⟩
 · intro X i A v g; letI:=X; rw [enters_common Y H V Q Qt s j C c f x P p A _ g]; exact handles _ _ _ _ _ _ _ _ _ _ _ _ _ (A.schedule.nodup_iff.mpr p)
 · rintro i A v g t ht q rfl; rw [train_lattice Y H V Q Qt A.stage i (P i) (C' i) _ _ t ht q _ _ A.travel, across_response Y H V,← keyPath Y H Q s f t A.stage A.large ht,order_word_perm Y H Q s f t A.schedule]; exact fun i h => (A.gate i).allows (g i h)
 · intro i A v g e; rw [enters_common Y H V Q Qt s j C c f x P p A _ g,recovers Y H V Q Qt A.stage i (P i) (C' i) (F A.stage) A.gate A.travel (A.schedule.nodup_iff.mpr p) v P g e]
 intro i A v z h; rw [euclidean_time Y H V Q Qt A.stage i (P i) (C' i) _ _ _ _ z h]; exact (enters_common Y H V Q Qt s j C c f x P p A _ h).symm
end
-- all room laws assembled; leave universes consumer open
structure BoughtAtlas : Prop where
 regions (s:ℕ) {ι:Type} [Fintype ι] (f:ι→ Marks (tent Y H) false) (x:List ι)(p:x.Nodup) : ChartPurchase Y H V Q Qt s j C c P f x
 stamps (i:Axis)(s:ℕ)(x: Marks (tent Y H) false)(g: Gate Y H s i x)(U:Set RSpace)(t:ℕ)(p:s≤t)(v:Cover)
    (h:∃ X:Finset Cover, InTest (tent Y H) true X false x.val ∧ silhouette Λ l s X ⊆ U):
    ∃ W:Finset Cover, InTest K true W false (relocateWorld Y H false v (upGrade Y H s Q false x t)).val ∧
       silhouette Λ l t W ⊆ {p | p-toR (M:=timeMesh Λ) (grid (timeMesh Λ) t v)∈ U}
lemma bought : BoughtAtlas Y H V Q Qt j C c P:=by
 refine ⟨fun s {_} [_] x y h=> chartPurchased Y H V Q Qt s j C c P x y h,?_⟩
 intro i s x g B t p v h; obtain ⟨Z,h,hp⟩:=h
 let d:= high_aperture_test Y H Q s h v t p; exact ⟨_,d.1,fun _ q=> hp (d.2 _ q)⟩
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas.bought
