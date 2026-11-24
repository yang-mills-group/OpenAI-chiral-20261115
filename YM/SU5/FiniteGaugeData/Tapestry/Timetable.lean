import YM.SU5.FiniteGaugeData.Tapestry.Concatenation
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 550000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale FullBill
open Nacre Mir Phase RP
open Altitude Heat Pastry
open PiTensorProduct (tprod)

/-!
# Changing observables, supports & level. Arrangements on the SAME cone of
one (optional) further simultaneous thinning.

These use the previously defined **same** row and Vista functionals, preserved
explicitly (not rebuilding a different Euclidean theory with this thinning). Can
still use `Fashion` on the further selection on the same B,F budget when needed.

Difference-cost statements: charged to arbitrary desired ε at each indicated
NEW IR stage for each request up to that stage. Rectangle facet is still the
same room (`Exhibition.status`). Earlier UV requirements paid along full UV row
at fixed period j via `notices`, not at one UV stage for all periods. At the
thinned selection receiving forecasts here, we can pay on ALL of its cone UV
choices at this new stage. No geometry dependence on test polynomial besides
what is declared in such slots.
-/
set_option quotPrecheck false
open Exhibition
section
variable {Λ: Preparation} {l : ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l)) (H:Real.exp 1 ≤ Λ.x)
variable {a b:ℕ→ℕ} {I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{L:Rack Λ l}{B:Clay Λ l}{T:ℕ→ℕ→Tariff}{t:ℕ→Tariff}(D:Fashion Y H a b I E L B T t)
local notation "V"=>tent Y H
namespace Fashion
local notation "Q"=> D.toExhibition
variable (S:BillOfWork)(n w j:ℕ) (ε:ℝ)

-- helpers
lemma rowIndependence {v u:ℕ→ℕ}(q:StrictMono u) (D':Fashion Y H v (b∘u) I E L B T t) :
    ∀ x∈FiniteGaugeDataPoly V, rowTake Y H j D x=rowTake Y H j D' x:=by
 intro x p; exact tendsto_nhds_unique (Filter.Tendsto.comp (D.allCoupon Y H p|>.inner j) q.tendsto_atTop) (D'.allCoupon Y H p|>.inner j)
lemma vistaIndependence {v u:ℕ→ℕ}(p:StrictMono v)(q:StrictMono u)(D':Fashion Y H (a∘v) (b∘u) I E L B T t) : ∀ x∈FiniteGaugeDataPoly V,
 vistaTake Y H D.toExhibition x= vistaTake Y H D'.toExhibition x:=fun x h=>
  tendsto_nhds_unique_of_eventuallyEq ((D.allCoupon Y H h).periods.comp p.tendsto_atTop) (D'.allCoupon Y H h).periods (Eventually.of_forall fun i=> rowIndependence Y H D _ q D' x h)
lemma vistaFinishIndependent {v u:ℕ→ℕ} {L' : Rack Λ l}{T':ℕ→ℕ→Tariff} (D':Fashion Y H v u I E L' B T' t):
    vistaFinish Y H n (Q)= vistaFinish Y H n D'.toExhibition:=by
 -- because B & mould. no qualifier.
 have h(i): liftD Y H i D.toExhibition = liftD Y H i D'.toExhibition:=by refine LinearMap.ext fun x=>?_ ; obtain ⟨S,h⟩:= findsBay V x; obtain ⟨y,rfl⟩:= accolade V S x h; rw [fromLocal,fromLocal]
 unfold vistaFinish; apply congrArg (fun (x:Decking (Dome V) (fun _=> Dome V))=> x.crown (auxiliaryPad V) n); unfold vistaDressing; congr 1
lemma rowFinishIndependent {v u:ℕ→ℕ}(q:StrictMono u)(D':Fashion Y H v (b∘u) I E L B T t) : ∀ x∈ shorter (Dome (tent Y H)) n, rowFinish Y H n j D x=rowFinish Y H n j D' x:= by
 intro x p; exact tendsto_nhds_unique (Filter.Tendsto.comp ((D.eachYear Y H n j p).2) q.tendsto_atTop) ((D'.eachYear Y H n j p).2)

local notation "i'" k:max => a (k:ℕ)
local notation "S'" => frameBudget S Λ l n
local notation "rFee"=> Garland Y H (Q) S n
local notation "Φ"=> ArcFee Y H S n B
structure Census : Prop where
 -- at IR stage w on D's selections. use ALL j on legacy cone
 seasonCost : propeller w * Garland Y H D.toExhibition S n ≤ ε
 arcsCost : propeller w * (spread (frameBudget S Λ l n)*ArcFee Y H S n B) ≤ ε
 visibleCost (x:Cloud (Dome (tent Y H)))(C:ℝ): Pocket (tent Y H) S n C x→ Quart Y H D S n (a w) (propeller w) x C
 completeCost (j:ℕ) (p:legacy Y (a w) (b j)): Exhibition.Pavilion Y S n (a w) (b j) ∧ ∀ x C,Pocket (tent Y H) S n C x→ Allows Y H D.toExhibition S n (a w) (b j) x C (propeller w) -- structure Prop add
lemma calculation (p:Census Y H D S n w ε) {x:Cloud (Dome (tent Y H))}{C:ℝ}(h:Pocket (tent Y H) S n C x)(g:legacy Y (a w) (b j)):
    ‖rowTake Y H (a w) D x-vistaTake Y H D.toExhibition x‖≤ ε*C ∧
    ‖taking Y H (a w) (b j) x - vistaTake Y H D.toExhibition x‖ ≤ ε*C ∧
    ‖rowFinish Y H n (a w) D x-roving Y H n (a w) (vistaFinish Y H n D.toExhibition x)‖≤ε*C∧
    ‖breathing Y H n (a w) (b j) x-roving Y H n (a w) (vistaFinish Y H n D.toExhibition x)‖≤ ε*C:= by
 have hp:= p.completeCost j g|>.2 x C h; have hv:= p.visibleCost x C h
 have he := mul_le_mul_of_nonneg_right p.seasonCost h.priced; have hf:=mul_le_mul_of_nonneg_right p.arcsCost h.priced; exact ⟨hv.reading.trans he,hp.reading.trans he,hv.grip.trans hf,hp.grip.trans hf⟩
include D
lemma wintering (e:0<ε): ∀ᶠ w in atTop,Census Y H D S n w ε:=by
 let f:= spread (frameBudget S Λ l n)*ArcFee Y H S n B
 have h(z:ℝ):∀ᶠ w:ℕ in atTop,propeller w*z ≤ ε:= by apply Tendsto.eventually _ (eventually_le_nhds e); simpa using propeller_fades.mul_const z
 filter_upwards [h rFee,h f, firedThrough Y H D S n, (eventuallyReflection _).1 (Exhibition.horizon Y H D.toExhibition S n)] with i h t p q
 exact ⟨h,t,p,fun j x=> q j ((D.status _ _).1 x)⟩

omit D
-- diagonal construction. explicitly all hats any given list S, n & assigned toll under tolerance. can take C-sequences too via scaling ε.
private lemma walkThrough (T:ℕ→ℕ→Prop)(p:∀ j,∀ᶠ k in atTop,T j k): ∃ u:ℕ→ℕ, StrictMono u ∧ ∀ i,T i (u i):=by
 choose l h using fun i=> eventually_atTop.mp (p i); let u:=fun i=> Nat.rec (motive:=fun _=>ℕ) (l 0) (fun i k=> max (k+1) (l (i+1))) i
 refine ⟨u,strictMono_nat_of_lt_succ fun i=>?_,fun i=> h i _ ?_⟩; exact (Nat.lt_add_one _).trans_le (le_max_left _ (l (i+1))); cases i with| zero=> exact le_refl _| succ n=> exact le_max_right ..
include D
theorem itinerary (f:ℕ→ BillOfWork) (x:ℕ→ℕ) (ε:ℕ→ℕ→ℝ) (p:∀ i j,0<ε i j) :
    ∃ u, StrictMono u ∧ ∃ D':Fashion Y H (a∘u) (b∘u) I E L B T t,
    (∀ x∈ FiniteGaugeDataPoly V, vistaTake Y H D.toExhibition x= vistaTake Y H D'.toExhibition x ∧∀ j,rowTake Y H j D x=rowTake Y H j D' x) ∧ ∀ i j,j ≤ i → Census Y H D (f j) (x j) (u i) (ε i j):=by
 obtain ⟨u,h,g⟩:= walkThrough (fun i k=>∀ j∈ Finset.Iic i,Census Y H D (f j) (x j) k (ε i j)) (fun i=> (eventually_all_finset (Finset.Iic i)).mpr fun j m=> wintering Y H D (f j) (x j) (ε i j) (p i j)); let D':= D.inherit_diag Y H u h; exact ⟨u,h,D',fun x p=> ⟨vistaIndependence Y H D h h D' x p,fun j=>rowIndependence Y H D j h D' x p⟩, fun i j p=> g i _ (mem_Iic.mpr p) ⟩
end Fashion
end
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Fashion.itinerary
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Fashion.calculation
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Fashion.vistaFinishIndependent
