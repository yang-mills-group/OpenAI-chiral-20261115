import YM.SU5.FiniteGaugeData.Tapestry.Umbra
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 400000
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
# Joint result on this Course

Includes per-period limit of all finitely-supported *resolution-polynomial*
questions, at arbitrary observing height with their stated support/buffer
cost. Every limiting reader is the same Vista; if x also has a qualifying placement
on another set of supports Saj, in either region, at any higher level etc, it is
the same state value. The compatibility of expressed probes & every M height,
and the local dual estimates, follow from the construction *without* ever claiming
matching of Printed parameters over all volumes. Clear room estimates with
`horizon` and consumer forms.
-/
set_option quotPrecheck false
variable {Λ: Preparation} {l : ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l)) (H:Real.exp 1 ≤ Λ.x)
variable {a b:ℕ→ℕ} {I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{L:Rack Λ l}{B:Clay Λ l}{T:ℕ→ℕ→Tariff}{t:ℕ→Tariff}(D:Fashion Y H a b I E L B T t) (S:BillOfWork)(n i k:ℕ)
local notation "κ"=> tent Y H
local notation "P"=> Pocket (tent Y H)
local notation "V"=> frameBudget S Λ l n
local notation "Ω" j:max=> side Y i j
local notation "U"=> Ward (side Y i n)
local notation "i₁" t:max => a (WedgeStage.vol t)
local notation "k₁" t:max => b (WedgeStage.uv t)
local notation "μ"=> propeller
open Exhibition
namespace Fashion
local notation "d"=> D.toExhibition
lemma eachYear {x:Cloud (Dome κ)}(p:x∈shorter (Dome κ) n): Tendsto (fun k=> taking Y H i (b k) x) atTop (𝓝 (rowTake Y H i D x)) ∧ Tendsto (fun k=> breathing Y H n i (b k) x) atTop (𝓝 (rowFinish Y H n i D x)):=by obtain ⟨S,p⟩:= anyWords κ n x p; obtain ⟨t,v⟩:=issued.mp p; exact D.purePrices Y H n i S v -- tune
include D
private lemma trueSupport {s:Side}(z:Ward s)(g:ℕ→Ward s){S:Finset (Site (More s))} (p:Tendsto g atTop (𝓝 z))(t:∀ᶠ i in atTop, AtSupport false S (attire (g i))): AtSupport false S (attire z):=by
  let Q : Submodule ℂ (FC (Single s)):=
     { carrier:={u| Reed.Fine (Tset s) (modesIn s S) false u}
       zero_mem':= Reed.Fine.empty _
       add_mem':= fun p q=> Reed.Fine.add p q
       smul_mem':=fun z x p=> Reed.Fine.scale p z }
  exact ⟨(Ward.signs z).env, fun x y u v=> tendsto_nhds_unique_of_eventuallyEq (Ward.limit_at p x) (Ward.limit_at p y) (t.mono fun i t=>t.dep x y u v),fun x=> Q.closed_of_finiteDimensional.mem_of_tendsto (Ward.limit_at p x) (t.mono fun i h=> h.allV x)⟩
lemma rowSupport {x:Cloud (Dome κ)}{C} (p:Pocket κ S n C x): AtSupport false (region (frameBudget S Λ l n) (side Y i n)) (attire (rowFinish Y H n i D x)):= trueSupport Y H D _ _ (D.purePrices Y H n i S p).2 ((D.toExhibition.sharper Y H n i).mono fun k v=> textureBudget Y H S n i (b k) v x p)
private lemma persisted {s:Side}{v: Ward s}{u:ℕ→ Ward s}(t:Tendsto u atTop (𝓝 v))(h:∀ᶠ k in atTop, covariant (attire (u k))) : covariant (attire v):=by
 intro g x; exact tendsto_nhds_unique_of_eventuallyEq (Ward.limit_at t (simultaneous g x)) ((Fock.breeze _).continuousAt.tendsto.comp (Ward.limit_at t x)) (h.mono fun k h=> h g x)
lemma rowGauge {x:Cloud (Dome κ)}(p:x∈shorter (Dome κ) n) {s:Bool}{A:Set ℕ}{V':Set RSpace}(q:x∈ well Λ κ l s V' A): covariant (attire (rowFinish Y H n i D x)):= persisted Y H D ((D.eachYear Y H n i p).2) ((D.toExhibition.sharper Y H n i).mono fun k v=> paid_coherence Y H i (b k) n v x q p) -- order
local notation "r"=> Garland Y H (d) S n
omit D
structure Quart (D:Fashion Y H a b I E L B T t) (S:BillOfWork)(n i:ℕ)(ε:ℝ)(x:Cloud (Dome (tent Y H)))(C:ℝ) : Prop where
 location : AtSupport false (region (frameBudget S Λ l n) (side Y i n)) (attire (rowFinish Y H n i D x))
 rangeLimit : ‖rowFinish Y H n i D x‖ ≤ spread (frameBudget S Λ l n)* Hank Y H S n B * C
 grip : ‖rowFinish Y H n i D x - roving Y H n i (D.toExhibition.vistaFinish Y H n x)‖ ≤ ε*(spread (frameBudget S Λ l n)*ArcFee Y H S n B)*C
 reading : ‖rowTake Y H i D x - D.toExhibition.vistaTake Y H x‖ ≤ ε * Garland Y H D.toExhibition S n * C
include D
-- state on period limit read included. no `Present.extras` claims earlier.
lemma firedThrough : ∀ᶠ j in atTop, ∀ x C,Pocket κ S n C x→ Quart Y H D S n (a j) (propeller j) x C:=by
  have h:= (eventuallyReflection (fun i=>∀ x C,Pocket κ S n C x→ Allows Y H (d) S n (i₁ i) (k₁ i) x C (propeller i.vol))).1 ((Exhibition.horizon Y H D.toExhibition S n).mono fun i v=> v.2)
  filter_upwards [h] with i t x C v'
  have p := purePrices Y H n (a i) D S v'; obtain ⟨e,g⟩:= p
  have hx : ∀ᶠ j in atTop, Allows Y H D.toExhibition S n (a i) (b j) x C (propeller i) := (eventually_ge_atTop i).mono fun k w=> t k w x C v'
  exact ⟨rowSupport Y H D S n (a i) v', le_of_tendsto g.norm (hx.mono fun i h=> h.rangeLimit), le_of_tendsto ((g.sub_const (roving Y H n (a i) (D.toExhibition.vistaFinish Y H n x))).norm) (hx.mono fun i h=> h.grip), le_of_tendsto ((e.sub_const (D.toExhibition.vistaTake Y H x)).norm) (hx.mono fun i h=> h.reading)⟩ -- rowSupport order D S n? purePrices order imported

-- Couplet stature. qualification for physical clipping.
lemma livePocket {x:Cloud (Dome κ)}{C:ℝ}(p:Pocket κ S n C x):
    Tendsto (fun k : ℕ=> rowTake Y H (a k) D x) atTop (𝓝 (D.toExhibition.vistaTake Y H x)) ∧
    Tendsto (fun i=> taking Y H (i₁ i) (k₁ i) x) followStage (𝓝 (D.toExhibition.vistaTake Y H x)):= by
  let g:ℕ→ℝ:= fun i=>propeller i*Garland Y H (d) S n*C; have hd:Tendsto g atTop (𝓝 0):=by simpa using (propeller_fades.mul_const r).mul_const C
  exact ⟨steam g _ _ hd ((firedThrough Y H D S n).mono fun i t=> (t x C p).reading),steam (X:=ℂ) (L:=followStage) (g∘WedgeStage.vol) _ _ (hd.comp overStage) ((D.toExhibition.horizon Y H S n).mono fun i h=>(h.2 x C p).reading)⟩
lemma heightFare {x:Cloud (Dome κ)}(p:x∈shorter (Dome κ) n): ∀ (u:ℕ→ℕ), (∀ᶠ i:ℕ in atTop, legacy Y (a i) (b (u i))) → ∀ᶠ i:ℕ in atTop, Pay Y n (a i) (b (u i)):=by
  choose S v using anyWords κ n x p -- choose tactic only exists once?
  have e:= (eventuallyReflection (fun t=> Exhibition.Pavilion Y S n (i₁ t) (k₁ t))).1 (Exhibition.awarded Y H D.toExhibition S n); intro u h; exact (e.and h).mono fun i p=>(p.1 (u i) ((D.status _ _).mp p.2)).payZ
lemma heightUvs {x:Cloud (Dome κ)}(p:x∈shorter (Dome κ) n) : ∀ᶠ j in atTop, Tapestry.Pay Y n i (b j):= Exhibition.sharper Y H n i D.toExhibition
lemma heightCoupon {x: Cloud (Dome κ)}(p:x∈shorter (Dome κ) n) :
   Couplet a b (fun i k=>taking Y H i k x) (fun i=>rowTake Y H i D x) (D.toExhibition.vistaTake Y H x) (fun u=>∀ᶠ i in atTop, legacy Y (a i) (b (u i))):=by
  obtain ⟨S,v⟩:=anyWords κ n x p; obtain ⟨C,z⟩:= issued.mp v; have g:= livePocket Y H D S n z
  refine ⟨fun i=> (D.eachYear Y H n i p).1,g.1,fun t q=>?_⟩; apply Metric.tendsto_nhds.mpr; intro ε e; let f(t: WedgeStage):Prop:= dist (taking Y H (i₁ t) (k₁ t) x) (D.toExhibition.vistaTake Y H x)< ε; have h':∀ᶠ k in followStage,f k:=Metric.tendsto_nhds.mp g.2 ε e
  exact (((eventuallyReflection f).mp h').and q).mono fun i z=> z.1 (t i) ((D.status _ _).mp z.2)
lemma allCoupon {x:Cloud (Dome κ)}(p:x∈ FiniteGaugeDataPoly κ):
   Couplet a b (fun i k=>taking Y H i k x) (fun i=>rowTake Y H i D x) (D.toExhibition.vistaTake Y H x) (fun u=>∀ᶠ i in atTop, legacy Y (a i) (b (u i))):= heightCoupon Y H D (curve.mp p).choose (curve.mp p).choose_spec -- p not exists
end Fashion
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Fashion.firedThrough
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Fashion.allCoupon
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Fashion.heightFare
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Fashion.eachYear
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Fashion.rowGauge
