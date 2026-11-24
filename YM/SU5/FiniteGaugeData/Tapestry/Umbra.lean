import YM.SU5.FiniteGaugeData.Tapestry.Margins
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
# Uniform changing supports/heights lemmas. Part 1: actual inner cutoff
(Signed Course, its exposure at each fixed period and actual momentum binder).
This statement and `Capsule` (all-frame cone) are complementary. Supply genuine
piece convergence at fixed observing height n (to the prepared mark reader
constructed using the UV limit F,Q and that row's whole Torus !), in op norm
sense on indicated inputs. Scalar probabilities already priced. Note the row &
UV all* heights first carried here (unlike late-stage cone).
-/
set_option quotPrecheck false
section
-- another usable result from herring and timing inner. refer `Echappe`
variable {Z:ℕ→ Side}
local notation "U"=> fun i=> Ward (Z i)
lemma upperUvBound (p:ℕ→ Ballet Z)(a:Ballet Z)(n:ℕ)(q:∀ i,Tendsto (fun k=>p k i) atTop (𝓝 (a i))): ∀ ε:ℝ,0<ε→ ∀ᶠ k in atTop,∀ x:(∀ i :ℕ,Ward (Z i)), ‖accolading Z (p k) n x-accolading Z a n x‖ ≤ ε*nectar n x:=by
 intro ε e
 let M(i:ℕ):=1+‖a i‖; let X:=awardStart (Z 0); let V(i:ℕ):=blossom (Z (i+1))
 let W:=fun _:ℕ=>(1:ℝ); let g:∀ i,0≤ M i:=fun i=>add_nonneg zero_le_one (norm_nonneg (a i)); let s:= discrepancy (X:=fun i=> Ward (Z i)) (Y:=fun i=>Ward (Z i)) X V a M W n; have hs:0≤ s:=feePos (X:=fun i=>Ward (Z i)) (Y:=fun i=>Ward (Z i)) X V a M g W n (fun i=> zero_le_one) -- ≤ s notation
 let d:= min 1 (ε/(1+s)); have hd:0<d:=by unfold d; positivity
 have hp:d*s≤ ε:=by
    have ht: d*(1+s)≤ ε:= (le_div_iff₀ (by positivity)).1 (min_le_right ..); linarith
 filter_upwards [(eventually_all_finset (Iic n)).mpr fun i t=> Altitude.glimpse (Y:=fun i=>Ward (Z i)) a p q i d hd] with k t x
 refine (Altitude.reckons (X:=fun i=>Ward (Z i)) (Y:=fun i=>Ward (Z i)) X V (p k) a M W n ?_ ?_ x).trans (mul_le_mul_of_nonneg_right hp (licensedN ..))
 · intro i h; change _≤d*1; rw [mul_one]; exact t i (mem_Iic.mpr h.le)
 intro i h; exact opPriceBelow (V:=Ward (Z i)) (W:=Ward (Z (i+1))) ((t i (mem_Iic.mpr h.le)).trans (min_le_left ..)) (le_refl ‖a i‖)

-- absolute prices select below arguments
lemma zeroPricedTrend {X Y:Type*} [NormedAddCommGroup X] {L:Filter Y}{f:Y→X}{x:X}{C:ℝ}(v:0≤C)(h:∀ ε:ℝ,0<ε→ ∀ᶠ y in L, ‖f y-x‖≤ ε*C): Tendsto f L (𝓝 x):=by
  apply Metric.tendsto_nhds.mpr; intro ε e; let M:= ε/(C+1); have p:0<M:=by unfold M; positivity
  have he:M*(C+1)=ε:=div_mul_cancel₀ _ (by positivity); exact (h M p).mono fun i x=> by rw [dist_eq_norm]; linarith
end
section
variable {Λ: Preparation} {l : ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l)) (H:Real.exp 1 ≤ Λ.x) (n i:ℕ)
local notation "κ"=> tent Y H
variable {a b:ℕ→ℕ} {I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{L:Rack Λ l}{B:Clay Λ l}{T:ℕ→ℕ→Tariff}{t:ℕ→Tariff}(D:Fashion Y H a b I E L B T t)
variable (S:BillOfWork)
local notation "Ω" j:max=> side Y i j
namespace Fashion
include D
lemma respiring (ε:ℝ)(e:0<ε): ∀ᶠ k in atTop,∀ x : Employee S, Clocked (K:=tent Y H) S n x→
    ‖breathing Y H n i (b k) (motif κ S x)-rowFinish Y H n i D (motif κ S x)‖ ≤ ε*nectar n x:=by
  let s:= cloudSpan n S; have h:0 ≤ s:=cloudSpan_pos n S; let d:=ε/(s+1); have hd:0<d:=by unfold d; positivity
  let Z:=fun j:ℕ=> Ω j
  have hp: d*s ≤ ε:=by have he:d*(s+1)=ε:=div_mul_cancel₀ _ (by positivity); linarith
  filter_upwards [upperUvBound (Z:=fun j=>side Y i j) (fun k=>stageRoll Y i (b k)) (stageInner Y i T) n (fun j=> performUV Y H j i D) d hd] with k w x h'
  unfold motif; rw [breathing_pure Y H n i (b k) _ h',rowFinish,show pureShot κ _=PiTensorProduct.tprod ℂ _ from rfl, Decking.reckon_paid _ _ _ h',← enjoysRow,← enjoying] -- tune
  exact (w (impetus Y H i (employ κ S x))).trans ((mul_le_mul_of_nonneg_left (fanPrice Y H i n S x) hd.le).trans (by rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right hp (licensedN ..)))
omit D
structure Insight (D:Fashion Y H a b I E L B T t)(S:BillOfWork)(n i k:ℕ)(ε C:ℝ)(A:ℝ)(x: Cloud (Dome (tent Y H))):Prop where
 payZ : Tapestry.Pay Y n i k
 annual : AtSupport false (region (frameBudget S Λ l n) (side Y i n)) (attire (breathing Y H n i k x))
 scaleM: ‖breathing Y H n i k x‖ ≤ C*A -- paid after row threshold. no heat comparison here
 bill : ‖breathing Y H n i k x-rowFinish Y H n i D x‖ ≤ ε*A
 spent : ‖taking Y H i k x-rowTake Y H i D x‖ ≤ ε*A
include D
lemma notices : ∃ C:ℝ,0 ≤ C∧∀ ε:ℝ,0<ε→ ∀ᶠ k in atTop, (Tapestry.Pay Y n i (b k)) ∧ ∀ A:ℝ, ∀ x:Cloud (Dome (tent Y H)), Pocket κ S n A x→ Insight Y H D S n i (b k) ε C A x:=by
 obtain ⟨C,c,H'⟩:= spinning Y H i n D S; refine ⟨C,c,fun ε e=>?_⟩
 filter_upwards [H',D.respiring Y H n i S ε e,D.uvBudget Y H i n S ε e] with k h u v; refine ⟨h.1,fun A x q=> ?_⟩
 let t:= breathing Y H n i (b k)
 exact ⟨h.1, textureBudget Y H S n i (b k) h.1 x q,q.bequeath t c (fun x u=>by unfold t motif; rw [breathing_pure _ _ _ _ _ _ u]; exact h.2 x), q.bequeath (t-rowFinish Y H n i D) e.le u,q.bilAsk _ _ e.le v.2 ⟩

lemma purePrices {x:Cloud (Dome (tent Y H))} {C} (q:Pocket κ S n C x): Tendsto (fun k=> taking Y H i (b k) x) atTop (𝓝 (rowTake Y H i D x)) ∧ Tendsto (fun k=> breathing Y H n i (b k) x) atTop (𝓝 (rowFinish Y H n i D x)):=by
  obtain ⟨z,u,H'⟩:= notices Y H n i D S; exact ⟨zeroPricedTrend q.priced (fun ε e=> (H' ε e).mono fun y u=> (u.2 _ _ q).spent), zeroPricedTrend (X:=Ward (side Y i n)) (Y:=ℕ) q.priced (fun ε e=> (H' ε e).mono fun y u=> (u.2 _ _ q).bill) ⟩
end Fashion
end
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Fashion.notices
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Fashion.purePrices
