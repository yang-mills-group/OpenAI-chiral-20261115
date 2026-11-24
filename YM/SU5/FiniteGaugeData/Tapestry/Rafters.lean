import YM.SU5.FiniteGaugeData.Tapestry.Echappe
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 440000
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
# Practice of Roof Window at EVERY period and common cutoff sequences.

Use complete local Torus within that fixed row. No need for that row to pay a
projection estimate based on supports actually embedding there (though those
claims remain available; only these all* rows see the early periods legalized).
We also pay in terms of Cover costs for such movies.
-/
set_option quotPrecheck false
variable {Λ: Preparation} {l : ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l)) (H:Real.exp 1 ≤ Λ.x)
variable (i k n:ℕ)(x:sequenceOf (tent Y H))
local notation "κ"=> tent Y H
local notation "Sx" n:max=> side Y i n
local notation "Z"=>fun i' : ℕ=> side Y i i'
abbrev stageRoll : Ballet (fun j=> side Y i j):=fun j=> music Y j i k
local notation "Q₀" k:max => stageRoll Y i k
def impetus : ∀ j:ℕ,Ward (side Y i j):=fun j=> roving Y H j i (x j)
lemma enjoying : accolading (fun j=> side Y i j) (stageRoll Y i k) n (impetus Y H i x)= (tidalDressing Y H i k).finish n x := by
 induction n with| zero=> rfl| succ n ih=> rw [awards_succ,Decking.finish,ih]; rfl
lemma fizzyMoving (p:Pay Y n i k)(q:Altitude.Enough n x):
 savings Y n i k (accolading (fun j=> side Y i j) (stageRoll Y i k) n (impetus Y H i x))= taking Y H i k (pureShot κ x):=by rw [breathing_fin _ _ _ _ _ _ p (board (P:={f|Altitude.Enough n f}) q),breathing_pure _ _ _ _ _ _ q,enjoying]

lemma wearRate (S:Finset Cover) (u:Swatch S) : ‖roving Y H n i (badge κ S u)‖ ≤ spread S*‖u‖:= Ward.save _ (present_bound Y H n i S u)
lemma fanPrice (S:BillOfWork)(x:Employee S):
 nectar n (impetus Y H i (employ κ S x)) ≤ (∏ i∈ Iic n,spread (S i))*nectar n x:=by
  apply le_trans (nectarBelow (X:=fun j=>Ward (side Y i j)) n _ (f:=fun i=> spread (S i)*‖x i‖) (fun j _=> wearRate Y H i j (S j) (x j)))
  rw [prod_mul_distrib, nectar_eq]
variable {a b:ℕ→ℕ} {I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{L:Rack Λ l}{B:Clay Λ l}{T:ℕ→ℕ→Tariff}{t:ℕ→Tariff} (D:Fashion Y H a b I E L B T t)
namespace Fashion
abbrev stageInner (T:ℕ→ℕ→Tariff): Ballet (fun j=> side Y i j):=fun j=> rhythm Y j i (T j i)
local notation "F"=> D.toExhibition
local notation "Q₁" => stageInner Y i T -- κ irrelevant
lemma enjoysRow : accolading (fun j=> side Y i j) (stageInner Y i T) n (impetus Y H i x)= (rowDressing Y H i D).finish n x := by induction n with| zero=> rfl| succ n ih=> rw [awards_succ,Decking.finish,ih]; rfl
lemma fizzyRow (q:Altitude.Enough n x):
 (F).refreshments Y H n i (accolading (fun j=> side Y i j) (stageInner Y i T) n (impetus Y H i x))= rowTake Y H i D (pureShot κ x):=by rw [rowCall Y H n i _ D (board (P:={f|Altitude.Enough n f}) q)]; rw [rowFinish,Decking.reckon_paid _ _ _ q,enjoysRow _ _ _ _ _ D] -- order n i for enjoys?
include D
lemma native_uv : ∀ ε:ℝ,0<ε→ ∀ᶠ j:ℕ in atTop, Pay Y n i (b j) ∧ ∀ x:sequenceOf (tent Y H), Altitude.Enough n x→
    ‖taking Y H i (b j) (pureShot κ x)-rowTake Y H i D (pureShot κ x)‖ ≤ ε*nectar n (impetus Y H i x):=by
  intro ε e; let q:ℕ→Ballet Z:= fun j=> stageRoll Y i (b j); let g: Ballet Z:= stageInner Y i T; let p(t):= savings Y n i (b t)
  have h : ∀ j,Tendsto (fun k=> q k j) atTop (𝓝 (g j)):= fun j=>D.performUV Y H j i
  filter_upwards [summery (fun j=>side Y i j) q g n h p ((F).refreshments Y H n i) (D.uv_strength Y H n i) ε e,(F).sharper Y H n i] with t h1 h2
  exact ⟨h2,fun x ht=>by rw [←fizzyMoving Y H i (b t) n x h2 ht, ←fizzyRow Y H i n x D ht]; exact h1 _⟩
variable (S:BillOfWork)
def cloudSpan:ℝ:= ∏ i∈ Iic n,spread (S i)
omit D
lemma cloudSpan_pos : 0≤cloudSpan n S := Finset.prod_nonneg fun i _=> Nat.cast_nonneg _
include D
lemma uvBudget(ε:ℝ)(e:0<ε): ∀ᶠ j in atTop, Pay Y n i (b j) ∧ ∀ x:Employee S, Clocked (K:=tent Y H) S n x→
    ‖taking Y H i (b j) (motif κ S x)-rowTake Y H i D (motif κ S x)‖ ≤ ε*nectar n x:=by
  let s:= cloudSpan n S; have h:0≤ s:=cloudSpan_pos n S
  let w:=ε/(s+1); have p:0<w:=by unfold w; positivity
  filter_upwards [native_uv Y H i n D w p] with k q
  have t:w*s≤ ε:=by have he : w*(s+1)=ε:= div_mul_cancel₀ _ (by positivity); linarith
  refine ⟨q.1,fun x u=>?_⟩; exact (q.2 (employ κ S x) u).trans ((mul_le_mul_of_nonneg_left (fanPrice Y H i n S x) p.le).trans (by rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right t (licensedN ..)))
-- op bound at actual native: still on all sufficiently late cutoffs of THAT period along actual b
lemma spinning : ∃ C:ℝ, 0≤ C ∧ ∀ᶠ j in atTop, Pay Y n i (b j) ∧ ∀ x:Employee S, ‖(tidalDressing Y H i (b j)).finish n (employ (tent Y H) S x)‖ ≤ C*nectar n x:=by
 let q:ℕ→ Ballet (fun n=>side Y i n):=fun j=>stageRoll Y i (b j); let g:= stageInner Y i T; have he:∀ j,Tendsto (fun k=> q k j) atTop (𝓝 (g j)):=fun j=>D.performUV Y H j i
 obtain ⟨v,p,h⟩:= ballroom (fun n=>side Y i n) q g n he
 refine ⟨v * cloudSpan n S,mul_nonneg p (cloudSpan_pos ..),?_⟩
 filter_upwards [h,(F).sharper Y H n i] with j h p'; refine ⟨p',fun x=>?_⟩; rw [←enjoying,mul_assoc]; exact (h (impetus Y H i (employ κ S x))).trans (mul_le_mul_of_nonneg_left (fanPrice Y H i n S x) p)
end Fashion
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Fashion.uvBudget
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Fashion.native_uv
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Fashion.spinning
