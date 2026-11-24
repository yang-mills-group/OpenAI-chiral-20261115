import YM.SU5.FiniteGaugeData.Dally.Archon
import ZecaQuote
set_option autoImplicit false
set_option maxHeartbeats 270000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder


open Poin.Gem Poin Poin.Galleon Poin.Galleon.Dai Leal Leal.Breve
  Celeritas Land
variable {K : Axis → Hilbert} (W : ∀ i : Axis, OS.Semigroup (K i) i)
    {ι : Type} (N : Canopy (K timeAxis) ι) (A : Tribe N)
    (ω : ∀ i, (K i).space) (j : Axis)
namespace Gilt

variable (u : N.Chip)
















/--  One coin, with axis j as time. -/
def coin : Moment (K j):=⟨N.grade u,useB N A u j⟩

abbrev Crown:= N.Chip × {v:ℝ≥0 //0<v}
def stamped (v:Crown N) : Shrine K:=
 ⟨fun _=>v.2.val, fun j=>(coin N A j v.1).cost (W j) v.2.val v.2.val⟩

def sooner (n:ℕ) : {v:ℝ≥0 //0<v}:=⟨1/((n:ℝ≥0)+1),by positivity⟩

/-- canonical Fleet. -/
def fleet : Fleet W N A (stamped W N A) where
 book t n := (t,sooner n)
 back := by
  intro t
  have h : Tendsto (fun n=>(sooner n).val) atTop (𝓝 0):=by
    apply NNReal.tendsto_coe.mp
    simpa [sooner] using (show Tendsto (fun n:ℕ=>1 / ((n:ℝ)+1)) atTop (𝓝 0) from tendsto_one_div_add_atTop_nhds_zero_nat)
  refine ⟨fun _=>h,?_⟩
  intro j
  suffices e: Wot (fun n=>(W j).E (sooner n).val *
       useB N A t j * (W j).E (sooner n).val) (useB N A t j) by
     change Wot (fun n=>
        Cache (W j) (N.grade t)*
          (Par (W j) (N.grade t) (sooner n).val * useB N A t j *
            Par (W j) (N.grade t) (sooner n).val) * Cache (W j) (N.grade t)) _
     simp_rw [← mul_assoc,fun i=>P_Heq (W j) _ (N.grade t) (sooner i).property,
          mul_assoc,
          fun n=>
              (show Commute (Par (W j) (N.grade t) (sooner n).val) (Cache (W j) (N.grade t)) from
                 ((gear (W j) _ (dur.mpr (sooner n).property) (N.grade t)).pow_left (N.grade t)).symm).eq,
          fun i=>P_Heq (W j) _ (N.grade t) (sooner i).property,←mul_assoc]
     exact e
  let d:=(W j)
  let q:=useB N A t j
  let e(n:ℕ):= d.E (sooner n).val
  refine ⟨⟨‖q‖,Eventually.of_forall fun n=>?_⟩,?_⟩
  · calc
      _ ≤ ‖e n*q‖ * ‖e n‖:=norm_mul_le ..
      _ ≤ (‖e n‖*‖q‖)*1:= mul_le_mul (norm_mul_le ..) (d.shrinks ..) (norm_nonneg _) (by positivity)
      _ ≤ _:= by rw [mul_one];exact mul_le_of_le_one_left (norm_nonneg _) (d.shrinks ..)
  have E (y:K j):Tendsto (fun n=>e n y) atTop (𝓝 y):=
     ((d.continuousE y).tendsto' 0 y (congrArg (fun a:(K j).Op=>a y) d.eZero)).comp h
  intro x y
  simp_rw [ContinuousLinearMap.mul_apply, ← OS.Semigroup.swing]
  exact (E x).inner (((useB N A t j).continuous.tendsto y).comp (E y))

lemma sealC : Stamp W N A (Set.range (stamped W N A)):=by
  refine ⟨fun t=>?_⟩
  let g:=fleet W N A
  exact ⟨_, fun k=>⟨_, ⟨g.book t k,rfl⟩,rfl⟩, g.back t⟩

#print axioms sealC
#print axioms fleet

variable {n:ℕ}(x:Points n)(v:Fin n→Crown N)
local notation "spz"=>fun i:Fin n=>SEP j (x i)

abbrev quoteG (w:Fin n→N.Chip)(L:List (Fin n)) :=
 quoteL (W j) (ω j) (coin N A j ∘ w) (spz) (clockV j x) L

lemma stamped_paid (L:List (Fin n))
 (h:saucer (W j) (ω j)=ω j)
 (p:L.Pairwise (Seers (stamped W N A ∘ v) x.ofLp j)):
 chorus W ω (stamped W N A ∘ v) x.ofLp L j=
 quoteG W N A ω j x (fun i=>(v i).1) L:=by
 let f:=fun i=>(v i).2.val
 let w:=fun i=>(v i).1
 let u := stamped W N A ∘ v
 let D:=coin N A j ∘ w
 change _=quoteL (W j) (ω j) D (spz) _ L
 rw [quoteL_paid (W j) _ _ _ (clockV j x) f f h _ (fun i _=>(v i).2.property)
         (fun i _=>(v i).2.property)
         (List.Pairwise.imp (fun i=>le_of_lt i) p)] -- inference?
 have e: actO W u x.ofLp j=padOp (W j) D (spz) f f:=
  funext fun i=>barry W j (u i) (x i)
 unfold chorus quotePaid
 rw [comparator,e];rfl

lemma coronet (w:Fin n→N.Chip)(L:List (Fin n))
 (p:ProofOrder x j L):
 quoteG W N A ω j x w L=evaluate x W N ω A w L j:= by
 rw [utop]
 apply congrArg (fun f:(K j).Op=>inner ℂ (ω j) (f (ω j)))
 let u := lodgedOp (W j) (coin N A j ∘ w) (spz)
 let v:=clockV j x
 let d:=leap0 (W j) (coin N A j ∘ w) v
 let e:=Poin.rho (W j) (N.credit w) v
 have e0 (a b:Fin n)(p:v a<v b):d a b=e a b:=by
   simp only [e,Poin.rho,Par,d,leap0,OS.Semigroup.duration,Real.coe_toNNReal _ (sub_nonneg.mpr p.le)]
   rfl
 change Film u d L = Film u e L
 induction L with
 | nil=>rfl
 | cons i L ih=>
    obtain ⟨h,k⟩ := List.pairwise_cons.mp p
    rw [Film_step,Film_step,ih k]
    cases L with
    | nil=>rfl
    | cons b L=>
       simp only [clip]
       rw [e0 i b (h b List.mem_cons_self)]
#print axioms stamped_paid
#print axioms coronet
