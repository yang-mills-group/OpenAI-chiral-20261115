import YM.CF.BProof.Vogue.Card
import Mathlib.Probability.Kernel.Representation
/-! Reconstruct uniform component from iid real tags. Symmetric operation (sum of bins)
and hence exact covariance componentwise. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Vogue
open Function Filter Set MeasureTheory Skye ProbabilityTheory Equiv
open scoped Topology BigOperators NNReal ENNReal Classical
private lemma announce (q:ℕ)[NeZero q]:∃ f:ℝ→ Fin q,MeasurePreserving f pale (paperMeas (Fin q)):=by
 haveI : Nonempty (Fin q):= ⟨0⟩
 obtain ⟨f,h,g⟩:= (paperMeas (Fin q)).exists_measurable_map_eq; obtain ⟨F,V,hf⟩:= unitInterval.measurableEmbedding_coe.exists_measurable_extend h (fun _=>⟨0⟩) -- check
 refine ⟨F,V,?_⟩; change Measure.map F (volume.restrict unitInterval) = _; rw [←unitInterval.measurePreserving_coe.map_eq,Measure.map_map V unitInterval.measurePreserving_coe.measurable,hf,g]
variable {K I J:Type*}[Fintype I][Fintype J]
variable (q:ℕ)[NeZero q]
def pitch :ℝ→Fin q:=(announce q).choose
lemma pitch_p: MeasurePreserving (pitch q) pale (paperMeas (Fin q)):=(announce q).choose_spec

section group
open Finset
variable (V:I→Finset J)(p:∀ i,(V i).Nonempty)(h:Pairwise (Disjoint on V))
include p h
-- uniform independent vector.Arbitrary consuming all tags.
def beans (x:J→ℝ)(i:I): Fin q:=∑ j∈V i,pitch q (x j)
lemma beans_exp: MeasurePreserving (beans q V) (Measure.pi (fun _=>pale)) (Measure.pi (fun _:I=> paperMeas (Fin q))):=by
 let f (x:J→ Fin q) (i:I):= ∑ j∈V i,x j
 have H : MeasurePreserving f (Measure.pi (fun _=>paperMeas (Fin q))) (Measure.pi fun _=>paperMeas (Fin q)) := by
    haveI: Nonempty (Fin q):=⟨0⟩; rw [← parcelPi,← parcelPi]; refine atomMP _ (measurable_of_countable _) (fun x y=>?_)
    choose g hg using p
    let A(j:J): Fin q:= ∑ i:I, Pi.single (M:=fun _:J=>Fin q) (g i) (y i-x i) j; let Z:= Equiv.addRight A; refine ⟨Z, orderMP Z,fun i=>?_⟩
    have hk(k:I): f A k=y k-x k:= by
       unfold f A; rw [sum_comm]; rw [sum_eq_single k] -- tune notation
       · rw [sum_eq_single (g k)]; · simp
         · exact fun j _ hj=> Pi.single_eq_of_ne hj _
         exact fun v=> (v (hg k)).elim
       · intro b _ hb; exact sum_eq_zero fun j hj=>Pi.single_eq_of_ne (fun (v:j=g b)=> Finset.disjoint_left.mp (h (Ne.symm hb)) hj (show j∈ V b from v.symm ▸ hg b)) _
       simp
    have he : f (Z i)= f i+ y - x:=by ext k:1; change (∑ j ∈ V k,(i j+A j))=_; rw [sum_add_distrib,show ∑ j∈V k,A j=y k-x k from hk k]; simp only [Pi.sub_apply, Pi.add_apply, add_sub_assoc]; rfl
    rw [he]; grind -- group
 have G:MeasurePreserving (fun x:J→ℝ=>pitch q ∘ x) (Measure.pi (fun _:J=> pale)) (Measure.pi fun _:J=> paperMeas (Fin q)):= measurePreserving_pi (fun _=>pale) (fun _=>paperMeas (Fin q)) (f:=fun _=>pitch q) (fun _=>pitch_p _)
 exact H.comp G
end group
-- projecting sweeps at any choice function
lemma coupon (K:Type*)[Fintype K][Nonempty K][MeasurableSpace K][MeasurableSingletonClass K](s:I→ J)(p:Injective s) : MeasurePreserving (fun x:J→K=> x ∘ s) (Measure.pi (fun _:J=> paperMeas K)) (Measure.pi (fun _:I=>paperMeas K)):=by
 classical
 rw [← parcelPi,← parcelPi]; refine atomMP _ (measurable_of_countable _) (fun x y=>?_); let w(i:J): Perm K:= if u:∃ j,s j=i then Equiv.swap (x u.choose) (y u.choose) else Equiv.refl _
 have hv(i:I): w (s i) (x i)= y i:=by unfold w; rw [dif_pos (show ∃ j,s j=s i from ⟨_,rfl⟩)]; set h:= Exists.choose _; rw [show h=i from p (Classical.choose_spec (show ∃ j,s j=s i from ⟨_,rfl⟩)),Equiv.swap_apply_left]
 let e:Equiv.Perm (J→K):= Equiv.piCongrRight w; refine ⟨e,orderMP _,fun i=>?_⟩
 exact ⟨fun h=>funext fun j=> by change w (s j) ((i ∘ s) j)=y j; rw [h,hv],fun h=>funext fun j=>(w (s j)).injective ((congrFun h j).trans (hv j).symm)⟩ -- inj expected metavars stuck
end YM.CF.BProof.Vogue
