import YM.SU5.Reconstruction.Anvil.Gap
/-! # True spacelike obligation for metered slits. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Anvil
open Function Set Filter Metric InnerProductSpace OS Semigroup Finset
open scoped Topology BigOperators Classical
-- all or subset. theorem formulate choose flag in K→ positive.Complement.
variable (a: Axis) (Δ:Finset Axis)(tC : a ∉ Δ) (d u f v:Axis→ℝ) (x:Meter)(e:x a=0)(t:ℝ)
abbrev CubePay (d u:Axis→ℝ): Set Meter:= {y| y a=0 ∧ ∀ i∈ Δ,y i ∈ Set.Icc (d i) (d i+u i)}
-- sectors input width positive in time too; optional
structure DisjointPay : Prop where
  widths : (∀ i∈Δ,0≤ u i) ∧ (∀ i∈Δ,0≤ v i)
  fares (y z:Meter)(p:y∈ CubePay a Δ d u)(q:z∈ CubePay a Δ f v) : t^2 < ‖rimPay a (z+x-y)‖^2
namespace DisjointPay
-- one-coordinate positions
abbrev aft (d u f v:ℝ) (w:Bool):ℝ:= if w then f-d-u else d-f-v
def gap (d u f v:ℝ):= max 0 (max (aft d u f v true) (aft d u f v false))
private lemma costAt (d u f v:ℝ)(p:0≤u)(q:0≤v): ∃ x∈ Set.Icc d (d+u),∃ y∈ Set.Icc f (f+v),|y-x|=gap d u f v:=by
 by_cases h:d+u<f
 · refine ⟨d+u,Set.right_mem_Icc.mpr (by linarith), f,Set.left_mem_Icc.mpr (by linarith),?_⟩; simp only [aft,gap,reduceCtorEq,if_true,if_false]; rw [abs_of_pos (sub_pos.mpr h),max_eq_left (show d-f-v≤ f-d-u from ?_)]; swap; -- tune
   · linarith
   rw [max_eq_right]; ring; linarith
 by_cases e:f+v<d
 · refine ⟨d,Set.left_mem_Icc.mpr (by linarith),f+v,Set.right_mem_Icc.mpr (by linarith),?_⟩; unfold gap; simp only [aft,reduceCtorEq,if_true,if_false]; rw [abs_of_neg (sub_neg.mpr e),max_eq_right (show f - d - u ≤ d-f-v from by linarith),max_eq_right (by linarith)]; ring
 refine ⟨max d f,⟨le_max_left ..,max_le (by linarith) (le_of_not_gt h)⟩, max d f,⟨le_max_right ..,max_le (le_of_not_gt e) (by linarith)⟩,?_⟩; simp [gap,aft, h]; constructor <;> linarith
local notation "F" i:max=> (f i+x i)
variable (p:DisjointPay a Δ d u f v x t)
def activeFee : Finset Axis:= Δ.filter fun i=> 0< gap (d i) (u i) (f i + x i) (v i)
include p tC
lemma exact_toll : t^2 < ∑ i ∈ DisjointPay.activeFee Δ d u f v x,(gap (d i) (u i) (f i+x i) (v i))^2:= by
 choose R R0 W W0 G using fun (i:↥Δ) => costAt (d i) (u i) (F i.val) (v i) (p.widths.1 i i.property) (p.widths.2 i i.property) -- order errors nested ∃ x∈Set...
 let r:Meter:=fun i=>if h : i∈Δ then R ⟨i,h⟩ else 0
 let q:Meter:=fun i=> if h:i ∈ Δ then W ⟨i,h⟩ -x i else if i=a then 0 else -x i; --
 have f0 (y:Axis)(h:y∈Δ):= G (⟨y,h⟩ : ↥Δ)
 have hx(i)(h:i∈Δ):r i∈ Set.Icc (d i) (d i+u i):=by unfold r; rw [dif_pos h]; exact R0 ⟨i,h⟩
 have hz(i)(h:i∈Δ):q i∈ Set.Icc (f i) (f i+v i):= by unfold q; rw [dif_pos h]; obtain ⟨b,c⟩:= W0 (⟨i,h⟩:↥Δ); dsimp at b c; exact ⟨by linarith,by linarith⟩
 refine (p.fares r q ⟨by simp [r,tC],hx⟩ ⟨by simp [q,tC],hz⟩).trans_eq ?_
 have hp(i:Axis)(h:i∈Δ): ((q+x-r) i)^2=(gap (d i) (u i) (F i) (v i))^2:= by
   have he:=f0 i h; rw [Pi.sub_apply,Pi.add_apply]; unfold r q; rw [dif_pos h,dif_pos h,← sq_abs ((_:ℝ) - _),sub_add_cancel]; rw [he]
 rw [rimPay_norm]; symm;
 calc
  _ = ∑ i∈Δ,(gap (d i) (u i) (F i) (v i))^2 := by
    refine Finset.sum_subset (filter_subset ..) (fun i t c=> ?_)
    rw [activeFee,mem_filter,not_and] at c; rw [le_antisymm (le_of_not_gt (c t)) (le_max_left ..),zero_pow (by decide)]; -- tune
  _ = ∑ i∈ Δ, ((q+x-r) i)^2:= Finset.sum_congr rfl fun i h=>(hp i h).symm
  _ = _:= by
    refine Finset.sum_subset (fun i h=> mem_erase.mpr ⟨fun v=> tC (v ▸ h),mem_univ _⟩) (fun i h e=> ?_)
    simp [q,r,ne_of_mem_erase h,e]
end DisjointPay
end YM.Anvil
