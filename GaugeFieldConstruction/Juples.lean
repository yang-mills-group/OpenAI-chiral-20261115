import GaugeFieldConstruction.Clifford97
/-!
# Touch dust for translations/rotations. Prescriptions before raw projection.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 5000
noncomputable section
namespace YM.GaugeFieldConstruction.Flux.One
open Gap Complex Cauchy Row Wick Phys Function Set Filter Submodule
open YM.Maxwell (grad)
open Matter (Slot)
open scoped Topology ContDiff BigOperators
variable {α β γ : Type*}
namespace Lamp
lemma emptyT {L : Lamp α β} {K c} : L.Touch K c 0 0 := by
  intro x y χ v d; simp [glow,Shell, Flux,currentZ,toll,YM.Maxwell.Free.exportFlux]
lemma sums_T {L : Lamp α β} {K c} (p : Course K) (V : Finset γ) (a b : γ → J α)
    (w : ∀ i ∈ V,L.Touch K c (a i) (b i)) : L.Touch K c (∑ i ∈ V,a i) (∑ i∈ V,b i) := by
  classical
  induction V using Finset.induction_on with
  | empty => simp [emptyT]
  | insert i v h ih=> rw [Finset.sum_insert h,Finset.sum_insert h]; exact L.plus p (w i (by simp)) (ih (fun j e=>w j (by simp [e])))

def crew (L : Lamp α β) {K} (p : Course K) (c : ℂ) : Submodule ℂ (J α × J α) where
  carrier:={a| L.Touch K c a.1 a.2}
  zero_mem':=emptyT; add_mem' h g:= L.plus p h g; smul_mem' r _ h:= L.wish h r
end Lamp
open Lamp
variable {K : Dollars} (p : Course K) (V : Bool → ℂ) (c d : Slot)
/-- Each pair, cost at Slot equal. store simultaneously bought u and its Y_B charge. -/
def bu (b : Bool) (c : Slot) (v : CJet × CJet) := (Glove (fStress V) b).Touch K (V (rad c)) (atop c v.1) (atop c v.2)

def tm (i j : CJet×CJet): J f × J f := (times' i.1 j.1,times' i.2 j.1+times' i.1 j.2)
def ready (K : Dollars) : Submodule ℂ (J f × J f) := span ℂ {x | ∃ i j, bu (K:=K) V false c i ∧ bu (K:=K) V true d j ∧ tm i j=x} -- unused p omitted intentional



def boost (A : Lattice) (b : Bool)(k : Axis) (v : CJet×CJet): CJet × CJet := (Cder b k v.1,Cder b k v.2+∑ j:Axis,(A j k:ℂ) • Cder b j v.1)
lemma bu_ext (p : Course K) {Ω : Ortho.Skew} (h : Toll K Ω.val) (c : Slot) (i k) {v} (w : bu (K:=K) V i c v): bu (K:=K) V i c (boost Ω.val i k v) := by
  let L := Glove (fStress V) i
  change L.Touch K (V (rad c)) (atop c _) (atop c _)
  dsimp only [boost]
  rw [map_add,map_sum]; simp_rw [map_smul]
  simp_rw [here _ c]; exact L.expand p h w k
lemma acts (p : Course K) {c d} (u : rad c=rad d) (v : J f × J f) (h : v∈ready (K:=K) V c d) :
    (gloF (fStress V)).Touch K (V (rad c)) (sD c d v.1) (sD c d v.2) := by
  let L := gloF (fStress V)
  suffices T: ready (K:=K) V c d ≤ comap (LinearMap.prodMap (sD c d) (sD c d)) (crew L p (V (rad c))) by exact T h
  unfold ready; apply span_le.mpr
  rintro _ ⟨x,y,h,p',rfl⟩
  change L.Touch _ _ (sD c d (tm x y).1) (sD c d (tm x y).2)
  have he:= (Glove (fStress V) false).merger (Glove (fStress V) true) p h (show (Glove _ true).Touch K (V (rad c)) _ _ from by rw [u]; exact p')
  dsimp only [tm]; rw [map_add,sD,straps,straps,straps]
  exact to_touch he (Phys.swap Mode)

-- x H. normalized B index proof
lemma f_bought (p : Course K) {Ω: Ortho.Skew} (w : Toll K Ω.val) (j : Axis) :
    (B j, ∑ i:Axis,(Ω.val i j:ℂ) • B i)∈ ready (K:=K) V c d := by
  let M:= ready (K:=K) V c d
  let q (r s : Spin):= tm (C r 0,Wf Ω.val false r) (C s 0,Wf Ω.val true s)
  have hu i j:q i j∈M:= subset_span ⟨(C i 0,Wf Ω.val false i),(C j 0,Wf Ω.val true j),lampF p w V false c i,lampF p w V true d j,rfl⟩
  have ht : (∑ i:Spin,∑ l:Spin,Hij j i l • q i l) ∈ M:= by apply Submodule.sum_mem; intro i _; apply Submodule.sum_mem; intro l _; exact smul_mem _ _ (hu i l)
  have he : (∑ i:Spin,∑ l:Spin,Hij j i l • q i l) = (B j,∑ i:Axis,(Ω.val i j:ℂ) • B i) := by
    apply Prod.ext
    · simp only [Prod.fst_sum,Prod.fst_smul,tm,B,q]; rfl -- tune
    change (∑ i:Spin,∑ l:Spin,Hij j i l • q i l).2= ∑ i:Axis,(Ω.val i j:ℂ) • B i
    have hp (a:Spin×Spin) (r:ℂ): (r • q a.1 a.2).2=r • (q a.1 a.2).2:=rfl
    simp only [Prod.snd_sum]
    have hv (i l) (r : ℂ) : (r • q i l).2= r • ((times' (Wf Ω.val false i) (C l 0))+(times' (C i 0) (Wf Ω.val true l))) := rfl
    simp_rw [hv,B,smul_add,Finset.sum_add_distrib,Wf,map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,Finset.smul_sum,smul_smul]
    -- explicit reorder
    let T (a b) := times' (C a 0) (C b 0)
    have Hx : (∑ a:Spin, ∑ b:Spin, (∑ i:Spin, (Hij j a b*theta Ω.val false i a ) • T i b))=
        ∑ i:Spin,∑ b:Spin, (∑ a:Spin,(Hij j a b * theta Ω.val false i a ) • T i b) := by
      simp_rw [Finset.sum_comm (f:=fun b i=> (Hij j _ b * theta Ω.val false i _ ) • T i b)]; rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun i _=> Finset.sum_comm
    rw [Hx]; simp_rw [Finset.sum_comm (f:=fun b l => (Hij j _ b*theta Ω.val true l b ) • times' (C _ 0) (C l 0)), ← Finset.sum_add_distrib]
    conv_rhs=>rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    conv_rhs=>rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro l _
    have hh := congr_arg (fun r:ℂ=> r • T i l) (label_fee Ω j i l); simp only [add_smul,Finset.sum_smul] at hh
    rw [← hh]; -- inner sums merged by ←sum_add?
    simp_rw [Finset.sum_add_distrib]; simp only [T, mul_comm]
  rw [← he]; exact ht

def DD (A : Lattice) (X : Axis→ Module.End ℂ (J f)) (k : Axis) : Module.End ℂ (J f× J f) := LinearMap.prod (X k ∘ₗ LinearMap.fst ℂ _ _)
  (X k ∘ₗ LinearMap.snd ℂ _ _ + (∑ i:Axis,(↑(A i k):ℂ) • X i) ∘ₗ LinearMap.fst ℂ _ _)
lemma costD A X k a b: DD A X k (a,b) = (X k a,X k b +∑ i:Axis,(A i k:ℂ) • X i a) := Prod.ext rfl (by change X k b+(∑ i:Axis,(↑(A i k):ℂ) • X i) a = _; rw [LinearMap.sum_apply]; rfl)

include p
lemma Psmart {Ω:Ortho.Skew} (g:Toll K Ω.val) (k : Axis) (X) (v : X∈ready (K:=K) V c d) : DD Ω.val P_f k X ∈ ready (K:=K) V c d := by
  let M:= ready (K:=K) V c d
  suffices E: M ≤ comap (DD Ω.val P_f k) M by exact E v
  apply span_le.mpr; rintro _ ⟨x,y,u,v,rfl⟩
  change DD Ω.val P_f k (tm x y)∈ M
  have H : DD Ω.val P_f k (tm x y)=tm (boost Ω.val false k x) y+tm x (boost Ω.val true k y) := by
    unfold tm; rw [costD]; apply Prod.ext
    · exact split_legs ..
    dsimp only [Prod.snd_add,boost]; rw [map_add]; simp_rw [P_f,split_legs,map_add,map_sum,map_smul]; simp only [LinearMap.add_apply,LinearMap.sum_apply,LinearMap.smul_apply,smul_add, Finset.sum_add_distrib]; abel
  rw [H]; exact M.add_mem (subset_span ⟨_,_,bu_ext V p g c false k u,v,rfl⟩) (subset_span ⟨_,_,u,bu_ext V p g d true k v,rfl⟩)
lemma Lsmart {Ω:Ortho.Skew} (g:Toll K Ω.val) (k : Axis) (X) (v : X∈ready (K:=K) V c d) : DD Ω.val Row.L k X∈ready (K:=K) V c d := by
  let M:= ready (K:=K) V c d
  suffices E:M ≤ comap (DD Ω.val Row.L k) M by exact E v
  apply span_le.mpr; rintro _ ⟨x,y,u,v,rfl⟩
  change DD Ω.val Row.L k (tm x y)∈M
  have h : DD Ω.val Row.L k (tm x y)= -tm (boost Ω.val false k x) y+tm x (boost Ω.val true k y):=by
    unfold tm; rw [costD]; apply Prod.ext
    · simp only [Row.L,split_legs, Prod.fst_add, Prod.fst_neg,LinearMap.neg_apply,map_neg]; rfl
    dsimp only [Prod.snd_add,Prod.snd_neg,boost]; rw [map_add]; simp_rw [Row.L,split_legs,map_add,map_sum,map_smul]; simp only [LinearMap.add_apply,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.neg_apply,map_neg,smul_add,smul_neg,Finset.sum_add_distrib,Finset.sum_neg_distrib,← neg_add]; abel
  rw [h]; exact M.add_mem (M.neg_mem (subset_span ⟨_,_,bu_ext V p g c false k u,v,rfl⟩)) (subset_span ⟨_,_,u,bu_ext V p g d true k v,rfl⟩)

end YM.GaugeFieldConstruction.Flux.One
