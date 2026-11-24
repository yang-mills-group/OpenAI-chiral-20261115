import GaugeFieldConstruction.PhysicalBook

/-!
# The gap derivatives on physical Book
-/
set_option autoImplicit false
set_option synthInstance.maxSize 5000
noncomputable section
namespace YM.GaugeFieldConstruction.Phys
open Cauchy Row Calibration Finset Function Matter -- ambiguous
open scoped BigOperators

/-- legs. -/
def stride (b : Bool) (i : Axis) : Module.End ℂ (J Mode) := onFirst (Cder b i)
def lace (i : Axis) : Module.End ℂ (J Pen) := onFirst (Gder i)

def bones (i : Axis) := splitD (stride false i) (stride true i)
def eyes (i : Axis) := splitD (lace i) (lace i)
def back (i : Axis) := splitD (bones i) (lace i)
def press (i : Axis) : Module.End ℂ Book := LinearMap.prodMap 0 (LinearMap.prodMap (eyes i) (LinearMap.prodMap (bones i) (back i)))

variable {α β γ η φ : Type*}
lemma here (V : J α→ₗ[ℂ] J β) (a : η) (i : J α) : atop a (V i)= onFirst V (atop a i) := (Cauchy.first V i (ket a)).symm
lemma both (X : J α →ₗ[ℂ] J β) (Y : J γ →ₗ[ℂ] J η)
    (u : Module.End ℂ (J α)) (v : Module.End ℂ (J β)) (s : Module.End ℂ (J γ)) (p : Module.End ℂ (J η))
    (hu : ∀ i,X (u i)=v (X i)) (hv : ∀ i,Y (s i)=p (Y i)) (w : J (α×γ)) :
    strap X Y (splitD u s w)=splitD v p (strap X Y w) := by
  have h : strap X Y ∘ₗ splitD u s= splitD v p ∘ₗ strap X Y := crossing (fun i j=> by
    simp only [LinearMap.comp_apply,split_legs,map_add,straps]; rw [hu,hv])
  exact LinearMap.congr_fun h w
lemma weave (i : Axis) (x y p) : sD x y (P_f i p)=bones i (sD x y p) := both _ _ _ _ _ _
  (fun v=> here (Cder false i) x v) (fun v=>here (Cder true i) y v) p
lemma velvet (i : Axis) (x y z p) : fD x y z (P_x i p)=back i (fD x y z p) := both _ _ _ _ _ _ (weave i x y) (here (Gder i) z) p -- implicit args?
lemma cloth (i : Axis) (x y p) : yD x y (P_g i p)=eyes i (yD x y p) := both _ _ _ _ _ _ (here (Gder i) x) (here (Gder i) y) p

lemma line_g (i p) : graph_g (P_g i p)=eyes i (graph_g p) := by simp_rw [graph_g,LinearMap.smul_apply,LinearMap.sum_apply,map_smul,map_sum,cloth]
lemma line_f (i p) : graph_f (mv (P_f i) p)=bones i (graph_f p) := by
  unfold graph_f; rw [LinearMap.sum_apply,LinearMap.sum_apply,map_sum]
  apply Finset.sum_congr rfl; intro x _; rw [LinearMap.comp_apply,LinearMap.comp_apply]; simp only [LinearMap.proj_apply,mv_at]; unfold tiap
  simp_rw [LinearMap.sum_apply, map_sum, LinearMap.smul_apply,map_smul,weave]
lemma line_x (i) (p : Fragment (J Row.x)) : graph_x (mv (A:=J Row.x) (B:=J Row.x) (P_x i) p)=back i (graph_x p) := by
  unfold graph_x; rw [LinearMap.sum_apply,LinearMap.sum_apply,map_sum]
  apply Finset.sum_congr rfl; intro x _; rw [LinearMap.comp_apply,LinearMap.comp_apply]; simp only [LinearMap.proj_apply,mv_at]; unfold tuap
  simp_rw [LinearMap.sum_apply, map_sum, LinearMap.smul_apply,map_smul,velvet]

lemma likes (i) (p) : dress (P i p)=press i (dress p) := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · simp only [dressG,P,press,LinearMap.prodMap_apply,line_g]
  apply Prod.ext
  · simp only [dressF,P,press,LinearMap.prodMap_apply,line_f]
  simp only [dressX,P,press,LinearMap.prodMap_apply,line_x]

def swap (α : Type*) : Module.End ℂ (J (α×α)) := jet fun ⟨i,j⟩=> ket (j,i)
def bosi : Submodule ℂ (J (α×α)) := LinearMap.ker (swap α - LinearMap.id)
lemma trace {w : J (α×α)} : w∈bosi ↔ swap α w=w := by simp [bosi,sub_eq_zero]
lemma swap_apply (x y : J α) : swap α (times' x y)=times' y x := by
  have H : (times' (α:=α) (β:=α)).compr₂ (swap α) = times'.flip := equalsB (fun a b=>by
    change swap α (times' (ket a) (ket b)) = times' (ket b) (ket a) ; rw [takes,takes,swap,on_ket])
  exact LinearMap.congr_fun (LinearMap.congr_fun H x) y
lemma comot (V : J α→ₗ[ℂ] J β) (X : J (α×α)) : swap _ (strap V V X)=strap V V (swap _ X) :=
  LinearMap.congr_fun (show swap β ∘ₗ strap V V= strap V V ∘ₗ swap α from crossing fun i j=> by simp only [LinearMap.comp_apply,straps,swap_apply]) _
lemma also (k : Axis) (X) : swap _ (eyes k X)=eyes k (swap _ X) := by
  have H : swap Pen ∘ₗ eyes k=eyes k ∘ₗ swap _ := crossing fun i j=>by simp only [LinearMap.comp_apply,eyes,split_legs,map_add,swap_apply]; rw [add_comm]
  exact LinearMap.congr_fun H X
lemma lift_bose (X : J Row.g) (p : X∈ bosi) : graph_g X∈ bosi := trace.mpr (by
  have he (p : Pig) : swap Pen (yD p p X) = yD p p (swap GIndex X) := comot (atop p) X
  simp_rw [graph_g, LinearMap.smul_apply,LinearMap.sum_apply,map_smul,map_sum,he,trace.mp p])
lemma bose_free (d : Floor) (p : UV d) : (dress (shells d p)).2.1∈bosi := by
  rw [dressG]; apply lift_bose; change p.2.1.val∈_
  have ht (a b) : Bose a b ∈ bosi:= trace.mpr (by unfold Bose; rw [map_add,swap_apply,swap_apply,add_comm])
  have he : SG Floor.five≤ bosi := by
    change Record.space evalTg ⊔ Record.space evalG≤bosi
    apply sup_le
    · unfold Record.space; rw [Fintype.range_linearCombination]
      apply Submodule.span_le.mpr; rintro _ ⟨x,rfl⟩; exact ht ..
    unfold Record.space; rw [Fintype.range_linearCombination]
    apply Submodule.span_le.mpr; rintro _ ⟨x,rfl⟩; exact ht ..
  exact he (belowg d p.2.1.property)
lemma bose_shift (b : Book) (h : b.2.1∈bosi) (k : Axis) : (press k b).2.1∈ bosi := trace.mpr (by
  change swap Pen (eyes k b.2.1)=eyes k b.2.1; rw [also,trace.mp h])
end YM.GaugeFieldConstruction.Phys
