import Zephyr.Chern.Rad
import Zephyr.Chern.Moments
import Zephyr.Chern.Decay
import YM.CF.Onyx.Gold
set_option autoImplicit false
noncomputable section
namespace Zephyr.Chern

open YM YM.Lattice Filter Silk YM.CF YM.CF.Fir YM.Next.Free YM.Laurent YM.CF.Jill


private theorem dresses {α : Type} {f : α → Bloch.Momentum → ℂ}
    (h : Moderate (fun _ => 1) f) (ov : ∀ i,Overlaps zone (f i)) :
    ∃ r : α → Silk, Moves ⊤ r ∧
      ∀ i (p : Bin), Bound Real.pi p → E (radians p) (r i) = f i (tmap p) := by
  obtain ⟨θ,C,ht,hC,h⟩ := h
  let s := min θ zone
  have hs : 0 < s := lt_min ht zone_pos
  let b := s/3
  have hb : 0 < b := by unfold b; linarith
  let B := (2*((1+b)/b))^(Fintype.card Axis)
  have ht i:= hol_on_thickening hs ((h i).mono (min_le_left ..) (by rw [mul_one]))
      ((ov i).mono (min_le_right ..))
  have hw i:= (ht i).1.issues (ht i).2.1 b b hb.le hb (by unfold b; linarith)
  let r i : Silk:= ⟨market (placed (f i)) 0, fun k=> (fast_kernel (C*B) hb k).of_nonneg_of_le
    (fun _=> mul_nonneg (penPos ..).le (norm_nonneg _))
    (fun _=> mul_le_mul_of_nonneg_left ((of_width (hw i) _).trans (by rw [Complex.norm_real,Real.norm_eq_abs]; exact le_abs_self _))
      (penPos ..).le)⟩

  refine ⟨r, swift_exp hb (C*B) (Eventually.of_forall fun i=> of_width (hw i)), fun i p hp => ?_⟩
  rw [E_read]
  have pc:=mem_cube_real (base_subset_realCube hs (b_base hp)) hs
  exact ((ht i).1.paints (ht i).2.1 _ pc.1).trans ((ht i).2.2 _ pc)

open scoped Real

def signal (j:ℕ) (M:Male) (p:Bloch.Momentum) : Five → ℂ :=
  Fin.cases (1-2*shell j M.val p) (fun a => 2*skin j M.val p a)

/-- Simultaneous Laurent lifts of the five scalar streams of the flat spin
projection, across the odd-depth parameter. -/
structure Looming (j:ℕ) (r : Male → Streams) : Prop where
  moves (k) : Moves ⊤ (fun i => r i k)
  plays (i : Male) (p : Bin) : Bound π p →
    ∀ k, E (radians p) (r i k)=signal j i (tmap p) k

theorem looming {j : ℕ} (hj : 1 ≤ j) : ∃ r,Looming j r := by
  obtain ⟨s,h,e⟩:=dresses (shellPay j hj (fun i:Male=>i.val) (fun i=>i.prop))
    (fun _=>shell_overlap _ _)
  choose t g d using fun a=>dresses (skinPay j hj (fun i:Male=>i.val) (fun i=>i.prop) a)
    (fun _=>skin_overlap _ _ a)

  let cc (z:Silk) : Moves (⊤ : Filter Male) (fun _ => z) := (arrives_const ..).swift
  refine ⟨fun i => Fin.cases (1+ -(2*s i)) (fun a => 2*t a i), fun k => ?_, fun i p hp k => ?_⟩
  · induction k using Fin.cases
    · exact (cc 1).add (((cc 2).mul h).neg)
    · rename_i a; exact (cc 2).mul (g a)
  induction k using Fin.cases
  · change E (radians p) (1+ -(2*s i))= (1-2*shell _ _ _)
    rw [map_add,map_one,map_neg,map_mul,map_ofNat,e _ _ hp,sub_eq_add_neg]
  rename_i a
  change E (radians p) (2*t a i)= (2*skin _ _ _ a)
  rw [map_mul,map_ofNat,d _ _ _ hp]
