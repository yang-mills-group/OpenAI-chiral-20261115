import YM.SU5.Reconstruction.Chambers.Schedule
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Convex.Basic
/-!
# At any physical gap, even with compact spacetime test footprints
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Chambers.Schedule
open Function Filter Set Metric
open scoped Topology NNReal ENNReal Classical
open Fixture Compose
variable {Γ : AddSubgroup ℝ} (d : Dense (Γ:Set ℝ))
variable {V W : Set (Axis→ℝ)} {j : Axis}
section budget
include d
lemma walls {a b : ℝ} (h : a<b) : ∃ x : Γ, a<(x:ℝ)∧ (x:ℝ)<b := by
  obtain ⟨x,h,k⟩:= dense_iff_inter_open.mp d (Set.Ioo a b) isOpen_Ioo (Set.nonempty_Ioo.mpr h)
  exact ⟨⟨x,k⟩,h⟩
lemma very_early {a : ℝ} : ∃ x : Γ,(x:ℝ)<a:= by obtain ⟨x,_,h⟩:= walls d (by linarith : a-1<a); exact ⟨x,h⟩
lemma very_late {a : ℝ} : ∃ x : Γ,(x:ℝ)>a:= by obtain ⟨x,h,_⟩:= walls d (by linarith : a<a+1); exact ⟨x,h⟩

-- finance even if footprint empty (constant probe). supplies split threshold in actual units.
omit d in
lemma surrounding {V : Set (Axis→ℝ)} (v : IsCompact V) (j : Axis) : ∃ a b : ℝ, ∀ x∈V,a< x j ∧ x j<b := by
  by_cases p:V.Nonempty
  · obtain ⟨x,hx,a⟩:= v.exists_isMaxOn p (continuous_apply j).continuousOn
    obtain ⟨y,hy,b⟩:= v.exists_isMinOn p (continuous_apply j).continuousOn
    exact ⟨y j-1,x j+1,fun x t=>⟨lt_of_lt_of_le (by linarith) (b t),lt_of_le_of_lt (a t) (by linarith)⟩⟩
  exact ⟨0,0,fun x t=>False.elim (p ⟨x,t⟩)⟩

lemma shutters (j:Axis)(p : IsCompact V) : ∃ a b : Γ,(a:ℝ)<(b:ℝ) ∧ ∀ x∈V, a < x j ∧ x j < b := by -- coe inference
  obtain ⟨a,b,k⟩:= surrounding p j; obtain ⟨t,v⟩:= very_early (a:=min a b) d; obtain ⟨w,h⟩:= very_late (a:=b) d;
  exact ⟨t,w,lt_trans (lt_of_lt_of_le v (min_le_right ..)) h, fun x v'=>⟨lt_trans (lt_of_lt_of_le v (min_le_left ..)) (k x v').1, lt_trans (k x v').2 h⟩⟩

lemma choose_grip (j:Axis) (p:IsCompact V)(q:IsCompact W)
    (h : ∀ x∈V,∀ y∈W,x j< y j) :
    ∃ a b c z:Γ, (a:ℝ)<(b:ℝ) ∧ (b:ℝ)<(c:ℝ) ∧ (c:ℝ)<(z:ℝ) ∧
      (∀ i∈ V, i j∈ Set.Ioo (a:ℝ) (b:ℝ)) ∧ ∀ i∈ W, i j ∈ Set.Ioo (c:ℝ) (z:ℝ) := by
  rcases V.eq_empty_or_nonempty with t|t
  · obtain ⟨w,z,r,v⟩:= shutters d j q; obtain ⟨x,b⟩:= very_early (a:=(w:ℝ)) d; obtain ⟨y,a⟩:= very_early (a:=(x:ℝ)) d; exact ⟨y,x,w,z,a,b,r,by simp [t],v⟩
  obtain ⟨w,z,r,v⟩:= shutters d j p
  rcases W.eq_empty_or_nonempty with a|a
  · obtain ⟨a',t'⟩:= very_late (a:=(z:ℝ)) d; obtain ⟨b,b'⟩:=very_late (a:=(a':ℝ)) d; exact ⟨w,z,a',b,r,t',b',v,by simp [a]⟩
  obtain ⟨w',z',r',v'⟩:= shutters d j q
  obtain ⟨x,hx,A⟩ := p.exists_isMaxOn t (continuous_apply j).continuousOn
  obtain ⟨y,hy,B⟩:= q.exists_isMinOn a (continuous_apply j).continuousOn
  obtain ⟨e,X,Y⟩:= walls d (h x hx y hy); obtain ⟨k,T,U⟩ := walls d Y
  exact ⟨w,e,k,z', (v x hx).1.trans X,T, U.trans (v' y hy).2,
    fun i t=>⟨(v i t).1,lt_of_le_of_lt (A t) X⟩,fun i t=>⟨lt_of_lt_of_le U (B t),(v' i t).2⟩⟩
end budget

namespace Fixture
variable {α : Type*} (B : Fixture Γ α)
lemma convex_permission {p v:α→Axis→ℝ} {a b:ℝ} {u w:Axis→ℝ}(ha:0≤a)(hb:0≤b)(he:a+b=1)(j:Axis)(l:List α)
    (p0:B.permission j true p u l) (p1:B.permission j true v w l) : B.permission j true (a•p+b•v) (a•u+b•w) l := by
  induction l generalizing u w with
  | nil=> trivial
  | cons i l ih=>
     let f:= a•p+b•v; have hc : B.start j f i=a• B.start j p i+b•B.start j v i := by
       funext j'; simp only [start, f, Pi.add_apply,Pi.smul_apply,smul_eq_mul]; set c:ℝ:=(Pi.single j ((B.low i j):ℝ):Axis→ℝ) j'; linear_combination - c * he
     have hp : B.stop j f i=a•B.stop j p i+b•B.stop j v i := by
       unfold stop; rw [hc]; funext j'; simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]; set c:ℝ:=(Pi.single j ((B.width i j):ℝ):Axis→ℝ) j'; linear_combination - c * he
     obtain ⟨s,t⟩:=p0; obtain ⟨u,t'⟩:=p1
     constructor
     · rw [if_pos rfl] at s u ⊢
       rw [hc]; simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.sub_apply] at s u ⊢; rcases lt_or_eq_of_le ha with h|h
       · nlinarith only [h,s,u,he,hb]
       subst a; rw [zero_add] at he; rw [he]; simpa using u -- goal uses junk
     rw [hp]; exact ih t t'

lemma convex_ready (q o) : Convex ℝ (B.ready q o) := fun _ a _ b _ _ u v h i=>
 (show _ from by have r:= B.convex_permission u v h i (o i) (a i) (b i); rw [← add_smul,h,one_smul] at r; exact r)
end Fixture
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Chambers.Schedule
