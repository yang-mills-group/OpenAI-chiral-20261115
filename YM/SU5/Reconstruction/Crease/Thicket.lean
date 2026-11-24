import YM.SU5.Reconstruction.Crease.Ghost
import YM.SU5.Reconstruction.Anvil.Cubicle
/-! # a screen's occupancies. -/
set_option autoImplicit false
noncomputable section
namespace YM.BridgeClub
open Anvil Set Function Metric OS
open scoped Topology BigOperators Classical
variable (a b:Axis)(pb:a≠b)
-- adapt arbitrary sets for HK receipt
def Tarp (u v:Axis→ℝ) (p:ℝ) : Set Meter := {q| (q a∈ Icc (0:ℝ) p) ∧ ∀ i, i ≠ a→ q i∈ Icc (u i) (u i+v i)}
def Reel (u v:Axis→ℝ) : Set E4 := {x|x a=0 ∧ ∀ i, i ≠ a→ x i∈ Icc (u i) (u i+v i)}
def Clearance (x:E4):Prop := (x a)^2 < ∑ i∈Finset.univ.erase a, (x i)^2
abbrev TicketSeparation (U W:Set E4): Prop:=∀ x∈ U, ∀ y∈W, Clearance a (y-x)
theorem clearPay (u v r d: Axis→ℝ)(p t:E4)(e:∀ i,i≠ a→0≤ v i)(z:∀ i,i≠a→0 ≤ d i) (h: TicketSeparation a ((fun x=> x+p) '' Reel a u v) ((fun x=> x+t) '' Reel a r d)) : DisjointPay a (Finset.univ.erase a) u v r d (eyebrow a t - eyebrow a p) (t a - p a):=by
 refine ⟨⟨fun x s=>e x (Finset.ne_of_mem_erase s), fun x s=> z x (Finset.ne_of_mem_erase s)⟩, fun x y s w=>?_⟩
 let X:= WithLp.toLp 2 x; let Y:=WithLp.toLp 2 y
 specialize h _ ⟨X,⟨s.1,fun i u=> s.2 i (Finset.mem_erase.mpr ⟨u,Finset.mem_univ _⟩)⟩, rfl⟩ _ ⟨Y,⟨w.1,fun i u=> w.2 i (Finset.mem_erase.mpr ⟨u,Finset.mem_univ _⟩)⟩,rfl⟩
 dsimp only [Clearance] at h; rw [show (Y+t-(X+p)) a=t a-p a from ?_] at h
 · rw [rimPay_norm]; exact h.trans_eq (Finset.sum_congr rfl fun i u=> by simp only [PiLp.sub_apply,PiLp.add_apply, Pi.add_apply,Pi.sub_apply,eyebrow,if_neg (Finset.ne_of_mem_erase u)]; change (y i + _- (x i+p i))^2=_; ring)
 simp [show Y a=0 from w.1, show X a=0 from s.1]
def Scope (x:E4):Prop := |x a| < x b
theorem scope_add {u v:E4}(h:Scope a b u)(p:Scope a b v): Scope a b (u+v):=(abs_add_le ..).trans_lt (add_lt_add h p)
def Wedge: Set E4 := {x| Scope a b x}
def Counter: Set E4:= {x| Scope a b (-x)}
theorem turn_fee (x:E4):turn a b x∈ Wedge a b↔ x ∈ Counter a b:=by simp [Wedge, Counter,Scope,turn_at]
theorem turning (x:E4):turn a b x∈ Counter a b↔ x ∈ Wedge a b:= by simp [Wedge,Counter,Scope,turn_at]
include pb in
lemma room_separated : TicketSeparation a (Wedge a b) (Counter a b):=by
 intro x p y q; have e:=scope_add a b p (v:=-y) q
 have hx:Clearance a (x + -y):=by
      unfold Clearance; rw [← sq_abs]; exact (pow_lt_pow_left₀ e (abs_nonneg _) (by decide)).trans_le (Finset.single_le_sum (f:=fun i:Axis=> _) (fun i _=> sq_nonneg ((x+ -y) i)) (a:=b) (s:=Finset.univ.erase a) (by simp [pb.symm])) -- b naming
 unfold Clearance at *; rw [←sub_eq_add_neg] at hx; rw [← neg_sub x y]; simpa only [PiLp.neg_apply,even_two.neg_pow] using hx
end YM.BridgeClub
