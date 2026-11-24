import YM.CF.BProof.Rise.Gait
/-! Paths within Guard/Slow by small local support perturbations,T Frame A from marker lease. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Cliff.Economy
open Function Filter Fock NormedSpace Finset Align Wick Spin Hearth
open SU Lat Dial Cube Tulip Hero Dream Lattice Jet Trek
open Skye MeasureTheory

open scoped Topology Matrix MatrixOrder InnerProductSpace Kronecker BigOperators Matrix.Norms.L2Operator Classical ContDiff
attribute [local instance] opCStarAlgebra
local notation "Gp"=> SU.group
variable {s N:Side}(X:Chart SU.group)(U:Bkg (More N))(ξ:ℝ)(hp:∀ i:Angular.Bond (More N), cd Gp (U i) 1≤ξ)
-- Micro price order Guard and Slower
include hp
lemma traveling (W:Walk)(x:Seat N): cd Gp (travel U x W) 1≤ ξ * W.length:=by
 induction W generalizing x with| nil=> simp [travel] | cons d W ih=>
    simp only [travel,List.length_cons,Nat.cast_add_one, mul_add,mul_one]; have hv: cd Gp (d.read U x) 1≤ξ:=by
      rcases d with ⟨i,b|b⟩; exact hp _; exact (by change cd Gp _⁻¹ 1≤_; simpa using ((cd_inv Gp _ _).trans_le (hp ((Step.mk i true).used x))))
    have ht:=cd_perturb Gp (d.read U x) (travel U (x+d.vec) W) 1 1; rw [mul_one] at ht; exact ht.trans ((add_le_add hv (ih _)).trans_eq (add_comm ..))
lemma guardU (δ:ℝ) (h:xm*(ξ*4) ≤δ): Guard U δ:=by
 constructor <;> intro x i j v
 · have hv:= optic₁ (travel U x (square i j)) 1; rw [SU.fund_one] at hv; exact hv.trans ((mul_le_mul_of_nonneg_left (traveling U ξ hp (square i j) x) xm_p.le).trans h)
 have hv:= optic₂ (travel U x (square i j)) 1; rw [map_one] at hv; exact hv.trans ((mul_le_mul_of_nonneg_left (traveling U ξ hp (square i j) x) xm_p.le).trans h)
lemma slowly (F P:Stun N)(k q:ℝ)(u:∀ i,Xd (P i) (F i)≤ xm*ξ)(h:PaceX Set.univ 1 F k)(t:k+3*xm*ξ < q): Slow U (hook P) q:=by
 apply pace_slow _ t; intro x i a b; let y:=x+step i; let V:=U (x,i); change Xd (scaledV V (P y)) (P x) ≤_
 have hv: Xd (scaledV V (P y)) (scaledV 1 (F y))≤ xm*ξ+xm*ξ:= (Xd_bits V 1 (P y) (F y)).trans (add_le_add (u y) (mul_le_mul_of_nonneg_left (hp (x,i)) xm_p.le)); apply le_trans ((Xd_triangle _ _ (P x)).trans (add_le_add hv ((Xd_triangle _ (F x) (P x)).trans (add_le_add (h x i trivial trivial) (Eq.trans_le (norm_sub_rev ..) (u x)))))); apply le_of_eq; ring -- Arg order
omit hp
variable (P:Stun N)(A: Seat N→ SU.E)
def paths(v:ℝ): Pane N:= fun i=> gait (U i) ξ v
def fillX(v:ℝ) : Stun N:=fun i=> scaledV (gait (A i) ξ v) (P i)
lemma path_zero : paths U ξ 0=1:= by funext; exact gait_zero ..
lemma fill_zero : fillX ξ P A 0=P:=by funext i; unfold fillX; rw [gait_zero,scaled_one,id_eq]
structure Pressure(X:Chart SU.group)(ξ K:ℝ):Prop where
 safe: 0<ξ
 hf:ξ≤X.radius
 cap:X.C*ξ ≤ X.size
 pay:lipBill X.C≤ K
variable {K:ℝ}(p:Pressure X ξ K)(Hv:∀ i, cd Gp (A i) 1≤ξ)
include p hp
lemma path_end : paths U ξ ξ=U:=funext fun i=> gait_self X (U i) ξ p.safe p.hf (hp i)
lemma path_pay(t:ℝ): TransK 1 (paths U ξ) t K:=fun i=> Allows.mono (Economy.plot X _ ξ p.safe p.hf (hp i) p.cap t) p.pay
abbrev Κξ (Z:ℝ):=Z*(Z*ξ)
lemma path_close(t:ℝ)(i:Angular.Bond (More N)): cd Gp (paths U ξ t i) 1 ≤ Κξ ξ X.C:= gait_close X _ ξ p.safe p.hf (hp i) p.cap t -- Tune Κξ binder
omit hp
include Hv
lemma fill_end : fillX ξ P A ξ=feast A P:=by funext i; unfold fillX feast; rw [gait_self X (A i) ξ p.safe p.hf (Hv i)]
lemma fill_pay(t:ℝ): Jet.seek (fillX ξ P A) 1 t K:= fun i=> Allows.mono (Economy.plotB X _ ξ p.safe p.hf (Hv i) p.cap t (P i)) p.pay
lemma fill_close(t:ℝ)(i:Seat N) : Xd (fillX ξ P A t i) (P i)≤ xm*(Κξ ξ X.C):=by have hv:= Xd_rate (gait (A i) ξ t) 1 (P i); rw [scaled_one,id_eq] at hv; exact le_trans hv (mul_le_mul_of_nonneg_left (gait_close X _ ξ p.safe p.hf (Hv i) p.cap t) xm_p.le)
include hp
lemma guarding(δ:ℝ)(h:xm*(Κξ ξ X.C *4)≤δ)(s q:ℝ)(u:PaceX Set.univ 1 P s)(k:s+3*xm*(Κξ ξ X.C) < q)(t:ℝ): Guard (paths U ξ t) δ ∧ Slow (paths U ξ t) (hook (fillX ξ P A t)) q:=⟨ Economy.guardU _ _ (path_close X U ξ hp p t) δ h, Economy.slowly _ _ (path_close X U ξ hp p t) P _ s q (fill_close X ξ P A p Hv t) u k⟩
end YM.CF.BProof.Cliff.Economy
