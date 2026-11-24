import GaugeFieldConstruction.Dickens3
import GaugeFieldConstruction.Toddy
import GaugeFieldConstruction.Tiaras
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 60000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry Grotto
namespace Ivey
open Sault Leaf Sour
open Ladder3 Drapes Tenant Palot Rue Iona
attribute [local instance] loreM loreN
variable {n: Side}{I α β γ G:Type}[LinearOrder I][Fintype I][Fintype α][Fintype β][Fintype γ]
-- old bank
namespace ShoreQ
open Tuner Ladder3 Branch Tenant XGarden XGarden.MastTin
open Hest Broc Jet Levier Urn Palot Rill Salt -- tune
open Sour.SliceRoof Lattice.Corona
variable (R:Loom n)(P:BudgetPoint) (K:ℕ)(t d a c:ℝ)
local notation "S0"=> Support (More n)
local notation "J"=> Single n
def Tyrant(k:ℕ)(b:ℕ)(δ a:ℝ):Prop:= δ > 0 ∧ δ*((k+22)+(k+22)+1:ℕ)^4 ≤ a/2 ∧ (a/2)*(4*(yard_M b:ℝ)+2) ≥1 -- cast ambiguous nat vs real
lemma tire_s(k:ℕ){a:ℝ}(p:0<a):∃ b δ,Tyrant k b δ a:=by
 obtain ⟨b,g⟩:= exists_nat_gt (1/(a/2)); let δ:= (a/2)/(((k+22)+(k+22)+1:ℕ)^ (4:ℕ) :ℝ)
 have q:1<(b:ℝ)*(a/2):=lt_of_lt_of_le ((div_lt_iff₀ (by linarith :0<a/2)).1 g) le_rfl
 refine ⟨b,δ,by positivity,le_of_eq (by unfold δ; push_cast; field_simp),?_⟩; unfold yard_M; push_cast; nlinarith only[p,q]
lemma τ_Hope(k b:ℕ){δ a:ℝ}(h:Tyrant k b δ a)(X:Support n): Branch.rent δ (Lattice.halo (k+22) X)≤ Branch.rent (a/2) X:=by
 refine Real.exp_monotone ?_; refine le_trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (halo_size X (k+22))) h.1.le) ?_ -- cast conversion
 have hg:=mul_le_mul_of_nonneg_left h.2.1 (Nat.cast_nonneg (α:=ℝ) X.card); norm_cast at *; push_cast at *; nlinarith only [hg] -- ring w
-- support term Plan on S.sum in group Kernel.H.T cost.
section
variable (F: Sour.Elm n Unit d a c)
abbrev ζΧ(V:Support (More n)):ℝ:=∑ i:Single n,∑ j:Single n,Wloop F V i j
lemma Hook_p (V:Support (More n)):0≤ ζΧ d a c F V:=sum_nonneg fun _ _=>sum_nonneg fun _ _=>loop_p .. -- F implicit pass?
lemma loop_gain (V:Support (More n))(i j:Single n)(h:Wloop F V i j≠0): Grove (terr _) V ∧ aptK i ∈ V ∧ aptK j∈ V:=by
 suffices hp:∃ x y:SU.Slot,F.W V (i.1,x) (j.1,y)≠0 by
    obtain ⟨x,y,t⟩:=hp; exact ((F.coat V).1 ()|>.expo (i.1,x) (j.1,y)).triggered t
 by_contra g; apply h; unfold Wloop; refine sum_eq_zero fun x _=>?_ ; apply sum_eq_zero; exact fun y _=>Classical.byContradiction (fun t=>g ⟨x,y,t⟩)
lemma growΧ (V:Support (More n))(h:ζΧ d a c F V≠0): Grove (terr _) V:=by
 by_contra w; apply h; unfold ζΧ; refine sum_eq_zero fun i _=>sum_eq_zero fun j _=>Classical.byContradiction (fun t=>w (loop_gain d a c F V i j t).1)
abbrev CrownBill (c:ℝ) (j:ℕ):= (Fintype.card SU.Slot :ℝ)*Fintype.card SU.Slot * c *(quotaL * yardZ j)
lemma LegendT {δ:ℝ}{j:ℕ}(p0:0 < a)(h:Tyrant K j δ a)(o: Seat n): (∑ V:Support (More n) with o∈V, ζΧ d a c F V * rent δ (Lattice.halo (K+22) V))≤ CrownBill c j:=by
 let A':=(Fintype.card SU.Slot:ℝ); let C₀:= (A'*(A'*c)); let X':=(univ:Finset (Support (More n))).filter (fun i=>o∈i); let v(x:S0)(i j:J):= Wloop F x i j * rent δ (Lattice.halo (K+22) x)
 have he(i:J): (∑ x∈X',∑ j:J,v x i j) ≤ windPulse j (aptK i) o * C₀:=by
    let y:=aptK i; let W':= windPulse j y o; have ht: ∀ x ∈ X',∀ k:J,v x i k ≤ W'*(Branch.rent a x* Wloop F x i k):=by
       intro x q k
       by_cases p: Wloop F x i k=0; · unfold v; rw [p,mul_zero,mul_zero,zero_mul]
       obtain ⟨hx,vK,g⟩:= loop_gain d a c F x i k p
       apply le_trans (mul_le_mul_of_nonneg_left (τ_Hope K j h x) (show 0≤ Wloop F x i k from loop_p (F:=F) _ _))
       rw [←mul_assoc W',mul_comm]; apply mul_le_mul_of_nonneg_right _ (loop_p (F:=F) ..)
       unfold W' windPulse Branch.rent; rw [←Real.exp_add]; apply Real.exp_monotone
       have hk : separation y o < x.card:= hx.lim y vK o (mem_filter.mp q).2
       have h' : (separation y o:ℝ)/(4*(yard_M j:ℝ)+2) ≤ (a/2)*x.card:=by
          rw [div_le_iff₀ (by positivity)]
          apply (Nat.cast_le.mpr hk.le).trans; nlinarith only [mul_le_mul_of_nonneg_right h.2.2 (show 0≤ (x.card:ℝ) from by positivity)]
       rw [neg_div]; linarith only [h']
    have hh:∑ k:J,saleM a (Wloop F) i k≤ C₀ := (hefty F).rows i
    apply le_trans ?_ (mul_le_mul_of_nonneg_left hh (Real.exp_pos _|>.le)); rw [Finset.mul_sum,sum_comm]; apply sum_le_sum; intro k _; unfold saleM; rw [mul_sum]; refine (sum_le_sum (fun i v=>ht i v k)).trans ?_; exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun x _ _=>mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le (loop_p ..))
 unfold ζΧ; simp_rw [sum_mul]; rw[sum_comm (f:=fun x i=> ∑ j:J,v x i j)]; -- tune rewriting.
 refine (sum_le_sum (fun i _=>he i)).trans ?_; have hC:=F.bank.posP
 rw [←sum_mul]; have ht: (∑ i:J,windPulse j (aptK i) o)≤quotaL*yardZ j:=by
    have h':(∑ i:J,windPulse j (aptK i) o) =∑ p:Seat n,∑ i:J with aptK i=p, windPulse j p o:=by
       simp_rw [sum_filter]; rw [sum_comm]; apply sum_congr rfl; intro i _; symm; rw [sum_eq_single (aptK i)]; simp; intro j _ h; rw [if_neg h.symm]; simp
    rw [h']; apply le_trans ?_ (mul_le_mul_of_nonneg_left (pulse_world j o) (show 0 ≤ (quotaL:ℝ) from by positivity)); rw [Finset.mul_sum]; refine sum_le_sum (fun i _=> ?_); rw[sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (quota_Θ _)) (pulse_pos ..|>.le)
 refine (mul_le_mul_of_nonneg_right ht (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hC))).trans_eq ?_; unfold CrownBill; ring
end
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end
