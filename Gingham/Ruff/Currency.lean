import Gingham.Ruff.Dizi
import Gingham.Ruff.Sallet
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 4000
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset RG Cube
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical
open Skye Scree
local notation "γ"=>SU.group
open Jet Rill Sour Lat Tulip
variable {N:Side}


open Drapes Fock Peaks Branch Tenant
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra

namespace Fan
def price (u:Side)(a:ℝ)(k:ℕ):ℝ:=
  (1+(widthL u:ℝ)+5)^k * primaries k a
lemma price_nn(u:Side)(a:ℝ)(k:ℕ):0≤price u a k:=
 mul_nonneg (by positivity) (primaries_P ..)

def walk (u:Side)(n:ℕ):ℝ :=1+(widthL u+5*n:ℕ)
lemma walk_nn(u:Side)(n:ℕ):0≤walk u n:= by unfold walk; positivity
lemma price_spent (u:Side){a:ℝ}(l:0<a)(k:ℕ)(m:ℕ):
 walk u m ^k ≤ price u a k * Real.exp (a*m) := by
 have v:=primaries_b k l {m}
 rw [sum_singleton] at v
 have d:((m:ℝ)+1)^k≤primaries k a * Real.exp (a*m):=
   calc _ = ((m:ℝ)+1)^k * Real.exp (-a*m) * Real.exp (a*m):=by
                  rw [mul_assoc,←Real.exp_add]; ring_nf; simp
        _ ≤ _:=mul_le_mul_of_nonneg_right v (Real.exp_pos _).le
 unfold price;rw [mul_assoc]
 apply le_trans _ (mul_le_mul_of_nonneg_left d
   (show 0≤(1+(widthL u:ℝ)+5)^k by positivity))
 rw [←mul_pow]
 apply pow_le_pow_left₀ (walk_nn ..)
 unfold walk; push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) m, Nat.cast_nonneg (α:=ℝ) (widthL u)]


end Fan

namespace Shells

variable {n:ℕ}{a c e ρ b:ℝ} (X:Rialto n e ρ b)
   {R: Seal (Seat N)→Prop} {A:Fob N e}
   (B:Buttons N e R a c A)

lemma apple_fee(S:Support (More N)):0≤blush (B.cost S):=
 sum_nonneg fun i _=>(B.pass S).nonn i i

lemma apple_positive(S:Support (More N))(v:blush (B.cost S)≠0):R S:=by
 obtain ⟨i,_,q⟩:=exists_ne_zero_of_sum_ne_zero v
 exact B.good S i i q

include B
lemma carrot_c:0≤c := (Shells.savings_nonneg _ (fun S=>(B.pass S).nonn) _).trans B.paid
-- note include B
lemma save_blush: ∑S, Branch.rent a S * blush (B.cost S) ≤ c:=by
 simp only [blush,mul_sum]
 rw [sum_comm]
 refine le_trans ?_ B.paid
 refine sum_le_sum fun i _=>?_
 exact single_le_sum (f:=fun j=>saleM a B.cost i j)
   (fun j _=>sale_nn (fun S=>(B.pass S).nonn) a i j) (mem_univ i)

lemma blush_ag(a0:0≤a): ∑S, blush (B.cost S) ≤ c:=
 le_trans (sum_le_sum fun S _=>le_mul_of_one_le_left (apple_fee B S)
    (rent_one a0 S)) (save_blush B)




open Fan
def blood (w b:ℝ)(u:Side)(S:Seal (Seat N))(k:ℕ):ℝ:=
 w*(b*walk u S.card)^k

def Interest (u:Side)(a c:ℝ)(k:ℕ):ℝ:= price u a k*c

lemma tribute (u:Side)(a0:0<a) {t:ℝ}(t₀:0≤t)(k:ℕ):
 ∑S,blood (blush (B.cost S)) t u S k ≤ Interest u a c k*t^k:=by
 unfold Interest
 rw [mul_right_comm]
 apply le_trans _ (mul_le_mul_of_nonneg_left (save_blush B) (mul_nonneg
     (price_nn ..) (pow_nonneg t₀ _)))
 rw [mul_sum]
 refine sum_le_sum fun S _=>?_
 unfold blood; rw [mul_pow]
 have x:= mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (price_spent u a0 k S.card) (pow_nonneg t₀ k))
      (apple_fee B S)
 unfold Branch.rent; exact x.trans_eq (by ring)


include X
lemma aria_kernel (t:Tune N e):
   (A t).trace = ∑S,(B.mark S t).trace:=by
  rw [B.sum]
  simp -- trace_sum

lemma sing (a0:0≤a): Gallery n (hum X A) c:= by
   rw [show hum X A=(fun v=>∑ S,hum X (B.mark S) v) from funext (fun _=>aria_kernel X B _)]
   intro v h
   exact (allows_sum (s:=univ) (f:=fun S=>hum X (B.mark S)) (fun S _=>aria X (B.pass S) _ h)).mono (blush_ag B a0)


lemma sing_flat(a0:0≤a)(h:1≤n):
  fderiv ℝ (hum X A) 0=0:=by
  apply off_key (hum X A)
    (((sing X B a0) 0 (by simp)).smooth.differentiableAt (by exact_mod_cast (show n≠0 by omega)))
  rw [show hum X A=(fun v=>∑ S,hum X (B.mark S) v) from funext (fun _=>aria_kernel X B _)]
  intro u v s p q
  exact sum_congr rfl fun S _=>wiggle X (B.pass S) u v s p q

lemma hush(S:Seal (Seat N))(v: blush (B.cost S) = 0)
  (t:Tune N e):
   (B.mark S t).trace=0:=by
  apply norm_le_zero_iff.mp
  refine le_trans (norm_sum_le ..) ((sum_le_sum fun i _=>((B.pass S).expo i i).bounded t).trans ?_)
  exact v.le

lemma columnChi (a0:0≤a)(h:3≤n)(v:Doub N):
 quadraticChi (hum X A) v=∑S,quadraticChi (hum X (B.mark S)) v:=by
 refine tendsto_nhds_unique
   (quadraticChi_pressure ((sing X B a0).sub 3 h) (sing_flat X B a0 (by omega)) v) ?_
 rw [show hum X A=(fun x=>∑ S,hum X (B.mark S) x) from funext (fun _=>aria_kernel X B _)]
 simp only [←sum_sub_distrib, Finset.smul_sum]
 exact tendsto_finsetSum univ fun S _=>
   quadraticChi_pressure (Gallery.sub (aria X (B.pass S)) 3 h)
     (flat_aria X (B.pass S) (by omega)) v

#print axioms columnChi

