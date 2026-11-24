import Organdy.Avenue
import Organdy.Zone
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Lattice Fock Sour Pastry Scree Skye Cadre Vow Palot Rue Sault Stax Rush Scroll Finset RG
open Cube Rill Mew Ione Bake Rive Vow.TreasuryFog Metric
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator Mew
attribute [local instance] opCStarAlgebra
variable {n:Side} {p:BudgetPoint} {h a b c d:ℝ}{q:ℕ} {I : Type} [LinearOrder I] [Fintype I]

open SectorNext.Remainder Py Py.Rate.BScale Pressure Lor
open Nor

variable {M:ℕ}{γ:ℝ}

def plenish (M:ℕ) :=1+2*(M:ℝ) + Real.exp (2*M)
def gather (M:ℕ)(o b γ:ℝ):= plenish M* (o*(b+200*γ))

private lemma narrowEyes {x:ℝ}(d:0≤x)(b:ℕ):TreasuryFog.sigma x b≤1:=by
 apply Real.exp_le_one_iff.mpr
 rw [neg_mul,neg_div]
 exact neg_nonpos.mpr (by positivity)

variable {X W:ℝ}
lemma imprest (s:Stalls p M a b γ)
 (b0:0≤b)(u:1≤ W)(i:2*W≤Real.exp (tailWidth p.B M))
 (e:18*M ≤ p.B)
 (z: W*gather M (hoard p) b γ ≤1):
 PortRates s.sleigh M (tailWidth p.B M) W (spending p b)
    (gather M (hoard p) b γ) 1 ∧
 DoubleR p s.sleigh M (spending p b) (gather M (hoard p) b γ):=by
   let A:=p.B; have h:0<(A:ℝ):=by exact_mod_cast p.B_pos
   let x:=tailWidth A M; have t:0≤x:=by unfold x tailWidth;positivity
   have hx:9*x*M ≤ biscuit p / 2 * (A:ℝ)^2:=by
     have hm:(0:ℝ)<18*(M+1):=by positivity

     have g:biscuit p * (A:ℝ)^2=A:=by change (A:ℝ)⁻¹*_= _;field_simp
     rw [div_mul_eq_mul_div,g]
     unfold x tailWidth
     field_simp
     -- goal?
     all_goals nlinarith
   let ρ:=hoard p
   let Z:=ρ*(b+200*γ)
   have hz:=hoard_zero (p:=p); have ht:=s.glow
   have hZ:0≤Z:=mul_nonneg hz (by linarith)
   have hf:0≤ spending p b:=mul_nonneg hz b0
   let Φ:=s.sleigh
   have hY:0≤yσF p Φ:=by
       change 0≤hoard p *((1:ℝ)⁻¹ * (γ*200))
       positivity
   have hb:spending p b ≤Z:=mul_le_mul_of_nonneg_left (by linarith) hz
   have y:yσF p Φ≤Z:=mul_le_mul_of_nonneg_left (by change (1:ℝ)⁻¹* (γ*200)≤_;rw [inv_one];linarith) hz
   have y0:0≤yσE p Φ:= mul_nonneg hz (mul_nonneg s.glow.le
      (inv_nonneg.mpr (sub_nonneg.mpr Φ.degree0.le)))
   have y':TreasuryFog.sigma (Φ.η+Φ.η) p.B*yσE p Φ≤Z:=
      (mul_le_of_le_one_left y0 (narrowEyes (add_nonneg Φ.hη.le Φ.hη.le) p.B)).trans
      (mul_le_mul_of_nonneg_left (s.read.trans (by linarith)) hz)

   let D:=Real.exp (2*M)
   have hD:0≤D:=(Real.exp_pos _).le
   have hq:Z≤plenish M*Z:=le_mul_of_one_le_left hZ
      (by change 1≤_ + D; linarith only [hD,Nat.cast_nonneg (α:=ℝ) M])
   refine ⟨⟨t,u,i,hx,hf,hY,
      (mul_le_mul_of_nonneg_left (hb.trans hq) (zero_le_one.trans u)).trans z,
      (mul_le_mul_of_nonneg_left (y.trans hq) (zero_le_one.trans u)).trans z,
      (mul_le_of_le_one_left hY (narrowEyes Φ.hη.le p.B)).trans (y.trans hq), y'.trans hq⟩,
      hb.trans hq, ?_,?_,?_⟩
   · change _≤(A:ℝ)⁻¹ * (A:ℝ)^2
     rw [sq,←mul_assoc,inv_mul_cancel₀ h.ne', one_mul]; norm_num; exact_mod_cast e
   · nth_rw 1 [mul_right_comm]
     refine (add_le_add (mul_le_mul_of_nonneg_left hb (by positivity:0≤(2:ℝ)*M)) y').trans ?_
     rw [←add_one_mul]
     exact mul_le_mul_of_nonneg_right (by unfold plenish; linarith [Real.exp_pos (2*(M:ℝ))]) hZ
   exact mul_le_mul (by unfold plenish; linarith [Nat.cast_nonneg (α:=ℝ) M]) y hY (show 0≤plenish M from by unfold plenish; positivity)

variable (R:Patch)(J G:ℝ→ℝ)(j α:ℕ) -- rebinding names? Lean variable forbids
local notation "w"=> prismPan R α
def bankFee (J G:ℝ→ℝ)(j:ℕ)(x:ℝ):=
   gather j (reserveT 2 6 (radiusB x) (runway x)) (J x) (G x)
lemma chills (p:Quench R J)(e:Quench R G):
 Quench R (bankFee J G j):=
   ((p.addL (e.manyF _)).bondF (reserve_bond 2 6)).manyF _

lemma bound_w (v:ℝ→ℝ) (r:Quench R v):
    ∀ᶠ x in atTop,w x*v x ≤1:= by
    have u:Chill_v (fun x=>w x*v x):=by
       unfold prismPan
       simp_rw [mul_assoc,inv_mul_eq_div]
       exact Chill_v.leanB r (beryl _)
    exact u.spine_a.eventually (ge_mem_nhds zero_lt_one)
end YM.CF.Organdy
