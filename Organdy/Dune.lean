import Organdy.Lace
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


open Push.AbsoluteSums.Trees

abbrev biscuit (p:BudgetPoint):ℝ:=(p.B:ℝ)⁻¹
abbrev highPace (p:BudgetPoint):ℝ:=p.supportExponent+7*biscuit p
abbrev straightPace (p:BudgetPoint):ℝ:=p.supportExponent+5*biscuit p
abbrev rider (p:BudgetPoint)(c:ℝ):ℝ:=spanV p.B*(biscuit p)⁻¹*c
local notation "η·" => biscuit p
local notation "l·" => straightPace p

lemma biscuit_pos : 0 < η·:=by unfold biscuit; exact inv_pos.mpr (Nat.cast_pos.mpr p.B_pos)

/-- κ at one; old forces and births pay directly at γ (much smaller
than Q), full only shot cost. -/
structure Stops (p:BudgetPoint)(c e γ:ℝ): Prop where
 can: 0≤c
 glow: 0<γ
 drink: degreePrice p.B (100*γ) (biscuit p)≤1/2
 sip : degreePrice p.B γ (biscuit p)≤1/2
 drop: 2*γ≤1
 stem: spanV p.B * γ ≤ biscuit p
 lake: spanV p.B*c ≤ biscuit p/4
 dew: rider p c ≤ biscuit p/4
 pen: e ≤ biscuit p/4*γ

variable {c e γ:ℝ}
lemma Stops.read (v:Stops p c e γ):
    γ * (1-degreePrice p.B γ (biscuit p))⁻¹≤ 2*γ:=by
  apply le_trans (mul_le_mul_of_nonneg_left _ v.glow.le) (le_of_eq (mul_comm γ _))
  have h:=v.sip
  rw [inv_le_iff_one_le_mul₀ (by linarith:0 < 1-degreePrice p.B γ η·)]
  linarith

def Stops.sleigh (v:Stops p c e γ):Occlus p where
 κ:=1
 w:=biscuit p
 η:=biscuit p
 uΓ:=l·
 γ:=γ
 c:=c
 d:=rider p c
 e:=e
 hγ:=v.glow
 hη:=biscuit_pos
 hw:=by rw [straightPace]; linarith
 degree:=v.drink
 degree0:=v.sip.trans_lt (by norm_num)
 still:=v.read.trans v.drop
 covers:=by
   have he:Real.exp 1 ≤ 3:=by have ht:=Real.exp_one_lt_d9; linarith
   have hx:Real.exp 1*(γ*_) ≤ 3*(2*γ):=mul_le_mul
     he v.read (mul_nonneg v.glow.le (inv_nonneg.mpr (by linarith [v.sip]))) (by norm_num)
   linarith [v.glow]

variable {z g:Aura n→ℝ}
local notation "xQ" => Cadre.fog (loom_v l· η· (widthK n p.B) 0) z γ

lemma fog_light (v:Stops p c e γ)(r:0≤z)(i:Aura n):
    xQ i ≤ z i * tact (l· + η·) p.B i:=by
  unfold Cadre.fog loom_v waveL
  rw [mul_assoc,←Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (r i)
  refine Real.exp_le_exp.mpr ?_
  rw [mul_zero,sub_zero,add_mul]
  have hx:=mul_le_mul_of_nonneg_right v.stem
        (zero_le_one.trans ((vigor n p.B).pos i)) -- parentheses
  have he:=mul_le_mul_of_nonneg_right ((vigor n p.B).rate i) v.glow.le
  linarith only [he,hx]

variable (v:Stops p c e γ)(r:0≤z)
  (t:∀ o:Seat n,tallB z p.B (highPace p) o ≤ c)
include v r t

lemma jar (o:Seat n): nook xQ o ≤ c:=by
  refine le_trans (sum_le_sum fun i _=>le_trans (fog_light v r i)
    (mul_le_mul_of_nonneg_left (tact_para (b:= highPace p) ?_ i) (r _))) (t o)
  unfold highPace straightPace
  linarith [biscuit_pos (p:=p)]

lemma jar_tight (o:Seat n): shelfR xQ o ≤ rider p c:=by
  refine le_trans ?_
    (mul_le_mul_of_nonneg_left (t o)
      (mul_nonneg (show 0 ≤ spanV p.B from Nat.cast_nonneg _) (inv_nonneg.mpr biscuit_pos.le)))
  let T:= highPace p
  change shelfR _ _ ≤ _ * ∑ i∈spark o,z i*tact T p.B i
  rw [mul_sum]; refine sum_le_sum fun i _=>?_
  apply le_trans (mul_le_mul_of_nonneg_right (fog_light v r i) (Nat.cast_nonneg _))
  rw [mul_assoc, mul_comm (tact _ _ i), mul_left_comm _ (z i)]
  have ht:=shelf_pay (s:=l· + η·) (k:=p.B) (biscuit_pos (p:=p)) i
  rw [show l·+η·+η· = T by unfold T highPace straightPace; ring] at ht
  exact mul_le_mul_of_nonneg_left ht (r i)

lemma Stops.filled (s:0≤g)
    (B:∀ o:Seat n,tallB g p.B l· o ≤ e) {J:Aura n→Support (More n)→ℝ}
    (hJ:∀ X:Aura n,∀ D⊆X.val,0≤ J X D)
    (u:∀ o:Seat n,tallB (roofL J 1) p.B l· o < γ):
    Timer (uChip z g J) z 1 l· η· (widthK n p.B) (spanV p.B)
      γ c (rider p c) e 1 g:=by
  have hx:=biscuit_pos (p:=p)
  have hm:η·/4<η·:=by linarith
  refine uGears z g J r s hJ _ _ _ _ _ _ _ _ _ (vigor n p.B) (jar v r t)
    (jar_tight v r t) (fun i=>by rw [←parse,mul_zero,sub_zero]; exact B i)
    le_rfl (Nat.cast_nonneg _) hx.le v.glow.le (v.lake.trans hm.le) v.can ?_ ?_
    (fun i=>by rw [←parse,mul_zero,sub_zero]; exact u i)
  · linarith [p.exponent_pos,show l· = p.supportExponent+5*η· from rfl]
  nlinarith only [v.pen, mul_le_mul_of_nonneg_right v.dew v.glow.le,
   mul_le_mul_of_nonneg_right v.lake v.glow.le, mul_pos hx v.glow]

end YM.CF.Organdy
