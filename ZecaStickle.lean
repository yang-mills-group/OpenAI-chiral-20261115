import ZecaKelp
set_option autoImplicit false
set_option maxHeartbeats 440000
noncomputable section

namespace YM.ZecaSky
open Function Metric Filter Asymptotics Set
open scoped ComplexOrder InnerProductSpace BigOperators Topology

open Lattice Regis.Head.Brecht Regis.Circuit Stationary




variable {n:Gaia}{s α:ℝ}{z:ℂ}

def billFee (j i:Axis) (K:ℝ) :=
  ‖(-2*Maxwell.normal*(basis j i):ℂ)‖ * K^2+
  ‖(8 * Maxwell.normal:ℂ)‖ * K * K^2

lemma feePaid (j i:Axis) (d:‖n‖=1) (sp:1≤ s)
 (u:0≤α)(q:α<1)(e:|z.im|≤α*s):
 ‖bill j i (current n s z) (currentQ s z)‖ ≤ billFee j i (1-α^2)⁻¹:=by
 obtain ⟨a,w⟩:=kelp_pay j i d sp u q e
 have yp:=le_trans (norm_nonneg _) a
 unfold bill billFee
 apply (norm_add_le ..).trans (add_le_add _ _)
 · rw [norm_mul,norm_pow]
   gcongr
 · rw [show (currentQ s z)⁻¹^3=(currentQ s z)⁻¹ * (currentQ s z)⁻¹^2 from by ring,
      ← mul_assoc, mul_assoc (8*(Maxwell.normal:ℂ)) (current n s z j * current n s z i),
      norm_mul,norm_mul, norm_pow]
   gcongr

abbrev inFee(a b c d:Axis)(K:ℝ):=
 (if c=b then billFee a d K else 0)+(if d=b then billFee a c K else 0)
abbrev stampFee(p q:PlaqAxes)(K:ℝ):=
 (inFee p.val.1 p.val.2 q.val.1 q.val.2 K)+(inFee p.val.2 p.val.1 q.val.1 q.val.2 K)

lemma kelp_stamp(p a:PlaqAxes) (d:‖n‖=1) (sp:1≤ s)
 (u:0≤α)(q:α<1)(e:|z.im|≤α*s):
 ‖stamp p a (current n s z) (currentQ s z)‖ ≤ stampFee p a (1-α^2)⁻¹:=by
 unfold stamp curlIn
 apply (norm_sub_le ..).trans
 refine add_le_add ((norm_sub_le ..).trans (add_le_add ?_ ?_))
    ((norm_sub_le ..).trans (add_le_add ?_ ?_))
 all_goals split
 all_goals first | exact feePaid _ _ d sp u q e | simp

def stickleFee(colA:PlaqAxes→ℝ)(G:Gauge)(K:ℝ) :=
 ∑ p,∑ a, ‖(colA p:ℂ)*(colA a:ℂ)‖*(‖(2:ℂ)*Fintype.card G.ColorIndex‖*stampFee p a K^2)
lemma stickle_priced(colA:PlaqAxes→ℝ)(G:Gauge)
 (d:‖n‖=1) (sp:1≤ s)
 (u:0≤α)(q:α<1)(e:|z.im|≤α*s):
 ‖Kelper colA G n s z‖ ≤ stickleFee colA G (1-α^2)⁻¹:=by
 unfold Kelper satire wholeV stickleFee duoPower
 refine (norm_sum_le ..).trans (Finset.sum_le_sum (fun p _ =>
   (norm_sum_le ..).trans (Finset.sum_le_sum (fun a _ =>?_))))
 have y:=kelp_stamp p a d sp u q e
 rw [norm_mul, norm_mul (2*_ : ℂ), norm_pow]
 gcongr
#print axioms stickle_priced
#check DifferentiableOn.diffContOnCl_ball
