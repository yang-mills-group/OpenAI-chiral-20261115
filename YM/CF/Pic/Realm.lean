import YM.CF.Pic.Franc
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pic
open Function Filter Metric Finset NormedSpace Lattice Laurent Kea Lat Fir Tulip Rush Cube Jill Ember SU Dial Thera Fock Peaks Cascade Flare Scroll Spire
open scoped Topology BigOperators Matrix MatrixOrder ContDiff Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
lemma score {p:ℝ}(h:0≤p)(q:p≤1): Real.exp p-1 ≤2*p:=by
 have ht:‖(p:ℂ)‖≤1:=by simpa [abs_of_nonneg h]
 have hg:=Complex.norm_exp_sub_one_le ht; rw [←Complex.ofReal_exp,←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg h] at hg; exact (le_abs_self _).trans hg
variable {n:Type*}[LinearOrder n][Fintype n][Nonempty n]{P Q R K:Op n}{p q f:Wave n}{k v C d w:ℝ}{A B:FC n}{a b:ℂ}{U:UNI n}
lemma stroll(h:IsStarProjection P)(g:IsStarProjection Q)(l: U.valᵀ= -U.val)(t:‖P-Q‖≤k)(e: ‖stage P U.val-U.val‖ ≤1/3)(hp:Sea P p)(hq:Sea Q q)(u:k≤1/16)(c:16*Fintype.card n*k+|(a-b).im|≤1)(x:Complex.exp a • p= filled P U.val)(y:Complex.exp b • q=filled Q U.val)(w':0 ≤ w)(v: 2*k*(Fintype.card n)^2*w^2≤1) :∃ A:FC n,acts A p = q-p ∧ Pays w A (48*(Fintype.card n*k+|(a-b).im|)+4*k*(Fintype.card n)^2*w^2):=by
 obtain ⟨K,H,L⟩:= wire h g t (by linarith)
 let m:ℂ:=inner ℂ p q; let B:=exp (dg (laneP P 1 K)); have he:B=exp (dg (laneP P 1 K)):=rfl
 have hb: ‖m-1‖≤48*(Fintype.card n*k+|(a-b).im|):=gross h g l t e hp hq u c x y
 have hp':‖m‖≤1:= le_trans (norm_inner_le_norm ..) (by rw [hp.2,hq.2,mul_one])
 have hk:q=m • acts B p:=by have ht:= broomstick H q p hq hp; rw [quant_one,act_one,skyGlow,quant_one,act_one] at ht; exact ht
 have hr:= Pays.linear ((Pays.brick w' _ L).exp_sub) m
 refine ⟨(m-1) • 1+m • (B-1),?_,?_⟩
 · rw [act_add,act_smul,act_smul,act_one,act_sub,act_one,smul_sub, sub_smul,one_smul, ←hk]; abel
 let c:=2*k*(Fintype.card n)^2*w^2; have he:0≤c:=by have he:= (norm_nonneg _).trans t; unfold c; positivity
 apply ((Pays.uno.linear (m-1)).add hr).weigh _ w'; rw [mul_one]; apply add_le_add hb; change ‖m‖* (Real.exp c-1)≤_; apply (mul_le_of_le_one_left (by linarith [Real.one_le_exp he]) hp').trans; exact (score he v).trans_eq (by unfold c; ring)
end YM.CF.Pic
