import YM.CF.BPress.Engine.Gauge
import YM.CF.Pec.Ora
/-! Pigment strong row prices on every field. sum-rows matrix notation incl centroid choice assigning spins a repeated cost (`/card_page`). No H dependence. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Nougat
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Pec Spin SpinSign Spin.Pledge Pledge.Costs Cube Lat SU Spin.Paint Nacre Laic Font Push.AbsoluteSums.Paths Tulip Tenant Dial -- check
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical YM.CF.BPress.Vesper
attribute [local instance] opCStarAlgebra
variable {N:Side}(i j:Single N) (z:Ok N × Ok N) (W:Pride N)
local notation "T_"=> home N
local notation "U_"=> T_ i
def footInk := native U_ (boot U_ z.1) ∪ native U_ (boot U_ z.2)
lemma feetInk : (footInk i z).card ≤8*contour U_ z.1 z.2 + (18:ℝ) ∧ U_∈footInk i z ∧ Grove (Grid.field 4 (More N)) (footInk i z):=by
 have ht(z:Ok N):U_ ∈ native U_ (boot U_ z):= Wealth.walks_first ..; refine ⟨?_, mem_union_left _ (ht _), (Wealth.walks_g ..).unite (Wealth.walks_g ..) (ht _) (ht _)⟩
 have he(z:Ok N):(native U_ (boot U_ z)).card≤8*(dial U_ z+1)+1:=(Wealth.walks_n ..).trans (Nat.add_le_add_right (leanB ..) 1); apply (Nat.cast_le (α:=ℝ)|>.mpr (show (footInk i z).card ≤ _ from (card_union_le ..).trans (add_le_add (he z.1) (he z.2)))).trans_eq; unfold contour; push_cast; ring -- tune ambiguity
abbrev stream_i(u: Post N):= (inner ℝ (silt U_ z.1 u) (silt U_ z.2 u)) • W i.1.1 z.1 z.2
def money_i:=32*(1+contour U_ z.1 z.2)* ‖W i.1.1 z.1 z.2‖ -- notation U_ shadow fallback
lemma money_c  :0≤ money_i i z W :=by unfold money_i; have ht:=ct_pos (home N i) z.1 z.2; positivity
lemma ledger_i : Expo (Sifting.outlook N).stage (footInk i z) i i (money_i i z W) (stream_i i z W):=by
 obtain ⟨_,hv,hu⟩:= feetInk i z; let f(x:Ok N)(v:Post N):=silt U_ x v; have ht(x:Ok N): Continuous (f x):= group.continuous_curvature.comp (continuous_travel ..); have hs(x:Ok N)(v:Post N):‖f x v‖≤2:=(group.curvature_norm _).trans (group.chord_le_two _); let c₁(z):ℝ:=dial U_ z; let a:=W i.1.1 z.1 z.2; have h(z:Ok N):0≤c₁ z:=Nat.cast_nonneg _
 refine ⟨money_c ..,fun _=>⟨hu,hv,hv⟩,fun x=>?_ ,fun x y=>?_ , (Continuous.inner (𝕜:=ℝ) (ht z.1) (ht z.2)).smul continuous_const⟩
 · unfold stream_i; rw [norm_smul]; unfold money_i; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); apply (norm_inner_le_norm ..).trans; apply le_trans (mul_le_mul (b:=(2:ℝ)) (d:=2) (hs ..) (hs ..) (norm_nonneg _) (by norm_num)); unfold contour; linarith [h z.1,h z.2] -- tune binder
 let X:= invitation (footInk i z) x y; have hX:0≤X:= invitation.positive; unfold stream_i; rw [←sub_smul, norm_smul]; change _ ≤ 32*(1+(c₁ z.1+c₁ z.2))*_ * X; rw [mul_right_comm _ _ X]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); let u:=f z.1; let v:=f z.2; rw [show inner ℝ (u x) (v x)-inner ℝ (u y) (v y)=inner ℝ (u x-u y) (v x)+inner ℝ (u y) (v x-v y) by rw [inner_sub_left,inner_sub_right]; ring]; apply (norm_add_le ..).trans; let M(z):= 8*(c₁ z+1)*X; have hp(z:Ok N):0≤ M z:= mul_nonneg (mul_nonneg (by norm_num) (add_nonneg (h z) zero_le_one)) hX; have ht':= le_trans (norm_inner_le_norm (𝕜:=ℝ) (u x-u y) (v x)) (mul_le_mul (show ‖u x-u y‖≤ M z.1 from Sifting.sifter i x y z.1 subset_union_left) (hs z.2 x) (norm_nonneg _) (hp _)); have he:= le_trans (norm_inner_le_norm (𝕜:=ℝ) (u y) (v x-v y)) (mul_le_mul (hs z.1 y) (show ‖v x - v y‖ ≤ M z.2 from Sifting.sifter i x y _ subset_union_right) (norm_nonneg _) (by norm_num)); refine (add_le_add ht' he).trans ?_; unfold M; nlinarith [h z.1,h z.2]
end YM.CF.BPress.Nougat
