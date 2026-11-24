import YM.SU5.Selected.Chene.Shale
import YM.Work.F03.Metric
/-! Norm estimates uniform in forest, on shortening. -/
set_option autoImplicit false
noncomputable section
namespace YM.Chene.Tail
open Function Filter Lattice Wilson RG Tree Finset Pressure Work.F03
open scoped Topology BigOperators
section
variable {I J T :Type*}[Fintype I][Fintype J] [NormedAddCommGroup T]
abbrev cloak(v:I→T) : PiLp 2 (fun _ : I=> T):= WithLp.toLp 2 v
def sail (v:I→T) := ‖cloak v‖
lemma receipt (v:I→T) : sail v=Real.sqrt (∑ i:I,‖v i‖^2):=PiLp.norm_eq_of_L2 _
lemma sail_nn (v:I→T):0≤sail v:=norm_nonneg _
lemma quadratic (v:I→T):sail v^2=∑ i:I,‖v i‖^2:=by rw [receipt,Real.sq_sqrt (by positivity)]
lemma sublease (v w:I→T):sail (v-w)≤ sail v+sail w:= norm_sub_le (cloak v) (cloak w)
lemma join (v w:I→T):sail (v+w) ≤ sail v + sail w:=norm_add_le (cloak v) (cloak w)
lemma carries [NormedSpace ℝ T] (v:I→T)(z:ℝ):sail (z • v)=|z| * sail v:= norm_smul z (cloak v)
lemma site_bill (u:I→J)(g:Injective u)(w:J→T)(v:I→T)(k:∀ j,‖v j‖ ≤‖w (u j)‖): sail v ≤ sail w:=by
 apply (sq_le_sq₀ (sail_nn _) (sail_nn _)).mp; rw [quadratic,quadratic]; refine le_trans (Finset.sum_le_sum (g:=fun j=> ‖w (u j)‖^2) (fun i _=> pow_le_pow_left₀ (norm_nonneg _) (k i) _)) ?_; exact FreeResolvent.Cost.sum_comp_le (f:=u) g (fun i => ‖w i‖^2) (fun i => sq_nonneg _) -- tune
end
variable {G:Gauge} {c:Clip} {σ C Λ :ℝ} {n:Side} (W : PathData G)
variable {T:Type*}[NormedAddCommGroup T][NormedSpace ℝ T][CompleteSpace T] (p:W.Bounds c σ C Λ)
def visit (k r:ℕ)(x:Face (Per n))(v:Face (Per n)→T):T:=
 if r < (W.row x.2 k).2.length then (W.row x.2 k).1 • v (slotFace (W.row x.2 k).2 x.1) else 0
include p
lemma capital : 0≤C:=by
 let v:= p.rows ⟨(0,1),by decide⟩; exact (tsum_nonneg v.1).trans v.2.2
local notation "Q" => Site n
local notation "F" => Trunk.circle n
def tail_r (r:ℕ)(v:F→T)(x:F):= ∑' (i:ℕ),visit W i r x v -- local notation caution
abbrev tax (K σ:ℝ)(r:ℕ) := K*Real.exp (-(σ*r))
omit p in
lemma tax_positive {r:ℕ} (p:0≤C)(a:ℝ): 0≤tax C a r:= mul_nonneg p (Real.exp_pos _).le -- omit W p
lemma stair (b:PlaqAxes)(r:ℕ)(v:F→T) : sail (fun x:Q=> tail_r W r v (x,b)) ≤ tax C σ r * sail v:=by
 let X(i:ℕ):= cloak (fun x:Site n=> visit W i r (x,b) v); let L(i:ℕ):=(W.row b i).2; let W'(i:ℕ):= |(W.row b i).1| *  Real.exp (σ*(L i).length); let E:= Real.exp (-(σ*r))*sail v
 let h(i:ℕ) := slotFace (L i) (n:=n); have hp:= p.rows b; have hv : 0 ≤ E := mul_nonneg (Real.exp_pos _).le (sail_nn v)
 have he(i:ℕ):‖X i‖ ≤ W' i*E:=by
    unfold X visit; by_cases u:r <(L i).length
    · change ‖cloak (fun x:Q=> if r < (L i).length then _ else _)‖≤ _; simp only [if_pos u]; change sail ((W.row b i).1 • fun x:Q=> v (h i x)) ≤_
      rw [carries]; have hs:Injective (h i):=fun j k v=>add_left_cancel (congrArg Prod.fst v); refine (mul_le_mul_of_nonneg_left (site_bill (h i) hs _ _ (fun i=>le_rfl)) (abs_nonneg _)).trans ?_
      unfold W' E; rw [mul_assoc,←mul_assoc (Real.exp _),← Real.exp_add]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); apply le_mul_of_one_le_left (sail_nn _); exact Real.one_le_exp (by nlinarith only [show (r:ℝ) ≤ (L i).length by exact_mod_cast u.le,p.width])
    change ‖cloak (fun x:Q=> if r < (L i).length then _ else _)‖≤ _; simp only [if_neg u]; change ‖cloak (0:Q→T)‖ ≤_; rw [show cloak (0:Q→ T)=0 from rfl,norm_zero]; exact mul_nonneg (hp.1 i) hv -- tune
 have hh : Summable W':=hp.2.1; have hs':Summable (fun i=>‖X i‖):=Summable.of_nonneg_of_le (fun i=>norm_nonneg _) he (hh.mul_right E)
 rw [sail,show cloak (fun x:Q=> tail_r W r v (x,b))=∑' i,X i from ?_]; swap
 · ext1 i; have hT:= (PiLp.proj (𝕜:=ℝ) 2 _ i).hasSum (hs'.of_norm).hasSum; exact hT.tsum_eq -- ext1 changes?
 refine (norm_tsum_le_tsum_norm hs').trans ((hs'.tsum_le_tsum he (hh.mul_right _)).trans ?_); rw [tsum_mul_right]; apply (mul_le_mul_of_nonneg_right (show _ ≤ C from hp.2.2) hv).trans_eq; unfold E tax; ring
-- Square pricing. limit used even when no omission because tiny torus.
abbrev rate_ell(σ C:ℝ)(r:ℕ):=(Fintype.card PlaqAxes:ℝ)*(tax C σ r)^2
lemma labor(r:ℕ)(v:F→ T) : ∑ i, ‖tail_r W r v i‖^2 ≤ rate_ell σ C r *∑ i, ‖v i‖^2:=by
 rw [Fintype.sum_prod_type, sum_comm]; let A:=tax C σ r; let B:=sail v; refine (sum_le_sum (g:=fun _=>(A*B)^2) (fun i _=> ?_)).trans_eq ?_
 · have he:= pow_le_pow_left₀ (sail_nn _) (stair W p i r v) 2; rw [quadratic] at he; exact he
 rw [sum_const,mul_pow, quadratic v]; unfold rate_ell; rw [card_univ]; push_cast; unfold A; ring
end YM.Chene.Tail
