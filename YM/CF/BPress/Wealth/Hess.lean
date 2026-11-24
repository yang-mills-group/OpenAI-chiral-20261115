import YM.CF.BPress.Wealth.Ray
/-! `eq:B-Hess` on angular columns. Positive real operator with gap mass exactly for every S. Spectral estimates via this form. Upper count over all foot-root charges, (regular subset). No Gaussian-sector-probability assumptions. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Wealth
open Function Filter MeasureTheory LocalH Lattice Wilson RG Precision Grid Push.AbsoluteSums Branch Ledger Cube Bands Tunnel Pressure Finset
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace ContDiff
open SU Gauge
attribute [local instance] Gauge.frobInner
variable {s:Side}{B:BandWidth}(X:Bands s B) (M:ℕ) (R:PathData group) (d:Clip) (β y:ℝ){σ C Λ:ℝ}(H:R.Bounds d σ C Λ)(S:Finset X.Hcols)(w v : RaySpace X)
local notation "ℬ" => BEnd X
abbrev Θ (S:Finset X.Hcols) := univ.filter fun i=> retained X M i ∧ regular (X:=X) (M:=M) S i
def hBet (β y:ℝ)(i:Root s):= wgt d i * (β*BPress.g y^2)
def columnP (i:Root s) : BEnd X:= let f:= shine X M R H i; hBet d β y i • ((ContinuousLinearMap.adjoint f).comp f)
def hessian : BEnd X:= (∑ i∈ Θ X M S,columnP X M R d β y H i)+keeper X S
lemma act2 (i:Root s) : inner ℝ w (columnP X M R d β y H i v)= hBet d β y i* inner ℝ (shine X M R H i w) (shine X M R H i v):= by simp_rw [columnP, ContinuousLinearMap.smul_apply, real_inner_smul_right, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
lemma act_sym (i:Root s): inner ℝ w (columnP X M R d β y H i v)= inner ℝ v (columnP X M R d β y H i w):= by rw [act2,act2,real_inner_comm (x:=shine X M R H i w)] -- tune arg
lemma section_sym : IsSelfAdjoint (hessian X M R d β y H S):= by
 rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]; intro w v; rw [real_inner_comm v _]; change inner ℝ v _= inner ℝ w _; change inner ℝ v (hessian X M R d β y H S w)= inner ℝ w (hessian X M R d β y H S v); unfold hessian; simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply, inner_add_right, inner_sum]; apply congrArg₂ (·+·); · exact sum_congr rfl fun i _=> act_sym ..
 exact (real_inner_comm ..).trans (ray_mask X S w v) -- tune wv
lemma quadP (i:Root s): inner ℝ w (columnP X M R d β y H i w)=hBet d β y i * ‖shine X M R H i w‖^2:=by rw [act2,real_inner_self_eq_norm_sq]
def picture (W:Bills X ink) : Directions group s:= canon X ((BPress.g y) • W)
lemma picture_stay (i:Root s): form R M i (picture X y (lead X w))= (BPress.g y) • shine X M R H i w:=by rw [picture,map_smul]; exact shape_smul M R H _ _ _
lemma epoch (i:Root s): inner ℝ w (columnP X M R d β y H i w)/2=second R d M β i (picture X y (lead X w)):=by rw [quadP,second,picture_stay X M R d y H w i,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]; unfold hBet; ring
lemma epoch_area : inner ℝ w (hessian X M R d β y H S w)/2= ∑ i∈ Θ X M S,second R d M β i (picture X y (lead X w)) + ‖keepOnly X S w‖^2/2:= by
 unfold hessian; simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply, inner_add_right, inner_sum]; rw [add_div,Finset.sum_div] -- tune rw direction
 simp_rw [epoch, show inner ℝ w (keeper X S w)= _ from mask_norm X S w] -- tune
lemma bet_g (p:0<y)(q:β∈ Set.Icc (y/2) (2*y)): 1/2 ≤ β*BPress.g y^2 ∧ β*BPress.g y^2≤2:=by
 obtain ⟨h,t⟩:=q; rw [gscale p.le]; constructor; apply le_trans ?_ (mul_le_mul_of_nonneg_right h (by positivity)); field_simp; rfl; apply le_trans (mul_le_mul_of_nonneg_right t (by positivity)); field_simp; rfl

lemma splitSoft (X:Bands s B) (S:Finset X.Hcols)(w:RaySpace X) : ‖w‖^2= ‖keepOnly X S w‖^2 + ‖keepOnly X Sᶜ w‖^2:=by rw [←mask_norm,←mask_norm,←inner_add_right,←mask_add,real_inner_self_eq_norm_sq] -- tune rewrite ambiguous

variable (p: 0<y)(t:β∈ Set.Icc (y/2) (2*y))(h:High B M)
include p t
lemma gate_safe (i:Root s) : 0≤ hBet d β y i∧ hBet d β y i ≤ (d.direct+ chPrice)*2:=by
 unfold hBet; obtain ⟨u,v⟩:= bet_g β y p t; have hb:= weight_price d i; have ht:0≤ β*BPress.g y^2:= le_trans (by norm_num) u; exact ⟨mul_nonneg hb ht, mul_le_mul (direct_price d i) v ht (hb.trans (direct_price ..))⟩
lemma vP (i:Root s) : 0≤ inner ℝ w (columnP X M R d β y H i w):= by rw [quadP]; exact mul_nonneg (gate_safe d β y p t i).1 (sq_nonneg _)
lemma barR (i:X.Air) : (d.direct*(1/2)) * ‖lead X w i- past X (lead X w) i‖^2 ≤ inner ℝ w (columnP X M R d β y H (.inl (vert X i)) w):=by
 rw [quadP,show ‖shine X M R H (.inl (vert X i)) w‖= _ from v_norm X i (lead X w) R M]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (bet_g β y p t).1 d.quadratic_pos.le) (sq_nonneg _)

def massL (B:BandWidth)(d:Clip) := min 1 ((d.direct/2)/(B.D:ℝ)^3)
omit t p
lemma mass_pos (B:BandWidth): 0<massL B d:= by
 unfold massL; have he:(0:ℝ)<B.D:=by exact_mod_cast B.D_pos
 positivity [d.quadratic_pos]
private lemma filt2 {f: X.Air→ℝ} (S:Finset X.Hcols) : ∑ i∈ (univ.filter (fun i:X.Air=> i.1∈ S)),f i=∑ p∈ S, ∑ j:SpatialDir,∑ a: Fin B.D,f (p,a,j):=by
 rw [sum_filter,Fintype.sum_prod_type]; refine Eq.trans (b:=∑ p:X.Hcols,(if p∈S then (∑ j:SpatialDir,∑ a:Fin B.D,f (p,a,j)) else 0)) ?_ (by rw [←sum_filter]; simp); apply sum_congr rfl; intro i _; by_cases p:i∈S <;> simp [p]
 rw [Fintype.sum_prod_type_right]

include h p t
lemma front_charge : massL B d*‖keepOnly X Sᶜ w‖^2 ≤ ∑ i∈ Θ X M S, inner ℝ w (columnP X M R d β y H i w):=by
 let A:=univ.filter fun i:X.Air=> i.1∈ Sᶜ; let f(i:X.Air) : Root s:= Sum.inl (vert X i); have hf: Injective f:= fun a b p => vert_one X (Sum.inl.inj p); let W(i):= inner ℝ w (columnP X M R d β y H i w); have hv(i) : 0≤W i:=vP X M R d β y H w p t i
 refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg (s:=A.image f) ?_ (fun i _ _=> hv i)); swap; · intro i v; obtain ⟨x,e,rfl⟩:= mem_image.mp v; exact mem_filter.mpr ⟨ mem_univ _, vert_ret X M x,(use_vert h S x).2 (mem_compl.mp (mem_filter.mp e).2)⟩
 rw [sum_image]; swap; · exact fun i _ j _ v=> hf v
 let v(i:X.Air) := lead X w i; let L:= massL B d; let g(i:X.Air):= point B (fun k=>v (i.1,k,i.2.2)) i.2.1; have hz(i:X.Air) : d.direct*(1/2)*‖g i‖^2 ≤ W (f i):= barR X M R d β y H w p t i; apply le_trans _ (sum_le_sum (f:=fun i:X.Air=> d.direct*(1/2)*‖g i‖^2) (g:=W ∘ f) (fun i (_:i∈ A)=>hz i)); rw [tally_ray, ←sum_filter, filt2]; unfold A; rw [filt2]; simp_rw [mul_sum]; refine sum_le_sum fun i u=> sum_le_sum fun j _=> ?_
 let z:=fun k=> v (i,k,j); let Q:=verticalE B z; have hp(i:Fin B.D): ‖z i‖^2 ≤ (B.D:ℝ)^2 * Q:= costsD B z i; have hB:(0:ℝ)<B.D:= by exact_mod_cast B.D_pos
 have hQ:0≤Q:= by unfold Q verticalE; positivity
 apply le_trans (sum_le_sum (fun l (_:l∈ univ)=> mul_le_mul_of_nonneg_left (hp l) (show 0≤L from (mass_pos d B).le))); rw [sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin,←mul_sum]; change (B.D:ℝ)* _ ≤ d.direct*(1/2)*Q; have hh:L≤ (d.direct/2)/(B.D:ℝ)^3:= min_le_right ..; replace hh:=(le_div_iff₀ (pow_pos hB _)).mp hh; nlinarith only [mul_le_mul_of_nonneg_right hh hQ]
lemma mass_lower : massL B d*‖w‖^2 ≤ inner ℝ w (hessian X M R d β y H S w):=by
 unfold hessian; rw [splitSoft X S w,mul_add]; simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply, inner_add_right, inner_sum]; rw [add_comm]; exact add_le_add (front_charge X M R d β y H S w p t h) ((mul_le_of_le_one_left (sq_nonneg _) (show massL B d≤1 from min_le_left ..)).trans_eq (mask_norm ..|>.symm)) -- tune
end YM.CF.BPress.Wealth
