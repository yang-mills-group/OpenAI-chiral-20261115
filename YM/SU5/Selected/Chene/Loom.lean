import YM.SU5.Selected.Chene.Lit
/-!
 Uniform precision on the determinant appearing in the step preparation. At actual Torus. So relative to TRUE oriented sum with uncut rows; not an estimate in block structure presumed RP.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Chene.Tail
open Function Filter Matrix Lattice Wilson RG Tree SectorNext.Vacuum.FlatTree Precision Exterior Finset Pressure Pressure.Stores
open Next Next.SectorChange Next.SectorChange.Flat Next.Fluctuations CF.Neige CF.Newt CF.Char FreeResolvent MeasureTheory
open Rows AnalyticBridge.LocalGaussianLaws Work.F03 Bid Pad Trunk Melody
open scoped Topology BigOperators Matrix InnerProductSpace MatrixOrder Classical Kronecker
variable {c f:Side}{S:StepData c f}{G:Gauge}
variable (F:Forest S.ratio)(T:Tube G S)(K:Bed)(q:S.Choices){σ E X D u x η:ℝ}
variable (t:T.up.Bounds T.high σ E D)(h:S.patch.Branches S.kernel G)
local notation "O"=> Next.SectorChange.Flat.omitted T
local notation "I"=> Next.SectorChange.Flat.ideal T
local notation "A"=> T.high.direct
include T t
lemma cull (x:ℝ)(b:Signed)(w:Directions G f) : ∑ i, ‖O x w (b,i)‖^2 ≤ (rate_ell σ E (till x)/T.high.direct)*∑ i, ‖Next.SectorChange.Flat.ideal T w (b,i)‖^2:=by
 let V(i:Face (Per f)):= faceCurl i (pulled (Next.SectorChange.Flat.labels w) b)
 let F:= ∑ i, ‖V i‖^2; let G':= tail_r T.up (till x) V; have he: ∑ i,‖O x w (b,i)‖^2=∑ i,‖G' i‖^2:=by
    rw [Fintype.sum_sum_type,Fintype.sum_prod_type]; change _ + ∑ _i: Bond c, ‖(0:G.Color)‖^2=_; simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sum_const_zero,add_zero, Fintype.sum_bool]; -- tune norm etc
    apply sum_congr rfl; intro i _; change _ + ‖(0:G.Color)‖^2=_; simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,add_zero]; rfl
 have h0:0<A:= T.high.quadratic_pos
 have hp:A*F ≤ ∑ i,‖I w (b,i)‖^2:=by
    rw [Fintype.sum_sum_type,Fintype.sum_prod_type]; unfold F; rw [Finset.mul_sum]; apply le_trans _ (le_add_of_nonneg_right (sum_nonneg fun _ _=> sq_nonneg _)); apply sum_le_sum; intro i _; rw [Fintype.sum_bool]; change _≤ _+ ‖Real.sqrt A • V i‖^2; rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt h0.le]; exact le_add_of_nonneg_left (sq_nonneg _)
 rw [he]; apply (labor T.up t (till x) V).trans; let E':=rate_ell σ E (till x); have hP:0≤E':=mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _); change E'*F ≤_; apply le_trans _ (mul_le_mul_of_nonneg_left hp (div_nonneg hP h0.le)); exact Eq.le (by field)
include h
lemma comfort (x:ℝ)(θ:ℝ)(z:0≤θ) (hX: rate_ell σ E (till x) / T.high.direct ≤ θ^2) (w:Directions G f):
    let K:=sail (slip • bump T x 1 q w); let B:=sail (slip • Next.SectorChange.Flat.ideal T w); (1-θ)*B ≤ K ∧ K ≤ (1+θ)*B:=by
 let P:= slip • bump T x 1 q w; let X:= slip • I w; let V:= slip • (O x w); have he:X=P+V:= congrArg (slip • ·) (ideal_checks T q t h x w)|>.trans (smul_add ..)
 intro D C; have hx:sail V ≤ θ*C := by
    unfold V; change _ ≤ θ*sail X; unfold X; rw [carries,carries]; suffices v:sail (O x w) ≤ θ*sail (I w) by nlinarith [abs_nonneg slip]
    apply (sq_le_sq₀ (sail_nn _) (mul_nonneg z (sail_nn _))).mp; rw [mul_pow,quadratic,quadratic,Fintype.sum_prod_type,Fintype.sum_prod_type, Finset.mul_sum]; apply sum_le_sum; intro i _; apply (cull T t x i w).trans; apply mul_le_mul_of_nonneg_right hX; positivity
 have hp : C ≤ D+sail V := show sail X≤_ from he ▸ join P V; have hv: D ≤ C+sail V := show sail P ≤ _ from by rw [show P=X-V by rw [he]; abel]; exact sublease X V
 constructor <;> linarith
variable (p:Attached K T.up)(a:Floor K T.high f X u)(s: Bid.Sworn K f G)
include q p a s
lemma chalk (x:ℝ)(l:Bid.Larger (G:=G) S) (X0:0<X) (θ:ℝ)(z:0≤θ)(t':θ<1) (hθ: rate_ell σ E (till x) / T.high.direct ≤ θ^2):
    let R:= testD F T x q; let B:= treeMatrix G S F K.metric;
    let D:= Rᵀ*R; B.PosDef ∧ D.PosDef ∧ ( (1-θ)^2 • B ≤ D) ∧ D ≤ (1+θ)^2 • B :=by
 intro R B D; have hp:=a.symmetric.1; let P:= slip; have hb: B.PosDef:= by
    refine Trunk.pos_by_gap ?_ (treeFare_pos G S.patch S.kernel X0) (tree_gap S F K.metric l X0 ⟨fun x=>(a.uniform.1 x).1⟩)
    unfold B treeMatrix fullMatrix baseMatrix; rw [transpose_submatrix,tensor_transpose,transpose_add,transpose_smul,transpose_mul,transpose_transpose]; rw [Precision.K,transpose_mul,transpose_mul, hp, transpose_transpose, Matrix.mul_assoc]
 have hw:0<(1-θ)^2:=pow_pos (sub_pos.mpr t') _; have hh(v:Key F G→ℝ):
    v ⬝ᵥ (((1-θ)^2 • B)*ᵥ v) ≤ v ⬝ᵥ (D*ᵥ v) ∧ v ⬝ᵥ (D *ᵥ v) ≤ v ⬝ᵥ (((1+θ)^2 • B)*ᵥ v):=by
    rw [smul_mulVec,dotProduct_smul,smul_mulVec,dotProduct_smul]; simp only [smul_eq_mul]; unfold B D R; rw [←brilliant F T K q t h p a s x,←vision F T q t h x]; -- p parameter order
    obtain ⟨α,β⟩:= comfort T q t h x θ z hθ (CF.Char.trays S x F v); rw [←mul_pow,←mul_pow]; exact ⟨pow_le_pow_left₀ (mul_nonneg (sub_pos.mpr t').le (sail_nn _)) α _,pow_le_pow_left₀ (sail_nn _) β _⟩
 have hD:D.PosSemidef:= squared R
 have hs: (1-θ)^2 • B ≤ D := Matrix.le_iff.mpr (PosSemidef.of_dotProduct_mulVec_nonneg (hD.isHermitian.sub ((hb.smul hw).isHermitian)) (fun i=>by rw [star_trivial,sub_mulVec,dotProduct_sub]; exact sub_nonneg.mpr (hh i).1))
 have hk:0<(1+θ)^2:= pow_pos (by linarith) _; exact ⟨hb, Melody.pay_c (hb.smul hw) hs, hs, Matrix.le_iff.mpr (PosSemidef.of_dotProduct_mulVec_nonneg (((hb.smul hk).isHermitian).sub hD.isHermitian) (fun i=>by rw [star_trivial,sub_mulVec,dotProduct_sub]; exact sub_nonneg.mpr (hh i).2))⟩
lemma checkpoint (x:ℝ)(l:Bid.Larger (G:=G) S) (X0:0<X) (θ:ℝ)(z:0≤θ)(t':θ<1) (hθ: rate_ell σ E (till x) / T.high.direct ≤ θ^2): let B:= treeMatrix G S F K.metric; let C:= (baseX T x (bareStores S) F q 1).det; let D:= B.det; 0<D∧0<C ∧ 2* (Fintype.card (Key F G))*Real.log (1-θ) ≤ Real.log C-Real.log D ∧ Real.log C-Real.log D ≤ 2* (Fintype.card (Key F G))*Real.log (1+θ):=by
 intro B C D; let W:= testD F T x q; let E:= Wᵀ*W; have hK:C=E.det:=by unfold C; rw [←det_submatrix_equiv_self (pageX F x),← gramK F]; -- tune
 obtain ⟨hb,hd,hx,hy⟩:=chalk F T K q t h p a s x l X0 θ z t' hθ
 let χ:= Fintype.card (Key F G); let w:=(1-θ); let W':=1+θ; have hu:0<w:=sub_pos.mpr t'; have hv:0<W':=by unfold W'; linarith
 have he:0<(1-θ)^2:=pow_pos hu _; rw [hK]; have H:0<D:=hb.det_pos; refine ⟨H,hd.det_pos,?_,?_⟩
 · have hg:(w^2)^χ*D≤E.det:=by -- bizz pow nested left vs right ^
      rw [← det_smul B]; exact det_rise (hb.smul he).posSemidef hx
   have hp':= Real.log_le_log (mul_pos (pow_pos he _) H) hg
   rw [Real.log_mul (pow_pos he _).ne' H.ne',Real.log_pow,Real.log_pow] at hp'; unfold χ at hp'; push_cast at hp'; change _ ≤ Real.log E.det-Real.log D; linarith only [hp']
 have hg:E.det ≤ (W'^2)^χ*D:=(det_rise hd.posSemidef hy).trans_eq (Matrix.det_smul ..)
 have hp':=Real.log_le_log hd.det_pos hg; rw [Real.log_mul (pow_pos (pow_pos hv _) _).ne' H.ne', Real.log_pow,Real.log_pow] at hp'; unfold W' χ at hp'; push_cast at hp'; change Real.log E.det-Real.log D ≤_; linarith only [hp']
end YM.Chene.Tail
#print axioms YM.Chene.Tail.checkpoint
