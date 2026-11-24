import YM.CF.BPress.Chalk.Marker
/-! § VolumeB-phase eq:B-Jrep. Letters of species one. Explicit row convention and site localization, not diagonal approximation. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Lily
open Function MeasureTheory Filter NormedSpace Finset Fock Lattice Cube Lat Spin Spin.Paint SU SU.Pair Chalk Pf Pressure Branch Bias Dial Nacre Tulip
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical
attribute [local instance] opCStarAlgebra
variable {I:Type}[Fintype I][LinearOrder I][Nonempty I]{C: Op I}
abbrev fract :ℂ := (Real.sqrt 2 : ℝ)⁻¹ -- coer tune
lemma fract_s : star fract=fract:=by unfold fract; simp
lemma fract_sq : fract*fract=1/2:=by unfold fract;  have he:= Real.sq_sqrt (by norm_num : (0:ℝ)≤ 2);  rw [←Complex.ofReal_inv, ←Complex.ofReal_mul, ←Complex.ofReal_one, ← Complex.ofReal_ofNat, ←Complex.ofReal_div, Complex.ofReal_inj]; field_simp; nlinarith

-- column form for Wick test
abbrev φ (C:Op I):=fract • (-Cᵀ)
abbrev ϕ (I:Type)[Fintype I][DecidableEq I]:= fract • (1:Op I)
def glyph (C:Op I) (i:I):FC I:= introW (φ C) (ϕ I) i
lemma pet (i:I): glyph C i= fract • (takeF i - coupleRow C i):=by
 rw [glyph,introW,letters,l_basis]; unfold prong φ ϕ coupleRow; -- tune via sum
 simp_rw [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, mul_ite, mul_zero, ite_smul,zero_smul, mul_one, sum_ite_eq',mem_univ,ite_true, ← smul_smul]; rw [smul_sub,sub_eq_add_neg]; refine (add_comm ..).trans ?_; apply congrArg; simp only [Matrix.neg_apply, Matrix.transpose_apply, neg_smul, smul_neg, Finset.sum_neg_distrib, Finset.smul_sum]
lemma conjugate (A B:Op I)(i:I):Star.star (introW A B i)=introW (cc B) (cc A) i:=by simp only [introW,letters,letterV,remove,star_add,star_star, echo_s,echo_b, cc_cc]; rw [add_comm]
lemma car_form (A B U V:Op I)(i j:I) : antiB (introW A B i) (introW U V j)=( (Bᵀ*U + Aᵀ*V) i j) • 1:=by
 unfold antiB introW letters; rw [l_CAR]; unfold τpair; apply congrArg (· • (1:FC I)); rw [soundM,soundM,Matrix.add_apply]; congr 1; simp only [Matrix.mul_apply, Matrix.transpose_apply]; apply sum_congr rfl; intro; intro; exact mul_comm ..
lemma glyph_duo (h:Cᵀ= -C)(i j:I):antiB (glyph C i) (glyph C j)=0:=by
 rw [glyph,glyph,car_form]; suffices ht:(ϕ I)ᵀ*φ C + (φ C)ᵀ*ϕ I=0 by rw [ht]; simp
                                                            -- indentation repair
 unfold ϕ φ; simp only [Matrix.transpose_smul,Matrix.transpose_neg,Matrix.transpose_transpose,Matrix.transpose_one]; rw [Matrix.smul_mul, Matrix.mul_smul,Matrix.smul_mul, Matrix.mul_smul,h, neg_neg,one_mul,mul_one]; simp -- tune
lemma glyph_zero (h:Cᵀ= -C) (i:I): glyph C i*glyph C i=0:=by ext q p; exact add_self_eq_zero.mp (Matrix.ext_iff.mpr (glyph_duo h i i) q p)
lemma glyph_pair (h:Cᵀ= -C)(p:C∈unitary (Op I))(i j:I): antiB (glyph C i) (Star.star (glyph C j)) =if i=j then 1 else 0:=by
 rw [glyph,glyph,conjugate,car_form]; have ht: (ϕ I)ᵀ*cc (ϕ I)+(φ C)ᵀ*cc (φ C)=1:=by
    have he:C*cc C= -1:=by
       rw [cc]; have hp: (star C)ᵀ= -star C:= by rw [show (star C)ᵀ=star Cᵀ from rfl,h,star_neg]
                             -- parser
       rw [hp,mul_neg,p.2] -- ℕ tune
    unfold ϕ φ; simp only [cc_smul, cc_one, Matrix.transpose_smul,Matrix.transpose_one, fract_s,h,neg_neg,Matrix.smul_mul,Matrix.mul_smul,smul_smul,one_mul,neg_mul,he]; rw [fract_sq,← add_smul,add_halves,one_smul] -- tune
 rw [ht]; by_cases h:i=j <;> simp [Matrix.one_apply,h]
lemma glyph_s (h:Cᵀ= -C)(i:I): acts (glyph C i) (pairWave C)=0:=by rw [pet,act_smul,act_sub,pull h, sub_self,smul_zero]
lemma priced_g (h:Cᵀ= -C)(p:C∈unitary (Op I))(i:I): ‖glyph C i‖≤1:=by
 let Y:= glyph C i; have hm: Y*star Y+star Y*Y=1:= (glyph_pair h p i i).trans (if_pos rfl); have ht:Y*star Y ≤ 1:= hm ▸ le_add_of_nonneg_right (star_mul_self_nonneg Y) -- maybe tune ▸ crazy
 have hb:= CStarAlgebra.norm_le_one_iff_of_nonneg _ (show 0≤Y*star Y from mul_star_self_nonneg ..); -- name
 have he:= CStarRing.norm_self_mul_star (x:=Y); nlinarith [norm_nonneg Y,hb.2 ht] -- tune
variable {N:Side} {H:Paint (More N)}
lemma axial_glyph (x:Site N)(i:Single N)(l:i∈ den x):glyph (coupling H) i=glyph (regent H x) i:=by
 rw [pet,pet]; let f(C:Op (Single N)):=coupleRow C i; congr 2; -- tune target
 unfold coupleRow; apply sum_congr rfl; intro k u; apply congrArg (· • put k); have he:i.1.1=x:= (mem_filter.mp l).2; rw [regent,yore_at,atX]; by_cases h:k.1.1=x<;>simp [penX,h,he,Ne.symm,home]
lemma axial_petal (x:Site N)(K:Op Slot)(i:Single N)(t:i∈ den x): Sector (den x) true (glyph (Yore x K) i):=by
 rw [pet]; apply Sector.scale; rw [sub_eq_add_neg, ←neg_one_smul ℂ]; refine (Sector.down i t).add (Sector.scale ?_ _); unfold coupleRow; apply Sector.sumS; intro j _; by_cases h:j∈den x; exact (Sector.up j h).scale _; rw [yore_at,if_neg (fun u=>h (mem_filter.mpr ⟨mem_univ _,u.2⟩)), zero_smul]; exact .zero _
lemma axial_skew (x:Site N)(P: Op Slot)(p:Spin.Sym P): (Yore x P)ᵀ= -(Yore x P):=by unfold Yore; simp only [Matrix.transpose_mul,self_t,Chalk.shelf]; rw [Paint.skew (N:=N) _ (fun i=>p)]; simp only [neg_mul,mul_neg,mul_assoc] -- tune self_t location
lemma glyph_cont (i:I): Continuous (fun C:Op I=> glyph C i):=by simp_rw [pet, coupleRow]; refine Continuous.smul (f:=fun _:Op I=>fract) continuous_const (continuous_const.sub ?_); refine continuous_finsetSum _ (fun j _=>?_); exact Continuous.smul ((continuous_id (X:=Op I)).matrix_elem i j) (g:=fun _:Op I=>Fock.put j) continuous_const
end YM.CF.BPress.Lily
