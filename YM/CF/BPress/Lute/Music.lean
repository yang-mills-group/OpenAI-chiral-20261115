import YM.CF.BPress.Lute.Pebbles
/-! eq:B-Gz. center block choices three copies of actual Sheet. leftover all five negative. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Lute
open Function Finset Filter NormedSpace InnerProductSpace SU SU.Pair Spin Spin.Paint Lattice Fock Complex Tile Join
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker InnerProductSpace ContDiff
attribute [local instance] opCStarAlgebra
local notation "π"=>Real.pi
namespace Music
abbrev Twins:=F×Two
abbrev Grouping:=Twins⊕F
abbrev TenE : (F⊕F)≃Ten:=Fintype.equivOfCardEq (by rw [pairs]; simp [F])
def ensemble : Grouping≃SU.Sheet where
 toFun | Sum.inl (i,u)=> if u=0 then .inl (TenE (Sum.inl i)) else .inr i | .inr k=> .inl (TenE (Sum.inr k))
 invFun | Sum.inr i=> .inl (i,1) | .inl u=> Sum.elim (fun i : F=>Sum.inl (i,(0:Two))) Sum.inr (TenE.symm u)
 left_inv x:=by rcases x with ⟨i,t⟩|t; fin_cases t <;> simp; simp
 right_inv x:=by rcases x with i|i; obtain ⟨i|i,rfl⟩:= TenE.surjective i <;> simp; simp
lemma refit_unit (A:Op Grouping)(h:A∈unitary (Op Grouping)) : refit ensemble A∈unitary (Op SU.Sheet):=(renU ensemble ⟨A,h⟩).property
abbrev spiceX : F→ℝ:=![0,0,0,m,1]
abbrev spiceY : F→ℝ:=![1,1,1,m,0]
def pair (k:F):Op Two:=chip (spiceX k) (spiceY k)
def dash (θ:ℝ):Op Twins:= zoneC (fun _=> levy θ)
def high (θ:ℝ): Op Grouping:= both (dash θ) (χ (-2*θ) • (1:Op F))
def songB : Op Grouping:= both (zoneC pair) (-(1:Op F))
lemma pair_u (k:F): pair k∈unitary (Op Two)∧ (pair k).det= -1:=by refine unit_chip ?_; fin_cases k <;> first| (change m*m+m*m=1; rw [m_sq]; norm_num)| norm_num [spiceX,spiceY]

lemma κ_θ (i:Fin 5){θ:ℝ}(p:χ θ=SU.z^i.val): fund (Mag.center i)⁻¹=χ (-θ) • (1:Op F):=by rw [fund_inv, show fund _=χ θ • (1:Op F) by rw [p]; exact Mag.mat_center i, star_smul,χ_cc,star_one]
private lemma masks (θ:ℝ) : each (χ (-θ) • (1:Op F)) = refit ensemble (high θ):=by
 rw [show χ (-θ) • (1:Op F)=Matrix.diagonal (fun _=>χ (-θ)) from (by ext i j; by_cases h:i=j<;>simp [h]), each, ExTwo.wedge_diag, show cc _=Matrix.diagonal (fun _:F=>χ θ) by ext i j; by_cases h:i=j <;> simp [cc_apply,h]]
 have ht:χ (-θ)*χ (-θ)=χ (-2*θ):=by rw [←χ_add]; congr 1; ring
 ext x y; obtain ⟨x,rfl⟩:=ensemble.surjective x; obtain ⟨y,rfl⟩:=ensemble.surjective y; rw [replaces,Equiv.symm_apply_apply, Equiv.symm_apply_apply]; rcases x with ⟨i,x⟩|i <;> rcases y with ⟨j,y⟩|j
 all_goals try fin_cases x
 all_goals try fin_cases y
 all_goals by_cases h:i=j <;> simp [ht,h, ensemble,both,high,dash, zoneC,jump_apply,levy,←neg_mul]
lemma high_occ(i:Fin 5){θ:ℝ}(p:χ θ=SU.z^i.val) : (matter (Mag.center i)⁻¹).val=(1:Op (Fin 3))⊗ₖ refit ensemble (high θ):=by rw [matter_matrix, triple, κ_θ _ p,masks]
lemma song_score : songB∈unitary (Op Grouping)∧songBᵀ=songB∧star songB=songB∧songB.det=1:=by
 let A:= -(1:Op F); have hg:A∈unitary (Op F):=⟨by simp [A],by simp [A]⟩; refine ⟨both_unitary (jump_unitary _ pair (fun i=> (pair_u i).1)) hg, ?_,?_,?_⟩; · unfold songB; rw [both_tran,zone_tran, show (fun i:F=>(pair i)ᵀ)=pair from funext fun i=>(in_chip ..).1,Matrix.transpose_neg,Matrix.transpose_one]
 · unfold songB; rw [star_both]; simp only [star_neg,star_one,zoneC,jump_star]; congr; ext1 i; exact (in_chip ..).2
 rw [songB,both_det,zoneC,Mir.jump_det]; simp_rw [(pair_u _).2]; rw [Matrix.det_neg]; norm_num [F]
-- full copies
abbrev bandB:=refit ensemble songB
def basis:Op Slot:= (1:Op (Fin 3)) ⊗ₖ bandB
lemma basis_acts : Spin.Sym basis:=by
 obtain ⟨p,x,h,k⟩:=song_score; unfold basis bandB; constructor
 · rw [←Matrix.kroneckerMap_transpose, Matrix.transpose_one, ← refit_T, x]
 · exact Matrix.kronecker_mem_unitary ((unitary _).one_mem) (refit_unit songB p)
 rw [Matrix.det_kronecker,Matrix.det_one,refit_ne,k]; simp
lemma basis_flip : IsSelfAdjoint basis:=by unfold basis; apply (show star _ = _ from ?_); rw [op_star_kron,star_one]; unfold bandB; rw [←map_star,song_score.2.2.1] -- tune
abbrev wave(z:Fin 5): Op Slot:= Paint.swivelC (Mag.center z)⁻¹ basis
lemma wave_s (i:Fin 5): Spin.Sym (wave i):= turn_plan basis_acts _
lemma meter (i:Fin 5) {θ:ℝ} (g:χ θ=SU.z^i.val): wave i*star basis=(1:Op (Fin 3))⊗ₖ refit ensemble (high θ* songB*(high θ)ᵀ*star songB):=by
 unfold wave swivelC congrC; rw [high_occ i g]; simp only [basis,bandB, ← Matrix.kroneckerMap_transpose, op_kron_mul,Matrix.transpose_one, op_star_kron,map_mul,star_one,one_mul, refit_T, map_star]
private lemma portion (θ:ℝ): high θ*songB*(high θ)ᵀ *star songB= both (zoneC (fun i:F=> board θ (spiceX i) (spiceY i))) (χ (-4*θ) • (1:Op F)):=by
 unfold high songB; rw [both_tran,star_both,both_mul, both_mul, both_mul]; congr 1
 · unfold dash; simp only [zone_tran,zoneC,jump_mul,jump_star,Equiv.refl_trans,Equiv.refl_symm]; rfl
 rw [Matrix.transpose_smul,Matrix.transpose_one,star_neg,star_one, Matrix.smul_mul, Matrix.mul_smul]; simp only [one_mul, Matrix.smul_mul, _root_.mul_neg, neg_mul, Matrix.mul_smul,mul_one, smul_neg, neg_neg]; rw [smul_smul,← neg_mul,← neg_mul,(phases_val θ).2.1]
abbrev clock (θ l k a b:ℝ):F→ℝ:=![ -2*θ,-2*θ,-2*θ,a+b,l+k]
lemma tune_price(i:Fin 5) : Swing (wave i*star basis) 0:=by
 obtain ⟨θ,l,k,a,b,δ,p,G⟩:= Lute.count i; rw [meter i p, portion];
 let f(q:F):=board θ (spiceX q) (spiceY q); let U:= both (zoneC f) (χ (-4*θ) • (1:Op F)); have he:Swing (refit ensemble U) 0:=by
    apply Swing.renameS; have hp: Swing (zoneC f) (∑ q:F,clock θ l k a b q):= Swing.together f _ fun q=>by fin_cases q ; exact peak G; exact peak G; exact peak G; exact amid G; exact west G
    unfold U; have hg: Swing (χ l • (1:Op F)) (5*l):=by simpa [F] using Swing.const (J:=F) l G.left
    have ht:= Swing.left_right hp hg; rw [G.dTen] at ht; convert ht using 1; simp only [F,clock,Fin.sum_univ_succ,Matrix.cons_val_zero, Matrix.cons_val_succ]; norm_num1; linarith [G.sumZ]
 rw [←jump_replicate]; exact (by simpa only [sum_const_zero] using Swing.together (fun _:Fin 3=>refit ensemble U) _ (fun _=>he)) -- tune
lemma disallowed {k:Fin 5}(h:k≠0): basis≠wave k:=by
 obtain ⟨θ,l,d,a,b,δ,p,G⟩:= Lute.count k; intro x; have he:0<k.val:= Nat.pos_of_ne_zero (fun h'=> h (Fin.ext h')); have hv : θ≠0:=by intro h; apply ‹k≠0›; refine Fin.ext (z_prim.pow_inj k.isLt (by decide : 0<5) ?_); rw [Fin.val_zero,pow_zero,←p,h,χ_zero]
 let f(i:F):= board θ (spiceX i) (spiceY i); let U:= both (zoneC f) (χ (-4*θ) • (1:Op F)); have hp:(1:Op (Fin 3))⊗ₖ refit ensemble U=1:= by unfold U f; rw [←Music.portion, ← meter k p,← x]; exact basis_acts.gate.2
 let z:=ensemble (Sum.inl (0,0)); have hy:=Matrix.ext_iff.mpr hp (0,z) (0,z); rw [Matrix.kroneckerMap_apply,Matrix.one_apply_eq, Matrix.one_apply_eq,one_mul] at hy
 have hz:= (phases_val θ).1; have ht: board θ 0 1 0 0= χ (-θ):=by norm_num [-neg_mul, board, Matrix.mul_apply, Two, chip,levy,Matrix.diagonal_apply]; exact hz
 unfold U z at hy; rw [replaces,Equiv.symm_apply_apply] at hy; have hx:χ (-θ)=1:= ht.symm.trans (by exact hy)
 have ht:= coverχ (by rw [abs_neg]; exact G.wing) (by simpa using Real.pi_pos) (hx.trans χ_zero.symm); exact hv (by simpa using ht)
end Music
end YM.CF.BPress.Lute
