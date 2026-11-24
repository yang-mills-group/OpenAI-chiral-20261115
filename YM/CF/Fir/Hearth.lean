import YM.CF.Fir.Marin
import YM.Next.FREE_KERNELS.Heart
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fir
open Function Filter Lattice Laurent Bloch Next.Free Metric Finset Set
open scoped Topology Matrix BigOperators
lemma shell_inv (j:ℕ)(N:Side){p:Momentum}(hp:p∈realCube zone)(hx:p≠0): shell j N p=(1+prodM (mixL j N p) (mixL j N p))⁻¹:=by
  have hh:D N p ≠0:=by intro h; have he:=noGhost N hp hx; rw [h] at he; exact lt_irrefl 0 he
  rw [shell, ← (denom j N p).resolve_right hh, div_eq_mul_inv, mul_inv,mul_inv_cancel_left₀ hh]
lemma kin_period (p:Momentum)(x:Cover): kin (p+reciprocal x)=kin p:=by
  unfold kin; congr 1; apply Finset.sum_congr rfl; intro a _; simp only [pl,Pi.add_apply,reciprocal,mul_comm _ ((x a:ℤ):ℂ),Complex.cos_add_int_mul_two_pi]
lemma sine_period (p:Momentum)(x:Cover): sine (p+reciprocal x)=sine p:=by
  ext a:1; simp only [sine,Pi.add_apply,reciprocal,mul_comm _ ((x a:ℤ):ℂ),Complex.sin_add_int_mul_two_pi]
lemma b_period (p:Momentum)(x:Cover) : bGraph (p+reciprocal x)=bGraph p:=by rw [bGraph,bGraph,gD,gD,rad,rad,mag,mag,sine_period,kin_period]
lemma b_odd (p:Momentum) : bGraph (-p)= -bGraph p:=by
  have hh : kin (-p)=kin p:=by simp [kin,pl]
  have hs:sine (-p)= -sine p:=by ext i:1; simp [sine]
  unfold bGraph gD rad mag; rw [hs, hh]; simp
lemma mix_period (j N)(p:Momentum)(x:Cover): mixL j N (p+reciprocal x)=mixL j N p:=by
  unfold mixL
  convert congr_arg ((N.val:ℂ)⁻¹ • ·) (Equiv.sum_comp (Equiv.addRight (wrap N x)) (fun l=> muff j N (aliasAt p l)^2 • bGraph (aliasAt p l))) using 2
  refine Finset.sum_congr rfl fun l _=>?_; obtain ⟨y,hy⟩:=alias_exchange p l x
  rw [hy,muff_period,b_period]; rfl
lemma mix_neg (j N)(h:Odd N.val)(p:Momentum): mixL j N (-p)= -mixL j N p:=by
  unfold mixL; rw [← Equiv.sum_comp (Equiv.neg (Site N)),← smul_neg, ← sum_neg_distrib]; congr 1; refine sum_congr rfl fun i _=>?_
  simp only [Equiv.neg_apply,alias_reverse _ h,muff_even j N h,b_odd,smul_neg]
lemma mix_jump (j:ℕ)(L M:Side)(h:Odd L.val)(e:Odd M.val)(p:Momentum): mixL j (L*M) p=(L.val:ℂ)⁻¹ • ∑ l : Site L, muff j L (aliasAt p l)^2 • mixL j M (aliasAt p l):=by
  have hh l r : M.val • aliasAt (aliasAt p (l:Site L)) (r:Site M)=aliasAt p l+reciprocal (lift r):=alias_scale ..
  rw [mixL,mul_side_complex, mul_inv, ← smul_smul,← Equiv.sum_comp (radices h e),Fintype.sum_prod_type]; congr 1; rw [Finset.smul_sum]; refine sum_congr rfl fun l _=>?_
  rw [mixL]; simp_rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun r _=>?_
  rw [← alias_refine, muff_join _ _ _ h e,hh,muff_period]; module
lemma mass_ne (j:ℕ)(N:Side)(h:Odd N.val){p:Momentum}(hp:p∈realCube zone): mass j N p≠0:=by
  by_cases he:p=0
  · simp [he]
  intro he'; have hh:= (noGhost N hp he).trans_le (mass_price j N h hp he); rw [he'] at hh; exact lt_irrefl 0 hh
@[simp] lemma shell_origin (j N): shell j N 0=0:=by simp [shell,D,gD,rad,mag,kin,pl,sine,narrow]
@[simp] lemma skin_origin (j N): skin j N 0=0:=by simp [skin,D,gD,rad,mag,kin,pl,sine,narrow,ds, show sine (0:Momentum)=0 from (funext fun i => by simp [sine])]
lemma skin_mix (j N){p:Momentum}(hp:p∈realCube zone): skin j N p=shell j N p • mixL j N p:=by
  by_cases h:p=0
  · simp [h]
  exact (skin_def ..).resolve_right fun he=> (lt_irrefl 0 ((congr_arg Complex.re he) ▸ noGhost N hp h))
lemma shell_overlap (j N): Overlaps zone (shell j N):=by
  intro p hp x hx; by_cases h:x=0
  · simp [h, show reciprocal (0:Cover)=0 by ext; simp [reciprocal]]
  obtain ⟨he,hg⟩:= overlap_regular h hp hx
  rw [shell_inv _ _ hx hg,shell_inv _ _ hp he,mix_period]
lemma skin_overlap (j N) (a:Axis): Overlaps zone fun p=> skin j N p a:=by
  intro p hp x hx; dsimp only; rw [skin_mix _ _ hx,skin_mix _ _ hp,mix_period,shell_overlap _ _ _ hp x hx]
end YM.CF.Fir
