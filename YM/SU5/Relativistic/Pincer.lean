import YM.SU5.Relativistic.Rothy
import YM.SU5.Relativistic.Rust
/-!
 *Clean* X times arbitrary site letter; importantly X_late-X_uniform small even on sites,
 for unbounded Neumann steps, on this TILTING lattice.
-/
set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
namespace YM.CF.Papyrus.Franc
open Function Set Filter NormedSpace Fock Finset Lattice Laurent Bloch Lat BPress.Spin.Blank Cube Rush SU Fir Ember Scroll Tulip Fixed.Extensive Dial Tenant
open Crest.Sleet
open scoped Topology Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator BigOperators ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
variable {N:Side}{M:Tulip.Male}{j k:ℕ}
local notation "R" => spar j M (1:Bkg (More N))
local notation "A" => angle true
local notation "F" => bent true j M.val
local notation "Z" => zTar j M
lemma fz_w{I:Type*}[LinearOrder I][Fintype I] {P B:Op I}{z:ℝ}(p:IsStarProjection P)(b:IsStarProjection B)(u:B*P*B=z • B)(ht:0<z)(g:z≤1) : let C:=(1-P)*B*P; C*(1-P*B*P)=(1-z:ℝ) • C ∧ ‖C‖ ≤ Real.sqrt z:=by
 intro C; have he:C*(1-P*B*P)=C - z • C:= by
    rw [mul_sub C,mul_one]; congr 1
    calc
      _=(1-P)*B*(P*P)*B*P:=by unfold C; noncomm_ring
      _= (1-P)*(B*P*B)*P:=by rw [p.isIdempotentElem.eq]; simp [mul_assoc]
      _=_:=by rw [u,Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
 rw [he]; refine ⟨(by rw [sub_smul,one_smul]),?_⟩
 have hv : ‖B*P‖ * ‖B*P‖ ≤ z:=by
    let a:=star (B*P); nth_rw 1 2 [←norm_star (B*P)]; change ‖a‖*‖a‖≤_
    rw [← CStarRing.norm_star_mul_self,show star a*a=B*P*B from (by unfold a; rw [star_star,star_mul,p.isSelfAdjoint,b.isSelfAdjoint, ←mul_assoc, mul_assoc B, p.isIdempotentElem.eq]),u,norm_smul, Real.norm_of_nonneg ht.le]; exact mul_le_of_le_one_right ht.le (b.norm_le _)
 have hh:‖B*P‖≤ Real.sqrt z:= by nlinarith only [Real.sq_sqrt ht.le,norm_nonneg (B*P),Real.sqrt_pos.mpr ht,hv]
 unfold C; rw [mul_assoc]; exact (norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) (p.one_sub.norm_le _)).trans hh)
private def windC(k:ℕ)(z:ℝ):= (1-(1-z)^k)/z
lemma angled (h:1≤j)(p:IsStarProjection R)(i:Site N) (k:ℕ) :
    Comb A (F (mel i)) k= windC k (Z i) • ((1-F (mel i))*A*F (mel i)):=by
 let P:=F (mel i); let C:= (1-P)*A*P; let z:=Z i; obtain ⟨a,b⟩:=fz_w (f_native h p i) strip_ge (cube_law N true j M i) (amp j h _ i) (z_cap h p i)
 have hx:0<z:=amp j h M i; change Comb A P k=windC k z • C
 induction k with
 | zero=> simp [windC,Comb]
 | succ k ih=>
   rw [Comb,ih,Algebra.smul_mul_assoc,(show C*(1-P*A*P)=(1-z) • C from a),smul_smul]; nth_rw 1 [show (1-P)*A*P= (1:ℝ) • C from (one_smul ℝ _).symm]; rw [←add_smul]; congr 1; unfold windC; field_simp <;> ring -- uses pow_succ
lemma zGain (h:1≤j)(p:IsStarProjection R)(i:Site N) (k:ℕ): ‖Comb A (F (mel i)) k‖ ≤ (Real.sqrt (Z i))⁻¹:=by
 let P:=F (mel i); let C:= (1-P)*A*P; let z:=Z i; have a:0<z:=amp j h M i; have v:=z_cap h p i; let d:=windC k z; have he:(1-z)^k≤1:= pow_le_one₀ (sub_nonneg.mpr v) (by linarith); have hd:0≤d:=div_nonneg (sub_nonneg.mpr he) a.le
 let t:=Real.sqrt z; have ht:0<t:=Real.sqrt_pos.mpr a
 rw [angled h p i k,norm_smul,Real.norm_of_nonneg hd]; apply (mul_le_mul_of_nonneg_left (fz_w (f_native h p i) strip_ge (cube_law N true j M i) a v).2 hd).trans
 apply le_trans (mul_le_mul_of_nonneg_right (show windC k z≤ z⁻¹ from (div_le_iff₀ a).mpr (by rw [inv_mul_cancel₀ a.ne']; exact sub_le_self _ (pow_nonneg (by linarith [show z≤1 from v]) _))) ht.le) (le_of_eq ?_); change z⁻¹*t=t⁻¹; nth_rw 1 [←(show t^2=z from Real.sq_sqrt a.le)]; field_simp
lemma zGap (h:1≤j)(p:IsStarProjection R)(i:Site N) (k v:ℕ)(t:k ≤ v): ‖Comb A (F (mel i)) v-Comb A (F (mel i)) k‖ ≤ (1-Z i)^k*(Real.sqrt (Z i))⁻¹:=by
 let P:=F (mel i); let C:= (1-P)*A*P; let z:=Z i; have a:0<z:=amp j h M i; have l:z≤1:=z_cap h p i; let d:=windC v z-windC k z; let r:=Real.sqrt z; have hp:0<r:=Real.sqrt_pos.mpr a
 have he: (1-z)^v≤(1-z)^k:= pow_le_pow_of_le_one (by linarith only [l]) (by linarith) t
 have hx:d=((1-z)^k-(1-z)^v)/z:=by unfold d windC; ring
 have hf:0≤d:= hx ▸ div_nonneg (sub_nonneg.mpr he) a.le
 rw [angled h p i k,angled h p i v,←sub_smul,norm_smul,Real.norm_of_nonneg hf]; apply (mul_le_mul_of_nonneg_left (fz_w (f_native h p i) strip_ge (cube_law N true j M i) a l).2 hf).trans
 refine (mul_le_mul_of_nonneg_right (show d ≤ (1-z)^k/z from hx ▸ div_le_div_of_nonneg_right (sub_le_self _ (pow_nonneg (by linarith) _)) a.le) hp.le).trans_eq ?_
 change (1-z)^k/z*r=(1-z)^k*r⁻¹; field_simp; rw [←(show r^2=z from Real.sq_sqrt a.le)]; ring -- fragile
section
variable (B: Momentum →Op SpinIdx) (x:Site N)(s:Slot) (f:Site N→Ket SpinIdx)
local notation "U" => ear N
lemma booth_D : lens B N=twist U (scalarP (Rush.mark N B)):=by
 rw [BPress.Spin.Blank.lens,plates,twist_formula,twist_formula]; rw [show (ear N).val= (overU N SpinIdx).val ⊗ₖ 1 from rfl,op_star_kron,star_one]; unfold scalarP; rw [op_kron_mul,op_kron_mul,one_mul,mul_one] -- tune
lemma fingers : acts (scalarP (Rush.mark N B)) (shellV N s f)=shellV N s (fun i=>acts (B (mel i)) (f i)):=by
 apply PiLp.ext; rintro ⟨⟨i,b⟩,t⟩; unfold scalarP; rw [act_at]; unfold Matrix.mulVec dotProduct Single; rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
 unfold shellV Rush.mark; simp only [Matrix.kronecker_apply,jump_apply,Equiv.refl_apply,Matrix.one_apply,WithLp.ofLp_toLp, mul_ite,mul_zero,ite_mul, zero_mul]; rw [sum_eq_single i];
 · simp only [ite_true, Finset.sum_ite_eq,pow_one,true_and]; by_cases v:t=s
   · rw [if_pos v]; rw [act_at]; unfold Matrix.mulVec dotProduct; rw [mul_sum]; apply Finset.sum_congr rfl; intro j _; simp [v]; ring
   rw [if_neg v]; apply sum_eq_zero; intro j _; simp [v]
 · intro j _ p; simp [Ne.symm p]
 simp
lemma shell_norm : ‖shellV N s f‖^2=(((N.val:ℝ)^4)⁻¹*∑ x,‖f x‖^2):=by
 rw [EuclideanSpace.norm_sq_eq,mul_sum]; unfold shellV Single
 rw [Fintype.sum_prod_type,Fintype.sum_prod_type]; apply sum_congr rfl; intro i _; rw [EuclideanSpace.norm_sq_eq, mul_sum]; apply sum_congr rfl; intro u _; rw [sum_eq_single s]; · simp [normF]; ring
 · intro _ _ p; simp [p]
 simp
lemma unitVar (k:SpinIdx) : acts (star (ear N).val) (basisKet ((x,k),s))=shellV N s (fun i=>star (frequency i x) • basisKet k):=by
 apply PiLp.ext; rintro ⟨⟨t,p⟩,j⟩; rw [←show ∀ (x:Ket (Single N)) j,x.ofLp j=x j from fun _ _=>rfl,over_basis]; unfold shellV; by_cases q:p=k <;> by_cases v:j=s <;> simp [q,eq_comm,v, mul_comm,div_eq_mul_inv,WithLp.ofLp_smul,basis_apply] <;> (intro h; exact False.elim (q h.symm))
lemma spice (i:SpinIdx) : ‖acts (lens B N) (basisKet ((x,i),s))‖^2 = ((N.val:ℝ)^4)⁻¹ * ∑ y:Site N, ‖acts (B (mel y)) (basisKet i)‖^2:=by
 rw [booth_D B,twist_formula,act_mul,act_mul,unitVar,act_unit_norm, fingers, shell_norm]; congr 1; apply sum_congr rfl; intro j _; rw [map_smul,norm_smul,norm_star,show ‖frequency j x‖=1 from ?_,one_mul]; rw [←freq_mode]; exact mode_real _ _ (mel_h _).1
end
lemma angledK (h:1≤j)(k:ℕ): Comb (tickA N) R k=lens (fun y=>Comb A (F y) k) N:=by rw [←t_comp,t_lamp,show R=lens F N from nativeP N true j M h,l_rec] -- notation fix
private abbrev glitz {I:Type*}[LinearOrder I][Fintype I](b:Bool)(P:Op I):Op I:=if b then star P else P
private lemma hoe (C:ℝ) (Q:Momentum→Op SpinIdx)(b:Bool)(t:∑ i:Site N, ‖Q (mel i)‖^2 ≤ C*N.val^4)(i:Single N): ‖acts (glitz b (lens Q N)) (basisKet i)‖^2 ≤ C:=by
 obtain ⟨⟨x,i⟩,j⟩:=i; let G(p:Momentum):=glitz b (Q p); have hh(y):‖G y‖= ‖Q y‖:=by unfold G glitz; cases b; rfl; exact norm_star _
 rw [show glitz b (lens Q N)= lens G N from ?_]; swap; · cases b; rfl; exact l_star _
 rw [spice]; apply (mul_le_mul_of_nonneg_left (le_trans (sum_le_sum (g:=fun i=> ‖Q (mel i)‖^2) (fun i h=>?_)) t) (by positivity)).trans_eq (by field_simp [nPos N|>.ne'])
 apply pow_le_pow_left₀ (norm_nonneg _); rw [←hh]; apply (ContinuousLinearMap.le_opNorm _ _).trans; unfold acts; rw [Matrix.l2_opNorm_toEuclideanCLM]; simp [basisKet]
lemma columnC (j:ℕ)(h:1≤j) : ∃ C:ℝ, 0 < C∧ ∀ (N:Side)(M:Tulip.Male),IsStarProjection (spar j M (1:Bkg (More N)))→∀ (k:ℕ) (i:Single N),let X:=Comb (tickA N) (spar j M (1:Bkg (More N))) k; ‖acts X (basisKet i)‖≤ C ∧ ‖acts (star X) (basisKet i)‖≤C:=by
 obtain ⟨C,a,p⟩:= bills j h; refine ⟨Real.sqrt C, Real.sqrt_pos.mpr a,fun N M g k i=>?_⟩; intro X; let P:=spar j M (1:Bkg (More N)); let G:=fun y=>Comb A (bent true j M.val y) k
 have hX:X=lens G N:=angledK h _
 have he: ∑ i:Site N, ‖G (mel i)‖^2≤ C*N.val^4:=by
    apply (p N M).trans'; apply sum_le_sum; intro i _; let z:=zTar j M i; let r:=Real.sqrt z; have hp:0<r:=Real.sqrt_pos.mpr (amp j h _ _); have hh:r≤1:= (Real.sqrt_le_sqrt (z_cap h g i)).trans_eq Real.sqrt_one
    apply (pow_le_pow_left₀ (norm_nonneg _) (zGain h g i k) _).trans; unfold hard; rw [inv_pow]; exact inv_anti₀ (pow_pos hp _) (pow_le_pow_of_le_one hp.le hh (by decide)) -- orientation check
 exact ⟨Real.le_sqrt_of_sq_le (hX.symm ▸ hoe C G false he i), Real.le_sqrt_of_sq_le (hX.symm ▸ hoe C G true he i)⟩
lemma net_c (j:ℕ)(h:1≤j)(ε:ℝ)(p:0<ε) : ∀ᶠ k:ℕ in atTop,∀ (N:Side)(M:Tulip.Male),IsStarProjection (spar j M (1:Bkg (More N)))→∀ (v:ℕ),k ≤ v →∀ (i: Single N),let X:=Comb (tickA N) (spar j M (1:Bkg (More N))); ‖acts (X v-X k) (basisKet i)‖ ≤ ε ∧ ‖acts (star (X v-X k)) (basisKet i)‖ ≤ ε:=by
 obtain ⟨C,t,u⟩:=bills j h; let q:=ε^2/C; have hh:0<q:=by unfold q; positivity
 filter_upwards [stintE q hh] with k r N M p' v a i; intro X; let G(p:Momentum):=Comb A (bent true j M.val p) v-Comb A (bent true j M.val p) k
 have hx:X v-X k=lens G N:=by unfold X; rw [angledK h,angledK h,l_sub]
 have he: ∑ i:Site N, ‖G (mel i)‖^2 ≤ ε^2 * N.val^4:=by
    apply (sum_le_sum (g:=fun i=> q*(hard (zTar j M i))⁻¹) (fun i h'=>?_)).trans (le_trans (show _≤q*(C*N.val^4) by rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (u N M) hh.le) (le_of_eq (by unfold q; field_simp)))
    let z:=zTar j M i; let W:= Real.sqrt z; let d:=(1-z)^k; have ht:0<z:=amp j h _ i; have hv:=z_cap h p' i
    have hd:0≤d:=pow_nonneg (sub_nonneg.mpr hv) _; have hy:d≤1:=pow_le_one₀ (sub_nonneg.mpr hv) (by linarith)
    have hl:d*W ≤ q:=r z ht hv; have hh:0<W:=Real.sqrt_pos.mpr ht
    apply (pow_le_pow_left₀ (norm_nonneg _) (zGap h p' i k v a) _).trans; change (d*W⁻¹)^2 ≤ q*(W^3)⁻¹; field_simp; nlinarith only [mul_le_mul_of_nonneg_right hy (show 0≤d*W by positivity),hl]
 exact ⟨le_of_pow_le_pow_left₀ (by decide) p.le (hx.symm ▸ hoe _ _ false he i), le_of_pow_le_pow_left₀ (by decide) p.le (hx.symm ▸ hoe _ _ true he i)⟩
end YM.CF.Papyrus.Franc
