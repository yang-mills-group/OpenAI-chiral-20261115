import YM.SU5.FiniteGaugeData.Largo.Track
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option maxHeartbeats 320000
noncomputable section
namespace YM.CF.Window.Largo
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
abbrev Stereo (N:Side):= Tang → Per N
abbrev Mini (N:Side):= Site N×SpinIdx
variable {N:Side}
abbrev debut (v:Stereo N) (i:Per N) (k:SpinIdx): Mini N:= (full v i,k)
lemma back_home {X:Type*}(p:Tang→X) (i:X): back (full p i)=p:= funext (fun j=> full_before p i j)
lemma sale_full {X:Type*}(p q:Tang→X)(i j:X): full p i=full q j ↔ p=q ∧ i=j:=by
 constructor; · intro h; exact Prod.mk.inj (meet.injective h)
 intro h; rw [h.1,h.2]
lemma offering {Y:Type*} [AddCommMonoid Y](f: Site N→Y): (∑ i,f i)=∑ (j: Stereo N), ∑ (k:Per N),f (full j k):=by rw [← Equiv.sum_comp meet f,Fintype.sum_prod_type]; rfl -- transparency
lemma debut_cases {p:Mini N→Prop}(h:∀ v i k,p (debut v i k)):∀ i,p i:=by rintro ⟨x,i⟩; rw [←full_back x]; exact h _ _ _
lemma mini_offer {Y:Type*}[AddCommMonoid Y](f: Mini N→ Y): (∑ i,f i)=∑ (j:Stereo N), ∑ (k:Per N), ∑ (h:SpinIdx),f (debut j k h):=by rw [Fintype.sum_prod_type,offering] -- tune
abbrev badge (q:Stereo N): Rim:= fun i => Lat.principal (q i)
lemma aliquotMel (p:Stereo N)(k:Per N): mel (full p k)=floorPin (badge p) (Lat.principal k):=by funext i; fin_cases i <;> rfl
abbrev phaseL (k x:Per N) := BZ.phase (Lat.principal k) ^ x.val
def traced (k x:Stereo N):ℂ:= ∏ i:Tang,phaseL (k i) (x i)
lemma frequencyL (q p:Stereo N)(x k:Per N): frequency (full p k) (full q x)= traced p q * phaseL k x:=by rw [frequency, foldBigP]; unfold pm; simp only [Function.comp_apply, full_before, full_last]; rfl
lemma phaseL_one(k x: Per N): phaseL k x*star (phaseL k x)=1:=by unfold phaseL; rw [star_pow,←mul_pow,BZ.phase_one,one_pow]
lemma traced_one(k x:Stereo N): traced k x* star (traced k x)=1:=by unfold traced; rw [star_prod,←prod_mul_distrib]; exact prod_eq_one fun i _=>phaseL_one ..
lemma stereo_card : Fintype.card (Stereo N)=N.val^3:=by unfold Stereo Per; rw [Fintype.card_pi_const,ZMod.card]
lemma chronos_t (x y:Per N) : ∑ k:Per N, phaseL k x*star (phaseL k y)= if x=y then (N.val:ℂ) else 0:=by
 let z : Stereo N:=0; have he := (show Fourier N*star (Fourier N) = 1 from (fourier_mem N).2); have hh:= congr_fun (congr_fun he (full z x)) (full z y); rw [Matrix.mul_apply,offering] at hh; -- tune order
 unfold Fourier at hh; simp only [Matrix.star_apply,Matrix.of_apply,Matrix.one_apply] at hh; simp_rw [frequencyL,star_div₀,star_mul,show star (normF N)=normF N from (by simp [normF]),div_mul_div_comm] at hh;  
 have hp : ∀ k u:Stereo N, ∀ i:Per N,traced k u * phaseL i x * (star (phaseL i y)*star (traced k u))=phaseL i x*star (phaseL i y) := by intro k u y; calc
            _ = traced k u*star (traced k u)*(phaseL y x*star (phaseL y _)):=by ring
            _ =_ := by rw [traced_one,one_mul]
 simp_rw [hp] at hh
 rw [sum_const,card_univ,nsmul_eq_mul,stereo_card] at hh; push_cast at hh; simp_rw [sale_full,true_and,←Finset.sum_div] at hh
 by_cases h:x=y <;> simp only [h, ↓reduceIte] at hh ⊢ <;> unfold normF at hh <;> (have he:(N.val:ℂ)≠0:=by exact_mod_cast N.property.ne');
 · field_simp at hh; linear_combination hh -- tune.
 field_simp at hh; simpa using hh -- tune
abbrev heightF (N:Side): ℂ:=(Real.sqrt N.val:ℝ)
lemma heightReal : star (heightF N)=heightF N:=by unfold heightF; simp
lemma heightSq : heightF N * heightF N=N.val:=by unfold heightF; exact_mod_cast Real.mul_self_sqrt (nPos N).le
lemma heightF_ne : heightF N≠0:=by unfold heightF; exact_mod_cast (Real.sqrt_pos.2 (nPos N)).ne'
private lemma nextL (x y:Per N): (∑ i:Per N,phaseL i x/heightF N * star (phaseL i y/heightF N))= if x=y then 1 else 0:=by
 simp_rw [star_div₀,heightReal,div_mul_div_comm,←Finset.sum_div,chronos_t]; split_ifs with h; · rw [heightSq,div_self]; exact_mod_cast N.property.ne'
 rw [zero_div]
private def χ (i:Side): Op (Mini i):= Matrix.of fun j k=> if back j.1=back k.1 ∧ j.2=k.2 then phaseL (k.1 3) (j.1 3) /heightF i else 0
private lemma Χ_debut (p q:Stereo N)(x y:Per N)(i j:SpinIdx): χ N (debut p x i) (debut q y j)=if p=q ∧ i=j then phaseL y x/heightF N else 0 := by unfold χ; simp only [debut,Matrix.of_apply,back_home,full_last] -- rhs _ error
private lemma chronologicalT : χ N∈unitary (Op (Mini N)):=by
 apply Matrix.mem_unitaryGroup_iff.mpr; apply Matrix.ext _; -- tune
 intro i; revert i; apply debut_cases; intro v i k x; revert x; apply debut_cases; intro y t j; rw [Matrix.mul_apply,mini_offer]; simp_rw [Χ_debut,Matrix.star_apply,Χ_debut]; rw [Matrix.one_apply]; change _= if (full v i,k)=(full y t,j) then _ else _
 by_cases h:v=y; swap
 · rw [if_neg (by simp [sale_full,h])]; refine sum_eq_zero fun i _=>?_ ; by_cases t:v=i; · subst i; simp [Ne.symm h]
   simp [t]
 subst y; by_cases h:k=j; swap
 · rw [if_neg (by simp [h])]; refine sum_eq_zero fun l _=> sum_eq_zero fun i _=> sum_eq_zero fun j' _=>?_ ; by_cases t:k=j'; · subst j'; simp [Ne.symm h]
   simp [t]
 subst j; rw [sum_eq_single v]
 · simp only [true_and,apply_ite star,star_zero,ite_mul, mul_ite,mul_zero,zero_mul,ite_self,ite_true]; simp only [ite_self, Finset.sum_ite_eq', mem_univ, ↓reduceIte, Finset.sum_ite_eq]; rw [nextL]; simp [sale_full] -- tune
 · intro b _ h'; simp [Ne.symm h']
 simp
def Chrono (N:Side): UNI (Mini N):= ⟨χ N,chronologicalT⟩
-- spin linear: U⁻¹ plates =... L.
def Cane (N:Side): UNI (Mini N):= overU N SpinIdx*star (Chrono N)
lemma properT (p q:Stereo N)(x y:Per N)(i j:SpinIdx): (Chrono N).val (debut p x i) (debut q y j)=if p=q∧i=j then phaseL y x/heightF N else 0:=Χ_debut ..
lemma alf (V:Momentum→Op SpinIdx): E₁ V N= twist (Cane N) (twist (Chrono N) (mark N V)):=by
 unfold E₁ plates; rw [twist_formula,twist_formula,twist_formula]; unfold Cane; -- simp? noncomm cancel
 let T:=(Chrono N).val; let Y:=(overU N SpinIdx).val; let f:=mark N V; change Y*f*star Y=Y*star T*(T*f*star T)*star (Y*star T); have ht:star T*T=1:=(Chrono N).property.1
 simp only [star_mul,star_star]; simp_rw [mul_assoc]; rw [←mul_assoc (star T) T,←mul_assoc (star T) T,ht,one_mul,one_mul]
lemma Cane_zero (h k: Mini N)(v:¬(h.1 3=k.1 3 ∧ h.2=k.2)): (Cane N).val h k=0:=by
 revert h k; apply debut_cases; intro x i y k; revert k; apply debut_cases; intro p o j v; unfold Cane; change ((overU N SpinIdx).val * star (Chrono N).val) _ _=0; rw [Matrix.mul_apply,mini_offer, sum_eq_single p]; -- Cane_zero: expand full
 · simp_rw [Matrix.star_apply,properT,overU,Fourier,Matrix.kroneckerMap_apply]; simp only [debut] at * -- unfold debut early? simplify
   simp_rw [Matrix.of_apply,frequencyL]; simp only [Matrix.one_apply,mul_ite,mul_zero,mul_one, true_and, apply_ite star,star_zero,ite_mul,zero_mul,full_last] at *
   by_cases h:y=j; swap
   · refine sum_eq_zero fun i _=>sum_eq_zero fun t _=>?_ ; by_cases b:t=y; · subst t; simp [Ne.symm h]
     simp [Ne.symm b]
   subst j; simp only [true_and,and_true,ite_self,ite_true] at * -- h gone after subst
   simp only [ite_mul,mul_ite,mul_zero,zero_mul,ite_self,ite_true,Finset.sum_ite_eq', Finset.sum_ite_eq,mem_univ, ↓reduceIte, star_div₀]
   rw [sum_congr rfl (g:=fun b:Per N=> (traced p x/(normF N*star (heightF N)))*(phaseL b i*star (phaseL b o))) (fun i _=> by ring),← mul_sum, chronos_t, if_neg v,mul_zero]
 · intro b _ h'; simp [Matrix.star_apply,properT,Ne.symm h']
 simp
end YM.CF.Window.Largo
