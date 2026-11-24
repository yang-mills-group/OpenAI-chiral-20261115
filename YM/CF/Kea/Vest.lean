import YM.CF.Kea.Sill
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Kea
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill SU Rush Tulip Cube
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker Branch Tenant
attribute [local instance] opCStarAlgebra
variable {N:Side}
def newm (d:Candle)(z:Cover)(l:Slot):ℂ:=mode (tmap (rise d l)) z
lemma keen (d:Candle)(z:Cover)(k:Site N)(o:Lattice.Order): (Tulip.track (profile (tax d)) (node k) (leap z o)).1=Matrix.diagonal (newm d z):=by
 rw [track_pr]; change (matter _).val= _; rw [travD]; unfold leap; simp only [route_end]; congr 1; funext i; unfold newm; rw [←mode_scale]; rw [two_smul]; congr 1; funext a; exact (Complex.ofReal_add ..).symm
lemma due(d:Candle)(z:Cover)(l:Slot): ‖newm d z l‖=1:=mode_real _ _ (tmap_physical _)
lemma slider_d (d:Candle)(z:Cover)(o:Lattice.Order)(b a:SpinIdx)(c:ℂ)(x y:Site N)(i j:SpinIdx)(l l':Slot): slider N z o b a c (profile (tax d)) ((x,i),l) ((y,j),l')=if i=b ∧ y=x+wrap N z∧ j=a∧ l=l' then wind x z*c*newm d z l else 0:=by
 simp only [slider, Matrix.sum_apply]; rw [Finset.sum_eq_single x]
 · simp only [Tulip.panel,Matrix.of_apply,Prod.mk.injEq,keen,Matrix.smul_apply,smul_eq_mul, Matrix.diagonal_apply]; by_cases h:i=b <;> by_cases g:y=x+wrap N z <;> simp [h,g]; grind
 · intro i _ h; simp [Tulip.panel,Ne.symm h]
 simp
lemma slider_s(d:Candle)(f:Cover→Op SpinIdx)(p b a) (h: Summable (fun z=>‖f z b a‖)): Summable fun n:ℕ=> slider N (Tulip.names n) p b a (f (Tulip.names n) b a) (profile (tax d)):=by
 apply Branch.kernel_sum; intro ⟨⟨x,i⟩,l⟩ ⟨⟨y,j⟩,t⟩; simp only [slider_d]; apply Summable.of_norm; apply Summable.of_nonneg_of_le _ _ (h.comp_injective Tulip.names.injective); intro; apply norm_nonneg
 intro n; split <;> simp [due,Rush.wind,Rush.fee_norm]
lemma tour_at (d:Candle)(f:Cover→Op SpinIdx)(h:∀ b a,Summable (fun z=>‖f z b a‖))(p:Lattice.Order)(i j:Single N): tourP N f p (profile (tax d)) i j= if i.2=j.2 then ∑' z, newm d z i.2 * wagon N f z i.1 j.1 else 0:=by
 obtain ⟨⟨x,i⟩,l⟩:=i; obtain ⟨⟨y,b⟩,k⟩:=j; simp only [tourP,Matrix.sum_apply]; simp_rw [Branch.kernel_entry (slider_s _ _ _ _ _ (h _ _)),slider_d]; rw [Finset.sum_eq_single i]
 swap; · intro a _ h; simp [Ne.symm h]
 swap; · simp
 rw [Finset.sum_eq_single b]; swap; · intro a _ h; simp [Ne.symm h]
 swap; · simp
 by_cases e:l=k; swap; · simp [e]
 subst k; simp only [and_self,eq_self,ite_true,and_true,true_and,wagon_app]; rw [← Tulip.names.tsum_eq (f:=fun z:Cover=> newm d z l * (if x+wrap N z=y then wind x z*f z i b else 0))]; apply tsum_congr; intro n; split_ifs <;> simp_all <;> ring
lemma further{d:Candle}(S: Slide N d)(x y: Site N)(l:Slot)(z:Cover): newm d z l*(wind x z * Fourier N (x+wrap N z) y)= Fourier N x y*mode (tmap (angle S (y,l))) z:=by
 rw [←wage (peer_p S (y,l)) z]; rw [show tmap (_+_)=mel y+tmap (rise d l) by ext i:1; exact Complex.ofReal_add ..,mode_phase]; unfold newm; simp only [Fourier,Matrix.of_apply]; rw [← mul_div_assoc (wind x z),freq_advance]; ring
lemma tour_e{d:Candle}(S:Slide N d)(g:Even N.val)(f:Cover→Op SpinIdx)(P:Momentum→Op SpinIdx)(h:Reads f P)(o:Lattice.Order): tourP N f o (profile (tax d))=Dofu N (fun k=>P (tmap (angle S k))):=by
 apply vind; ext ⟨⟨x,b⟩,l⟩ ⟨⟨y,j⟩,L⟩; rw [wool, Matrix.mul_apply]
 simp_rw [tour_at d f h.sumK o,coil]; simp only [Single,Fintype.sum_prod_type]; rw [sum_comm]
 by_cases e:l=L; swap
 · rw [if_neg (show l≠L from e),sum_eq_zero]; intro c _; apply sum_eq_zero; intro i _; apply sum_eq_zero; intro l h; apply sum_eq_zero; intro i _; split_ifs <;> grind
 subst L; let p:= tmap (angle S (y,l)); have hp: p∈baseCube:= b_base (up_p _ g _); simp only [ite_true]
 rw [sum_eq_single j]; swap; · intro a _ h; simp only [h,false_and,ite_false,mul_zero,sum_const_zero]
 swap; · simp only [mem_univ,not_true_eq_false,IsEmpty.forall_iff]
 simp only [true_and]
 let R(i:Site N)(u:Slot):ℂ:=(if l=u then ∑' z,newm d z l*wagon N f z (x,b) (i,j) else 0)*(if u=l then Fourier N i y else 0)
 change ∑ i, (∑ u:Fin 3,∑ z:Sheet,R i (u,z))=Fourier N x y* P p b j
 have he i: ∑ u:Slot,R i u=(∑' z,newm d z l*wagon N f z (x,b) (i,j))*Fourier N i y:=by rw [sum_eq_single l]; simp only [R,ite_true]; intro b _ h; unfold R; simp only [Ne.symm h,h,ite_false,mul_zero]; simp
 rw [sum_congr rfl (fun k _=> (Fintype.sum_prod_type (R k)).symm)] -- tune
 simp_rw [he,← tsum_mul_right]; have hg(i:Site N):Summable (fun z=>newm d z l*wagon N f z (x,b) (i,j)):=by
    apply Summable.of_norm; simp_rw [norm_mul,due,one_mul]; exact (wagon_sum h (x,b) (i,j)).norm
 rw [← Summable.tsum_finsetSum (fun i _=> (hg i).mul_right _), ← h.readK p hp b j]; unfold Laurent.read; rw [← tsum_mul_left]; apply tsum_congr; intro z
 rw [sum_eq_single (x+wrap N z)]; swap; · intro i _ h; simp only [wagon_app,Ne.symm h,ite_false,mul_zero,zero_mul]
 swap; · simp
 rw [wagon_app,if_pos rfl]; change _= Fourier N x y*(mode p z*f z b j); have he:= further S x y l z; unfold p; linear_combination (f z b j)*he
end YM.CF.Kea
