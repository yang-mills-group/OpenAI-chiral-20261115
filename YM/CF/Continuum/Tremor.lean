import YM.CF.Continuum.GraspPolar
import YM.CF.Continuum.Flags
import YM.CF.Continuum.Conditional
import YM.CF.Emu.Fern

/-! # At flat tilt the undecorated color-traced component includes the shift
    in the Wilson-band projection, via near-singular pole. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Tulip Phase
open Laurent Next.Free Bloch Fir Ember Jill Kea Sods Flare Emu Onyx Dial Graph
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 8192
variable {L' B N m:Side}{j:ℕ}{P:Op (Single N)}

def lesser (g:Fin 3) : Family := (g,false)
def selected (N:Side)(a:Family) := (univ:Finset (Site N)) ×ˢ colors a
lemma selected_size (g:Fin 3)(N:Side): (selected N (lesser g)).card=N.val^4*5:=by rw [selected,card_product, colors_card,card_univ,Lattice.site_card]; rfl
lemma topIn (g:Fin 3)(N:Side) : tinyMode N g ∈ selected N (lesser g) := by simp [selected,colors,tinyMode,topColor,family,lesser]

def bias (g:Fin 3)(M:Jill.Male)(j:ℕ)(N:Side): Op SpinIdx:= ((N.val:ℂ)^4)⁻¹ • ∑ i∈selected N (lesser g), tiltCharge N j M i
lemma biasMoney(g:Fin 3)(M:Jill.Male)(p:1≤j)(h:Even N.val)(x:SpinIdx)(a b:SpinIdx)(ha:a∈plusHalf)(hb:b∉plusHalf) : bias g M j N a x = 0 ∧ bias g M j N x b=0:=by
  have he(i:Stag N): tiltCharge N j M i a x=0 ∧ tiltCharge N j M i x b=0:=by
    obtain ⟨t,u⟩:=polarSector (crestQ j M (needlesView N) h i).2.2.1 (tiltGap M p h); let Q:= tiltCharge N j M i; change Aop*Q=0 at t; change Q*Aop=Q at u; have hl:= Matrix.ext_iff.mpr t a x; have hz:= Matrix.ext_iff.mpr u x b; rw [Adef,←raising,cutM, Matrix.diagonal_mul,if_pos ha,one_mul] at hl; rw [Adef,←raising,cutM,Matrix.mul_diagonal,if_neg hb,mul_zero] at hz; exact ⟨hl,hz.symm⟩
  unfold bias; simp [Matrix.sum_apply, (fun i=>(he i).1),fun i=>(he i).2]
lemma charge_zero {g:Fin 3}{k:Stag N} (h:k∈ (selected N (lesser g)).erase (tinyMode N g)): k≠tinyMode N k.2.1:=by
  have he:= (mem_erase.mp h).1; obtain ⟨a,b⟩:= k; have hb:b∈colors (lesser g):= (mem_product.mp (mem_erase.mp h).2).2; have hp:b.1=g:=(Prod.mk.inj (mem_filter.mp hb).2).1; simpa only [hp] using he

section scale
lemma growsTilt(j:ℕ)(h:1≤j):∃ (c C:ℝ),0<c ∧ 0 < C ∧ ∃ k:ℕ,∀ N:Side,k≤N.val→Even N.val→∀ g:Fin 3,∀ M:Jill.Male, c*N.val^5 ≤ ‖bias g M j N‖ ∧ ‖bias g M j N‖≤ C*N.val^9:=by
  obtain ⟨c,C,p,hC,X⟩:= tiltPulse j h; obtain ⟨k,hk⟩:= exists_nat_gt ((5*C+1)*2/c)
  refine ⟨c/2,5*C,by positivity,by positivity,k, fun N g e l M=>?_⟩
  let T:=selected N (lesser l); let v:ℝ:= N.val; have he:1≤v:=Nat.one_le_cast.mpr N.property; have hs:= selected_size l N; let P(i: Stag N):= tiltCharge N j M i; have hv:= X N e M; let W:= T.erase (tinyMode N l); let G:=∑ i∈T,P i; let A:=∑ i∈W,P i; rw [show ‖bias l M j N‖= (v^4)⁻¹*‖G‖ from (by unfold bias; rw [norm_smul,norm_inv,norm_pow,norm_natCast])] -- tune
  have hj : ‖A‖≤5*C*v^5:=by
    apply (norm_sum_le ..).trans; calc
       _ ≤ ∑ i∈T, C*v:= (sum_le_sum (fun i l=>(hv i).2.1 (charge_zero l))).trans (sum_le_sum_of_subset_of_nonneg (erase_subset ..) (fun _ _ _=>by positivity))
       _ = _ :=by rw [sum_const,nsmul_eq_mul,show T.card=_ from hs]; unfold v; push_cast; ring
  constructor
  · rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]; have ht:= (hv (tinyMode N l)).2.2 (show tinyMode N l=_ from rfl); let Y:=‖P (tinyMode N l)‖; change c*v^9≤ Y+1 at ht
    have hy : Y ≤ ‖G‖+‖A‖:= calc
       _ = ‖G-A‖ := by unfold G A W; rw [← add_sum_erase T P (topIn ..),add_sub_cancel_right] -- fix
       _ ≤ _:= norm_sub_le ..
    have hh: 5*C*v^5+1 ≤ (c/2*v^5)*v^4:=by
        have hK:= hk.trans_le (show (k:ℝ)≤v from Nat.cast_le.mpr g); have hp:5*C+1≤ c/2*v:=by rw [div_lt_iff₀ p] at hK; linarith
        calc
           _ ≤ (5*C+1)*v^5:=by rw [add_mul,one_mul]; exact add_le_add_right (one_le_pow₀ he) _
           _ ≤ c/2*v*v^5:=by gcongr
           _ ≤ _:=by nlinarith only [show v^5 ≤ v^8 from pow_le_pow_right₀ he (by norm_num),p, he, mul_le_mul_of_nonneg_left (pow_le_pow_right₀ he (show 6 ≤ (9:ℕ) from (by omega))) p.le]
    change c/2*v^5* _≤_; linarith
  refine le_trans (mul_le_mul_of_nonneg_left (le_trans (norm_sum_le ..) (sum_le_sum (s:=T) (fun i t=> (hv i).1))) (by positivity)) ?_
  refine le_of_eq ?_; rw [sum_const,nsmul_eq_mul,show T.card=_ from hs]; unfold v; push_cast; field_simp

end scale
section value
lemma unitBias_view(C: Stag N→ Op SpinIdx)(o:Site N)(a b:SpinIdx)(g:Slot) : Dofu N C ((o,a),g) ((o,b),g) = ((N.val:ℂ)^4)⁻¹ * ∑ i:Site N, C (i,g) a b:=by
 rw [dent,if_pos rfl,mul_sum]; refine sum_congr rfl fun k _=>?_ ; change Fourier N o k* C (k,g) a b*star (Fourier N o k)= _; rw [mul_right_comm (Fourier ..),show Fourier N o k*star (Fourier N o k)=_ from ?_] -- tune not finish
 unfold Fourier; simp only [Matrix.of_apply,star_div₀]; rw [div_mul_div_comm, mul_comm (frequency k o),frequency_unit]; unfold normF; simp only [star_pow,star_natCast,one_div]; ring
lemma shiftLaw(g:Fin 3)(M:Jill.Male)(p:1≤j)(h:Even N.val)(s:Site N) (a b:SpinIdx)(x:a∈ plusHalf)(y:b∉plusHalf)(X:Wave (Single N))(A:Sea (Dofu N (field (needlesView N) j M)) X)(U:Bkg (More N)) : oneField U X (current N (lesser g) s a b)=oneField U X 1 * bias g M j N b a:=by
 unfold oneField; let S:=needlesView N; let G(k):= polarLift (field S j M k) (disk j M (Kea.angle S k)); let Q:=tickA N; let T:= Dofu N G; let Y:=mateK N; let V(f):=bias g M j N b f
 have hp:Clad (Dofu N (field S j M)) (tickA N) 1 1 T:=by rw [←map_one (Dofu N)]; exact torn S h j M G 1 1 (tiltClad M p h)
 let P:=Dofu N (tiltCharge N j M); have hx:laneP Q 1 T=P:=by
    rw [←show Dofu N 1=1 from map_one (Dofu N)]; exact (tall_s (N:=N) 1 G).symm
 have hl(c:Slot):inner ℂ Y (acts (put ((s,a),c)*takeF ((s,b),c)) X)=inner ℂ Y X * P ((s,b),c) ((s,a),c) := by
    let i:Single N:=((s,a),c); let l:Single N:=((s,b),c); let Z(k:Bool):Reader0 (Single N):= (k,basisKet (if k then l else i))
    have he:∀ i,KeyT (Z i) Q:=by
      intro k; cases k
      · change acts Q (basisKet i)= basisKet i; unfold Q; rw [touchP,cut_basis]; exact if_pos ((mem_Tset s a c).2 x)
      change acts Q (basisKet l)= 0; unfold Q; rw [touchP, cut_basis]; apply if_neg; exact fun k=> y ((mem_Tset s b c).1 k)
    have ht:= Emu.frown hp (tickB N) A Z he [false,true]; unfold pRead at ht; simp only [quant_one, mul_one,List.map_cons,List.map_nil, Function.comp_apply,List.prod_cons,List.prod_nil,skyGlow,act_one,Fock.rollC] at ht; rw [show ton (Z false)=put i from create_put i,show ton (Z true)=takeF l from remove_take l] at ht; apply ht.trans; congr 1
    rw [show runes _ [false,true]=_ from (show ∀ B:Bool→Bool→ℂ,Emu.runes B [false,true]=B false true from fun a=> (by simp [runes, spinC, offer, claps,picks, cites,besideX,Fock.cval,extendsU])) _]; change inner ℂ (basisKet l) (acts (laneP Q 1 T) (basisKet i))= _; rw [basis_inner,basis_act,hx]
 rw [current_words, act_sum, inner_sum, Pi.one_apply, act_one]; change ∑ i∈ _,inner ℂ Y _= _; simp_rw [hl]; rw [←mul_sum]; congr 1; unfold P bias selected; simp_rw [unitBias_view]; rw [Matrix.smul_apply, Matrix.sum_apply,Finset.sum_product]; simp_rw [←Finset.mul_sum]; change _ = ((N.val:ℂ)^4)⁻¹ * _; rw [sum_comm (f:=fun i:Site N=>fun k: Slot=> tiltCharge N j M (i,k) b a)]
end value
end YM.CF.Window
