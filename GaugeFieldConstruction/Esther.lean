import GaugeFieldConstruction.Trapeze
import GaugeFieldConstruction.SpinPay
import YM.SU5.Relativistic.Nashi
import YM.CF.Emu.Fern
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock.Flux
open Function Filter Metric NormedSpace Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Kea Flare Rush Tulip Cube SU Dial Thera
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker Classical
attribute [local instance] opCStarAlgebra
open YM.GaugeFieldConstruction
local notation "I"=> Complex.I
-- CRT on physical charts. Up lower.
variable {N:Side} {M:Jill.Male}
abbrev scarB (N:Side)(M:Jill.Male) (p:Stag N): Op SpinIdx:= (tilt_scar p 4 M)
abbrev schick (N:Side)(M:Jill.Male)(p:Stag N): Op SpinIdx:= shoe N 4 M p+scarB N M p
abbrev pinT (N:Side)(M:Jill.Male): Op (Single N):= pinBack N 4 M * boardC N 4 M * pinShift N 4 M
lemma seaUp (w:Pad 4 N) (M:Jill.Male) : pinT N M=Dofu N (schick N M):=by
 let P:=boardC N 4 M; let Q:=shoe N 4 M
 have h:=token_V w (by decide) M; unfold pinT; rw [h.bring,pinShift,basic_band w,←map_mul]; refine congrArg (Dofu N) ?_; funext i
 change Q i * (1+scarB N M i)=Q i +scarB N M i; rw [mul_add,mul_one]; unfold scarB tilt_scar scarH; rw [Matrix.mul_smul]; dsimp only [Q]; rw [←mul_assoc,←mul_assoc, (shoe_P w.1 i 4 M).isIdempotentElem.eq]
lemma mapsβ (w:Even N.val)(k:Stag N) : schick N M k=(1-Fir.zen (mixL 4 M.val (mel k.1)))*Aop:=by
 let P:=shoe N 4 M k; let p:=mel k.1; let V:= mixL 4 M.val p; let z:= zen V
 have hg:P= bar 4 M.val p:=by unfold P shoe field; rw [too_u]; rfl
 have hp:p∈realCube zone:=base_subset_realCube zone_pos (mel_h k.1)
 have hU:tmap (pm k.1)=p:=rfl
 let d:=slit k.1 4 M; have hx:shell 4 M.val p=(d:ℂ):= express 4 _ _ (show tmap (pm k.1) ∈ _ from hp) M.property
 let W:= 1-z; let L:=(W*Aop*(1+z)); have he:P=(d:ℂ) • L:= hg.trans ((bar_full _ _ hp (mel_away _) (graphs_ne (phys_mix _ _ M.property p hp.1))).1.trans (congrArg (· • L) hx)) -- tune
 have hz:Aop*(1+z)*Aop=Aop:=by
    rw [mul_add,mul_one,add_mul,AOne, show Aop*z*Aop=0 from ?_,add_zero]; rw [show Aop*z=z*(1-Aop) from zenA V,mul_assoc,sub_mul,AOne,one_mul,sub_self,mul_zero]
 have hT:P*Aop=d • (W*Aop):=by
    rw [he]; unfold L; rw [Matrix.smul_mul, mul_assoc W, mul_assoc W,show (Aop*(1+z)) * Aop=Aop from hz,Complex.coe_smul]
 -- P E P = d • P follows directly W*A*A *( d ... )
 have hv:P*Aop*P=d • P:=by
    have hb: Aop * W * Aop = Aop:=by unfold W; rw [mul_sub,mul_one,sub_mul,AOne, show Aop*z*Aop=0 from ?_,sub_zero]; rw [show Aop*z=z*(1-Aop) from zenA V,mul_assoc,sub_mul,AOne,one_mul,sub_self,mul_zero]
    rw [hT,he,Matrix.smul_mul,Matrix.mul_smul,show W*Aop*L=L from ?_]; unfold L; rw [←mul_assoc,←mul_assoc,mul_assoc W Aop,mul_assoc W (Aop*W),hb]; -- maybe order
 have hd:0<d:= slit_positive (by decide) w _ M
 change P+d⁻¹ • (P*Aop*(1-P))= W*Aop; rw [mul_sub,mul_one,hv,hT,smul_sub, smul_smul,smul_smul,inv_mul_cancel₀ hd.ne',one_smul,one_smul]; abel
lemma slotA (r:GaugeFieldConstruction.Cauchy.Spin): Cauchy.band false r ∈plusHalf ∧ Cauchy.band true r ∉ plusHalf:=by fin_cases r <;> decide
abbrev tenderD (x y:GaugeFieldConstruction.Cauchy.Spin)(p:Momentum):ℂ:= ∑ i:Axis, (-I*p i)*star (GaugeFieldConstruction.Cauchy.Hij i x y)
lemma looksB (w: Even N.val)(k:Stag N)(r t:GaugeFieldConstruction.Cauchy.Spin): schick N M k (Cauchy.band true t) (Cauchy.band false r)=tenderD r t (mixL 4 M.val (mel k.1)):=by
 rw [mapsβ w,show Aop=cutM plusHalf from Adef.trans Lat.raising.symm]; unfold cutM; rw [Matrix.mul_diagonal, if_pos (slotA _).1, mul_one,Matrix.sub_apply, Matrix.one_apply_ne (show Cauchy.band true t ≠ Cauchy.band false r from fun e=> (slotA t).2 (by rw [e]; exact (slotA r).1)),zero_sub] -- tune
 unfold zen tenderD; simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]; rw [← sum_neg_distrib]; apply sum_congr rfl; intro i _; rw [← show gammaOp i (Cauchy.band true t) (Cauchy.band false r)= star (Cauchy.Hij i r t) from ?_] -- direction revise
 · ring
 rw [← (gammaAdj i).star_eq]; change star (gammaOp i (Cauchy.band false r) (Cauchy.band true t))= _; rw [show gammaOp i _ _=Cauchy.Hij i r t from congrArg (fun M:GaugeFieldConstruction.Cauchy.M2=>M r t) (Cauchy.gamma_price i)]
-- winding cost
abbrev tagR(N:Side)(x:Cover):ℂ:= Rush.fee (Rush.periods N x)
lemma phasor (p:Site N)(x:Cover): mode (mel p) x= frequency p (wrap N x)* tagR N x:=by
 rw [←freq_mode]; unfold tagR; conv_lhs=> arg 2; rw [← Rush.carrying N x]; -- syntax
 rw [mode_shift,mode_fee]
abbrev κR (N:Side)(b:Bool)(i:Cauchy.Spin)(n:Slot)(x:Cover):Single N:= ((wrap N x,Cauchy.band b i),n)
abbrev frankφ (p:Momentum)(x:Cover) :ℂ:= Laurent.mode p x
abbrev tellerP (x y:Cover)(i j:Cauchy.Spin) (N:Side)(M:Jill.Male)(s:Site N):ℂ:= frankφ (mel s) (y-x)* tenderD i j (mixL 4 M.val (mel s))
lemma matΘ (p:Pad 4 N)(x y:Cover)(i j:Cauchy.Spin)(t s:Slot): tagR N x * tagR N y * pinT N M (κR N true j t y) (κR N false i s x) = if t=s then (stageVolume N)⁻¹ * ∑ a:Site N,tellerP x y i j N M a else 0:=by
 rw [seaUp p,Emu.dent]; change _*(if t=s then _ else 0)=_; by_cases h:t=s; swap; · simp [h]
 subst t; rw [if_pos rfl,if_pos rfl,mul_sum,mul_sum]; refine sum_congr rfl fun a _=>?_ ; simp only [κR,looksB p.1]; unfold tellerP frankφ; rw [sub_eq_add_neg,Laurent.mode_shift,show mode (mel a) (-x)=star (mode (mel a) x) from ?_,phasor,phasor, star_mul]; unfold tagR; rw [fee_real]; unfold Fourier stageVolume; simp only [Matrix.of_apply,star_div₀,normF,star_pow,star_natCast]; ring -- tune
 have hg : star (mel a)=mel a:=(mel_h a).1; have he:= mode_adjoint (mel a) x; rw [hg] at he; exact he.symm
end YM.CF.Fock.Flux
end
