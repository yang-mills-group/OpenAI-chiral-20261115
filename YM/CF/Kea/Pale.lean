import YM.CF.Kea.Vest
set_option autoImplicit false
noncomputable section
namespace YM.CF.Kea
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill SU Rush Tulip Cube
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {N:Side}{d:Candle}(S:Slide N d)
open WilsonFrame
lemma Tor_H(a:Axis): love N ((frame matter (links (tax d)) (anticut N)).T a)=Dofu N fun i=> (BZ.atom (angle S i)).T a:=by
 apply vind; ext ⟨⟨x,i⟩,l⟩ ⟨⟨y,j⟩,L⟩; rw [wool, show (colU N).val=wedgeN N from rfl, wedgeN,← map_mul]
 let u:= links (N:=N) (tax d)
 let P:= tax d (N:=More N); change (Lat.shift matter u (anticut N) a*(spatialU N Slot).val) (x,i,l) (y,j,L)=_
 rw [Lat.shift,rowBlock]; have he:u (x,a)=waveG (d a)*waveG (d a):=rfl -- links prod
 simp only [hop,color,he,map_mul]
 change ∑ z:SpinIdx×Slot, (_ • ((1:Op SpinIdx) ⊗ₖ ((matter (waveG (d a))).val * (matter (waveG (d a))).val))) (i,l) z * _= _
 rw [sum_eq_single (i,l)]
 · conv_lhs => rw [matD,Matrix.diagonal_mul_diagonal]; simp only [Matrix.smul_apply, Matrix.kronecker_apply, Function.comp_apply,Matrix.one_apply_eq,Matrix.diagonal_apply_eq]
   change (_:ℂ)*_ = (if l=L then Fourier N x y*((pw ((angle S (y,L)) a)) • (1:Op SpinIdx)) i j else 0); simp only [spatialU,Matrix.kronecker_apply, Matrix.smul_apply,Matrix.one_apply,Prod.mk.injEq]
   by_cases v:i=j <;> by_cases g:l=L <;> simp only [v,g,ite_false,ite_true,false_and,and_false,mul_zero,smul_eq_mul,mul_one,one_mul,true_and] -- tune
   rw [← modal, ← wage (peer_p S _) (step a),modal]; simp only [Pi.add_apply,rise,pulse,phase_a]; have hh:=HF x y a; rw [← show pw (pm y a)=BZ.phase (pm y a) from rfl] at hh; linear_combination pw (freqD (d a) L)*pw (freqD (d a) L)*hh
 · rintro ⟨b,u'⟩ _ h; rw [matD,Matrix.diagonal_mul_diagonal]; by_cases e:i=b <;> by_cases v:l=u' <;> first| exact False.elim (h (Prod.ext e.symm v.symm))|simp [Matrix.one_apply,e,v]; -- tune
 simp
lemma caseH:dome N (profile (tax d))=Dofu N fun i=> (BZ.atom (angle S i)).H :=by
 rw [dome_kernel]; let V:=frame matter (links (tax d)) (anticut N); let X:= fun i:Stag N=> BZ.atom (angle S i)
 let K:=Dofu N; have ht a: love N (V.T a)=K (fun i=> (X i).T a):=Tor_H ..
 have hv(a:Axis): love N (star (V.T a))= K (fun i=> star ((X i).T a)):=by rw [map_star,ht]; exact (Dofu_s _).symm
 have he :∀ a:Axis,love N (V.inc a)= K (fun i=> (X i).inc a):=by
   intro a; let T(i:Stag N):= (X i).T a; let Y:= fun i=>star (T i); let Q(i:Stag N):= (X i).gamma a
   have hh:love N (V.gamma a)= K Q:=turnU _; rw [inc,diff,lap]; simp only [map_add,map_mul,map_one,map_sub, love_scale, hh, ht,hv]; change _=K (1-(1/2:ℝ) • (T+Y)+Q*((1/2:ℝ) • (T-Y))); simp only [map_add,map_smul,map_mul,map_sub,map_one]; rfl
 change love N (V.chir*V.H0)=K ((fun i=> (X i).chir)*(fun i=> (X i).H0))
 rw [H0,map_mul,map_add,map_sum,map_neg,map_one,show love N V.chir= _ from turnU (N:=N) grading,map_mul]; congr 1 -- tune
 rw [show (fun i=> (X i).H0)=- (1:Stag N→Op SpinIdx)+ ∑ j:Axis, fun i=> (X i).inc j by funext i; simp [H0],map_add,map_neg,map_one,map_sum]; simp_rw [he]
lemma planet(A:Stag N→ Op SpinIdx)(h:∀ i,Safe (A i))(p:Safe (Dofu N A)): projector (Dofu N A)=Dofu N fun i=>projector (A i):=by
 let Q:= Dofu N
 let B:= fun k=>rsEval (A k)
 have hs:HasSum (fun i k=>rsTerm (A k) i) B:= by rw [Pi.hasSum]; exact fun i=> rs_sum ((h i).good.trans_lt rho_lt)
 have hx: HasSum (rsTerm (Q A)) (Q B):=by
    convert hs.map Q Q.toLinearMap.continuous_of_finiteDimensional using 1; ext i:1
    change rsTerm _ i= Q (fun k=>rsTerm (A k) i)
    rw [show (fun k=>rsTerm (A k) i)=SignScalar.c i • ((1-(1/256:ℝ) • A^2)^i) by funext k; simp only [rsTerm,slack,Pi.pow_apply,Pi.smul_apply,Pi.sub_apply,Pi.one_apply],map_smul,map_pow,map_sub,map_one,map_smul,map_pow]; rfl
 rw [show (fun k=>projector (A k))=(1/2:ℝ) • (1+((1/16:ℝ) • A)*B) by funext k; simp [projector,polarity,B], projector,polarity,(rs_sum (p.good.trans_lt rho_lt)).unique hx,map_smul,map_add,map_mul,map_one,map_smul]
def field(j:ℕ)(M:Jill.Male):Stag N→Op SpinIdx:= fun i=> bar j M.val (tmap (angle S i))
lemma idol(j:ℕ)(M:Jill.Male)(g:Even N.val):IsStarProjection (Dofu N (field S j M)):=by
 let A:=field S j M; let T:=Dofu N; have hp(i):= firm_bar j M.val M.property (base_subset_realCube zone_pos (b_base (up_p S g i)))
 exact ⟨(show T A*T A= _ from by rw [←map_mul,show A*A=A from funext fun i=>(hp i).1]),(show star (T A)=T A from by rw [← show T (star A)=_ from Dofu_s A,show star A=A from funext fun i=>(hp i).2])⟩
-- key theorem ALL flat momenta and histories
lemma azur(j:ℕ)(p:1≤j):∃ v:ℕ,∀ {N:Side}{d:Candle} (S:Slide N d),Even N.val →v ≤ N.val → ∀ M:Jill.Male, funde j M N (profile (tax d))=Dofu N (field S j M):=by
 obtain ⟨e,he,k,R⟩:= (painter j p).2; refine ⟨k,fun {N} {d} S g l M=>?_⟩
 let Y:=field S j M; let T:= Dofu N; let F:=T Y; have hp:=idol S j M g; let x:=profile (tax d (N:=More N)); unfold funde; split
 next h=>
    let A(i:Stag N):=(BZ.atom (angle S i)).H; have hb:dome N x=T A:=caseH _
    change projector (dome N x)=_; rw [hb,planet A (fun i=>BZ.atom_safe (angle S i))]; congr 1 -- inspect
    · funext i; unfold field; rw [h]; exact (start_bar j (angle S i)).symm
    rw [← hb]; exact Broad (show (0:ℝ)<1/(60*256) by norm_num) (by norm_num) _ (tax_guard _ _ _ (by positivity))
 have hb:art N j M.val x= (2:ℝ) • F-1:=by
    have hv: reserveP N j M.val x=F:=by
       unfold reserveP dialW; simp_rw [show ∀ o,tourP N (tub (bar j M.val)) o x=F from fun o=>tour_e S g _ (bar j M.val) (cBar j M.val true p M.property) o]; simp only [sum_const,card_univ]; rw [←Nat.cast_smul_eq_nsmul ℝ, inv_smul_smul₀]; positivity
    rw [art,pale,ice_pr,hv,(show star F=F from hp.2),two_smul]
 let A:=art N j M.val x; have ht:A*A=1:=by change art _ _ _ _*_=_; change art N j M.val x * art N j M.val x=_; rw [hb]; simp only [mul_sub,sub_mul,mul_one,one_mul, Matrix.smul_mul, Matrix.mul_smul,show F*F=F from hp.1]; module -- tune
 change projector A=F; rw [projector,polarity_scalar (R M N l _ (tax_guard d _ _ he.le)) 1 (by norm_num) (by simpa using ht)]; change (1/2:ℝ) • (1+_)=_; rw [hb]; norm_num; module
end YM.CF.Kea
