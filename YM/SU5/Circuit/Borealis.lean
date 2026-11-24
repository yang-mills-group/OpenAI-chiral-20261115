import YM.SU5.Circuit.Chariot
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.Regis.Circuit
open Function Filter Metric Lattice Laurent Next.Free Bloch Finset CF CF.Lat CF.Jill CF.Ember CF.Flare CF.Onyx CF.Fir
open Precision Exterior Matrix RG Work.F06 MeasureTheory
open YM.Stationary (Gaia cartWeight)
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix -- DecEq careful
-- assembly real
variable {N:ℕ→ Side}{M:ℕ→Bed}{k:∀ i,Site (N i)}{R:ℕ→ℝ}{q:Clip}{σ η C D:ℝ}{X:Gaia}
variable (P:Yard N R)(H:Tendsto (fun i=> duel (R i) (rubyOff (N i)) (k i)) atTop (𝓝 X)) (A:∀ i, Floor (M i) q (N i) η C)(G:∀ i,(M i).covered σ C)
-- helpers
private lemma through_chip {p:ℕ→ℂ}{r:ℕ→ℂ}{x:ℂ}(u:Tendsto p atTop (𝓝 0))(v:Tendsto (fun i=>r i*p i) atTop (𝓝 x)): Tendsto (fun i=> r i*chip (p i)) atTop (𝓝 (Complex.I*x)):=by
 let F:=dslope chip 0; have he(z :ℂ): chip z=z*F z:=by simpa [F] using (sub_smul_dslope chip 0 z).symm
 have hd : HasDerivAt chip Complex.I 0:=by have hh:= ((hasDerivAt_id' (0:ℂ)).const_mul Complex.I).cexp.sub_const 1; unfold chip; simpa only [mul_one,mul_zero,Complex.exp_zero,one_mul] using hh
 have hp:F 0=Complex.I:=(dslope_same ..).trans hd.deriv
 have hx:Tendsto F (𝓝 0) (𝓝 Complex.I):= hp ▸ (show Tendsto F _ (𝓝 (F 0)) from (continuousAt_dslope_same.mpr hd.differentiableAt).tendsto) -- tune
 simp_rw [he,←mul_assoc]; rw [mul_comm Complex.I]; exact v.mul (hx.comp u)
local notation "ρ" i:max=>rubyM (k i)
local notation "r" i:max=>(R i:ℂ)
include P H
omit P in
lemma momentum_high : Tendsto (fun i=> r i • ρ i) atTop (𝓝 (river X)):= drought N _ R k X H -- tune
lemma momentum_ice : Tendsto (fun i=> ρ i) atTop (𝓝 0):=by
 have he:= ((Complex.continuous_ofReal.continuousAt.tendsto.comp ((tendsto_inv_atTop_zero (𝕜:=ℝ)).comp P.high)).smul (momentum_high H)) -- tune P needed
 have hk(i:ℕ):r i≠0:=by exact_mod_cast (P.pos i).ne'
 simpa only [Function.comp_def,Complex.ofReal_zero,zero_smul,Complex.ofReal_inv,inv_smul_smul₀ (hk _)] using he
lemma chipUnder (a:Axis): Tendsto (fun i=> r i*tripQ 1 (ρ i) a) atTop (𝓝 (Complex.I*(river X a))):=by
 have hg:= tendsto_pi_nhds.mp (momentum_ice P H) a; have hx:= tendsto_pi_nhds.mp (momentum_high H) a; simpa [tripQ] using through_chip hg (show Tendsto (fun i=> r i*((ρ i) a)) atTop _ from hx)
omit P H
variable {m n l: Type*} [Fintype m][Fintype n][Fintype l]
abbrev Meet (A:ℕ→Matrix m n ℂ)(X:Matrix m n ℂ): Prop:=∀ i j,Tendsto (fun k=>A k i j) atTop (𝓝 (X i j))
lemma Meet.mul {A:ℕ→Matrix m n ℂ}{B:ℕ→Matrix n l ℂ}{X:Matrix m n ℂ}{Y:Matrix n l ℂ}(u:Meet A X)(v:Meet B Y): Meet (fun i=> A i*B i) (X*Y):=by intro a b; simp_rw [Matrix.mul_apply]; exact tendsto_finsetSum _ fun i _=>(u a i).mul (v i b)
lemma Meet.plusK {A B:ℕ→Matrix m n ℂ}{X Y:Matrix m n ℂ}(u:Meet A X)(v:Meet B Y): Meet (fun i=> A i+B i) (X+Y):=fun i j=> (u i j).add (v i j)
lemma Meet.revenge [DecidableEq n]{A:ℕ→ Matrix n n ℂ}{X:Matrix n n ℂ}(u:Meet A X)(p:X.det≠0): Meet (fun i=> (A i)⁻¹) X⁻¹ := by
 have he:ContinuousAt Inv.inv X:= continuousAt_matrix_inv _ (by rw [show (Ring.inverse (M₀:=ℂ))= Inv.inv from funext Ring.inverse_eq_inv]; exact continuousAt_inv₀ p); have hu :Tendsto A atTop (𝓝 X):=@tendsto_pi_nhds ℕ n (fun i=> n→ℂ) _ _ _ _ |>.mpr (fun i=> tendsto_pi_nhds.mpr (u i)) -- tune
 have ht:=he.tendsto.comp hu; exact fun i j=>tendsto_pi_nhds.mp (tendsto_pi_nhds.mp ht i) j
abbrev BoreV (X:Gaia)(j:ℕ):= wedge j (fun i=> Complex.I*(river X i))
include P H
lemma young (j:ℕ): Meet (fun i=> r i • signal 1 j (ρ i)) (BoreV X j):=by
 intro a b; simp only [signal,BoreV,wedge,Matrix.smul_apply,Matrix.sum_apply,smul_eq_mul,Finset.mul_sum,← mul_assoc]; exact tendsto_finsetSum _ fun i _=> (chipUnder P H i).mul_const _
lemma oldster (j:ℕ):Meet (fun i=> r i • mirage 1 j (ρ i)) (BoreV X j)ᴴ:=by
 have he(i): r i • mirage 1 j (ρ i)=(r i • signal 1 j (ρ i))ᴴ:= by rw [Matrix.conjTranspose_smul,mirage_herm 1 _ (ruby_pigment _)]; simp
 intro a b; simp_rw [he,conjTranspose_apply]; exact (young P H j b a).star
lemma haloV : Tendsto (fun i=> r i^2* divisor 1 (ρ i)) atTop (𝓝 ((‖X‖:ℂ)^2)):=by
 have he(z: Momentum): seedQ 1 z=tripQ 1 z:=funext fun i=>by simp [seedQ,tripQ,narrow]
 have hg(i:ℕ)(a:Axis): r i^2* ‖seedQ 1 (ρ i) a‖^2 = ((‖r i * tripQ 1 (ρ i) a‖^2:ℝ):ℂ):=by simp [he,norm_mul, mul_pow, Real.norm_of_nonneg (P.pos i).le] -- tune coerce implicit
 have hx(x:Gaia): (∑ i, ((‖Complex.I*(river x i)‖^2:ℝ):ℂ))=(‖x‖:ℂ)^2:=by
    rw [← Complex.ofReal_pow,←Complex.ofReal_sum,← Stationary.geode_sum]; congr 1; apply sum_congr rfl; intro i _; change ‖Complex.I*(x i:ℂ)‖^2=_; simp
 simp_rw [divisor_normSq _ (ruby_pigment _),Complex.ofReal_sum, Finset.mul_sum, Complex.ofReal_pow,hg]
 rw [← hx]; exact tendsto_finsetSum _ fun i _=>Complex.continuous_ofReal.continuousAt.tendsto.comp ((chipUnder P H i).norm.pow 2)
lemma atLaplacian : (BoreV X 1)ᴴ*BoreV X 1 + BoreV X 0*(BoreV X 0)ᴴ=(‖X‖:ℂ)^2 • (1:wireC):=by
 have hh:= Meet.plusK (Meet.mul (oldster P H 1) (young P H 1)) (Meet.mul (young P H 0) (oldster P H 0)); ext i j; apply tendsto_nhds_unique (hh i j)
 simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul,←sq,←smul_add,trough,smul_smul,Matrix.smul_apply]; exact (haloV P H).mul_const _
variable (u:0<σ)
include A G u
lemma AscentM : Meet (fun i=> tab (M i).metric (k i)) 1:=by
 intro a b; let f(i:ℕ):= tab (M i).metric (k i) a b; let X:orbC:=1; let e(i:ℕ):=∑ j, ‖Exterior.q (ρ i) j‖
 have ht:Tendsto e atTop (𝓝 0):=by
    have hy (j:Axis):Tendsto (fun i=>‖Exterior.q (ρ i) j‖) atTop (𝓝 0):=by
       have hs:Continuous (fun p:Momentum=> ‖Exterior.q p j‖):=by unfold Exterior.q; fun_prop
       have hv:= hs.continuousAt.tendsto.comp (momentum_ice P H); simpa only [Exterior.q,Pi.zero_apply,mul_zero,Complex.exp_zero,sub_self,norm_zero,Function.comp_def] using hv
    simpa only [Finset.sum_const_zero] using (tendsto_finsetSum univ (fun j _=> hy j))
 change Tendsto f atTop (𝓝 (X a b)); rw [tendsto_iff_norm_sub_tendsto_zero]; apply squeeze_zero (fun i=> norm_nonneg _) (g:=fun i=>e i/σ*C) (fun i=> ?_) (by simpa using (ht.div_const σ).mul_const C)
 unfold X; rw [← (A i).starts]; exact row_entry_depart (G i).2.1 u (ρ i) (ruby_pigment _) (e i) (by unfold e; positivity) (fun j=> by apply Finset.single_le_sum (f:=fun j=> ‖Exterior.q (ρ i) j‖) (fun _ _=> norm_nonneg _) (mem_univ _)) a b
lemma ascendsCliff : Meet (fun i=> r i^2 • cliffMap (M i) (ρ i)) ((‖X‖:ℂ)^2 • (1:wireC)):=by
 have he:= Meet.plusK (Meet.mul (Meet.mul (oldster P H 1) (AscentM P H A G u)) (young P H 1)) (Meet.mul (young P H 0) (oldster P H 0)); simp only [Matrix.mul_one, atLaplacian P H,Matrix.smul_mul,Matrix.mul_smul, smul_smul,←sq,←smul_add] at he; exact he
abbrev Boreas (X:Gaia):orbC:= (‖X‖:ℂ)^(-2:ℤ) • (BoreV X 1*(BoreV X 1)ᴴ)
lemma skyman (p:X≠0) : Meet (fun i=> Cov (M i) (ρ i)) (Boreas X):=by
 let r':ℂ:=(‖X‖:ℂ); have hp: r' ≠0:=by unfold r'; exact_mod_cast (by exact (norm_pos_iff.mpr p).ne' : ‖X‖≠0)
 have hf(i):r i≠0:=by exact_mod_cast (P.pos i).ne'
 let T : wireC:=1; let v(i:ℕ):wireC:= cliffMap (M i) (ρ i); let S(i:ℕ):= signal 1 1 (ρ i); let A'(i:ℕ):=mirage 1 1 (ρ i)
 have ht:= Meet.mul (Meet.mul (young P H 1) ((ascendsCliff P H A G u).revenge (by rw [det_smul,Matrix.det_one,mul_one]; exact pow_ne_zero _ (pow_ne_zero 2 hp)))) (oldster P H 1)
 have hz(i):r i*((r i^2)⁻¹ * r i)=1:=by have he:=hf i; field_simp
 have hg: (r'^2 • T)⁻¹ = (r'^2)⁻¹ • T:=by rw [Actus.inverseCall _ _ (pow_ne_zero _ hp), show T=1 from rfl]; simp
 have he (i:ℕ): (r i • S i)*(r i^2 • v i)⁻¹*(r i • A' i)=Cov (M i) (ρ i):=by
   rw [Actus.inverseCall _ _ (pow_ne_zero _ (hf i))]; unfold Cov; simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul,mul_assoc, hz i,one_smul]; rfl
 change Meet (fun i=> (r i • S i)*(r i^2 • v i)⁻¹*(r i • A' i)) (BoreV X 1 * (r'^2 • T)⁻¹*(BoreV X 1)ᴴ) at ht; simp_rw [he,hg] at ht; unfold T at ht; simp only [Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one] at ht; unfold Boreas; rw [_root_.zpow_neg,zpow_ofNat]; exact ht
end YM.Regis.Circuit
#print axioms YM.Regis.Circuit.skyman
