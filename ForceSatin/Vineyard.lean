import ForceSatin.Sugars
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option maxHeartbeats 440000
set_option quotPrecheck false
noncomputable section
namespace YM.Regis.Circuit.SpringDay
open Function Filter Metric Lattice Laurent Next.Free Bloch Finset CF CF.Lat CF.Jill CF.Ember CF.Flare CF.Onyx CF.Fir
open Precision Exterior RG Work.F06
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix
local notation "π" => Real.pi
open YM.Stationary (Gaia exileE cartWeight cart_weight_pos orbit_at)
open MeasureTheory
open scoped SchwartzMap FourierTransform
open Complex (ofReal)
open Complex (I)
namespace Spring
@[fun_prop] structure Grow(f: Gaia→ℂ) : Prop where
 rise : ∃ (d:ℕ)(C:ℝ),0≤C ∧ ∀ x:Gaia,1≤‖x‖→ ‖f x‖≤ C* ‖x‖^d
namespace Grow
variable {f g : Gaia→ℂ}(h:Grow f)
include h
@[fun_prop] lemma mul (k:Grow g):Grow fun x=> f x*g x:=by
 obtain ⟨d,C,c,p⟩:= h.rise; obtain ⟨e,V,v,t⟩:= k.rise; refine ⟨d+e,C*V,by positivity,fun x a=>?_⟩; rw [norm_mul]; exact (mul_le_mul (p x a) (t x a) (norm_nonneg _) (by positivity)).trans_eq (by rw [pow_add]; ring)
@[fun_prop] lemma add (k:Grow g):Grow fun x=> f x+g x:=by obtain ⟨d,C,c,p⟩:= h.rise; obtain ⟨e,V,v,t⟩:= k.rise; refine ⟨d+e,C+V,by positivity,fun x a=>?_⟩; apply (norm_add_le ..).trans ((add_le_add (p x a) (t x a)).trans ?_); rw [_root_.add_mul]; gcongr <;> omega
@[fun_prop] lemma neg:Grow fun x=> -f x:=by obtain ⟨d,C,c,p⟩:= h.rise; exact ⟨d,C,c,fun x a=>by simp [p x a]⟩
@[fun_prop] lemma powL (n:ℕ):Grow fun x=> (f x)^n:=by
 induction n with
 | zero=> simpa using (show Grow (fun _=> (1:ℂ)) from ⟨0,1,zero_le_one,fun _ _=>by simp⟩)
 | succ n ih=> simpa [_root_.pow_succ] using ih.mul h
lemma zoom (k:Swift g): Swift fun x=> f x*g x:=by obtain ⟨d,C,c,p⟩:= h.rise; constructor; intro n; obtain ⟨A,a,q⟩:=k.fast (n+d); refine ⟨C*A,by positivity,fun x e=>?_⟩; rw [norm_mul]; refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (p x e) (norm_nonneg _)) (pow_nonneg (norm_nonneg _) _)) ((Eq.trans_le ?_ (mul_le_mul_of_nonneg_left (q x e) c))); rw [pow_add]; ring
omit h
@[fun_prop] lemma fixity (c:ℂ): Grow (fun _=> c):=⟨0,‖c‖,by positivity,fun _ _=> by simp⟩
@[fun_prop] lemma dtype (i:Axis): Grow fun x=>(x i:ℂ):=⟨1,1,zero_le_one,fun x _=>by simpa using sed x i⟩
@[fun_prop] lemma languor : Grow fun x=>(‖x‖:ℂ):=⟨1,1,zero_le_one,fun x _=>by simp⟩
@[fun_prop] lemma dusk : Grow fun x=>(‖x‖:ℂ)⁻¹:=⟨0,1,zero_le_one,fun x a=> by simp only [norm_inv, Complex.norm_real,norm_norm,pow_zero,mul_one]; exact inv_le_one_of_one_le₀ a⟩ -- tune
@[fun_prop] lemma swell : Grow fun x:Gaia=> (fieldV x:ℂ):= by unfold fieldV; push_cast; simp_rw [div_eq_mul_inv]; fun_prop
@[fun_prop] lemma swellinv :Grow fun x:Gaia=> (fieldV x:ℂ)⁻¹:= by unfold fieldV; push_cast; simp_rw [div_eq_mul_inv,_root_.mul_inv, ←_root_.inv_pow]; fun_prop
lemma pixie : Swift fun x=>(elf x 1:ℂ):=by
 constructor; intro k; obtain ⟨C,c,Q⟩:= tribune (1/4) (by norm_num) k; refine ⟨C,c.le,fun i e=>?_⟩; unfold elf fieldV; rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _),div_one,show -(‖i‖^2/4)=-(1/4:ℝ)*‖i‖^2 from (by ring)]; apply le_trans _ (Q ‖i‖ (norm_nonneg _)); gcongr; linarith
end Grow
-- units leg prices
private lemma Garden {f g: Gaia→ℂ}(G:Swift g)(h:∀ x:Gaia,x≠0→ f x=g x): Swift f:=by constructor; intro k; obtain ⟨C,c,p⟩:= G.fast k; refine ⟨C,c,fun i h'=> ?_⟩; rw [h i (norm_pos_iff.mp (zero_lt_one.trans_le h'))]; exact p i h'
private lemma ivy(a:Axis)(x:Gaia)(p:x≠0): Maxwell.grad a Maxwell.Green x = cartWeight*(-(Real.pi^2/fieldV x^2))*(x a/2):=by rw [Maxwell.first_Green p]; unfold Maxwell.normal cartWeight fieldV; have hz:= Real.pi_pos; have h:=norm_pos_iff.mpr p; field_simp; ring
private lemma thorn(a b:Axis)(x:Gaia)(p:x≠0): Maxwell.grad a (Maxwell.grad b Maxwell.Green) x = cartWeight*(Real.pi^2/(fieldV x)^3*2*(x a/2)*(x b/2)+ -(Real.pi^2/(fieldV x)^2)*(YM.basis a b/2)):=by rw [Maxwell.second_Green p]; unfold cartWeight fieldV Maxwell.normal; have hz:=Real.pi_pos; have h:=norm_pos_iff.mpr p; field_simp; ring
private lemma feeM (a b:Axis):Swift fun x=> kinder a b 1 x - Maxwell.grad a (Maxwell.grad b Maxwell.Green) x:=by
 let Φ(x:Gaia):ℂ:= fieldV x
 let f(x:Gaia):ℂ:= (cartWeight:ℂ)*(Real.pi:ℂ)^2*(-(2+2*(Φ x)+(Φ x)^2)/(Φ x)^3*((x a:ℂ)/2)*((x b:ℂ)/2)+(1+Φ x)/(Φ x)^2*((YM.basis a b:ℂ)/2))
 have hf:Grow f:=by unfold f Φ; simp_rw [div_eq_mul_inv, ← _root_.inv_pow]; fun_prop (disch:=exact Grow.swell) -- tune
 refine Garden (hf.zoom Grow.pixie) (fun x p=> ?_); rw [kinder, one_pow, inv_one, gaze a b p one_pos,thorn a b x p]; unfold f Φ velvet dye βrock; push_cast; ring
private lemma stellarP (A B X Y:Axis)(h:Swift (kinder A B 1 - fun x:Gaia=> (↑(Maxwell.grad A (Maxwell.grad B Maxwell.Green) x:ℝ):ℂ))): Swift fun x=> solo X Y (kinder A B 1 x)-solo X Y ((Maxwell.grad A (Maxwell.grad B Maxwell.Green) x:ℝ):ℂ):=by unfold solo; split_ifs; exact h; simp only [sub_self]; exact Swift.zero
section
variable (P Q:Lattice.PlaqAxes)
local notation "A" => P.val.1
local notation "B" => P.val.2
local notation "Cμ" => Q.val.1
local notation "D" => Q.val.2
lemma frostGauge : Swift (hotK (plaquette P) (plaquette Q) 1-specter P Q):=by
 let F(a b u v:Axis)(x:Gaia):= solo a b (kinder u v 1 x)-solo a b ((Maxwell.grad u (Maxwell.grad v Maxwell.Green) x:ℝ):ℂ)
 have hf(a b u v:Axis):Swift (F a b u v):= stellarP u v a b (feeM u v)
 apply Garden (((hf Cμ B A D).sub (hf D B A Cμ)).sub ((hf Cμ A B D).sub (hf D A B Cμ))); intro i e; simp only [Pi.sub_apply]; rw [show hotK (plaquette P) (plaquette Q) 1 i=_ from (by simpa only [one_pow,inv_one] using inConcerto P Q 1 i one_pos),specter,Maxwell.bareCurl,Pi.sub_apply,Maxwell.Bare.opp_grad e,Maxwell.Bare.opp_grad e]; unfold F solo; push_cast; split_ifs <;> push_cast <;> abel
abbrev ges(p:Gaia):= regal (glad p) (plaquette P) (plaquette Q)
end
abbrev fettle (a:Axis)(x:Gaia):ℂ:= -2* I* Maxwell.grad a Maxwell.Green x
lemma iceberg (x i:Gaia)(a:Axis):burn x i*incense a (glad i)= -2* I * nerve a 1 x i:=by
 unfold incense nerve purr pet; rw [gathering,glacial]; push_cast; rw [show glad i a=(i a:ℂ) from rfl]; ring_nf; norm_num -- tune
lemma frostMatter(a:Axis):Swift (gorge (incense a ∘ glad)-fettle a):=by
 let g(x:Gaia):ℂ:= -2* I* (cartWeight:ℂ) *(Real.pi:ℂ)^2/(fieldV x:ℂ)^2*(1+ (fieldV x:ℂ))*((x a:ℂ)/2)
 have hp:Grow g:=by unfold g; simp_rw [div_eq_mul_inv, ← _root_.inv_pow]; fun_prop -- tune
 apply Garden (hp.zoom Grow.pixie); intro i e; unfold gorge fettle; change _*(∫ p,burn i p*incense a (glad p)) - _ = _
 simp_rw [iceberg]; rw [integral_const_mul, say _ one_pos e, ivy a i e]; unfold g dye; push_cast; ring
end Spring
#print axioms Spring.frostGauge
namespace Spring
-- run projected spectra; exact Maxwell poly and Vertex
structure SunPay (F:Momentum→ℂ)(X: Gaia→ℂ) : Prop where
 whole(p: Gaia) : Integrable (fun x=> burn p x* F (glad x))
 poly : ∃ A:Gaia→ℂ,HasTemperateGrowth A ∧ ∀ x:Gaia,F (glad x)= A x*(pet 1 x:ℂ)
 deft : Swift (gorge (F ∘ glad) - X)
namespace SunPay
variable {F:Momentum→ℂ} {X:Gaia→ℂ}(h:SunPay F X)
abbrev high(f:Momentum→ℂ)(p:Gaia):= (1-(blazing p:ℂ))*f (glad p)
abbrev low(f:Momentum→ℂ)(p:Gaia):= (blazing p:ℂ)*f (glad p)
include h
lemma loft :∃ f:𝓢(Gaia,ℂ), (f:Gaia→ℂ)= high F:=by
 obtain ⟨V,hv,b⟩:= h.poly; obtain ⟨f,hf⟩:= vRock V hv; refine ⟨f,hf.trans (funext fun i=> ?_)⟩; rw [high,b, mul_assoc]
lemma tar(i:Gaia):Integrable (fun x=> burn i x* high F x):=by obtain ⟨f,v⟩:= loft h; rw [←v]; refine (f.integrable (μ:=volume)).norm.mono' (by unfold burn; fun_prop) (ae_of_all _ fun x=>?_); rw [norm_mul,iron,one_mul]
lemma life (i:Gaia): Integrable (fun x=> burn i x*low F x):=by
 convert (h.whole i).sub (tar h i) using 1; ext1 x; unfold high low; simp only [Pi.sub_apply]; ring
lemma melt : Swift (gorge (low F)-X):=by
 obtain ⟨f,v⟩:= loft h; refine (show Swift (gorge (F ∘ glad)-X-gorge (high F)) from h.deft.sub (by rw [← v]; exact ghoul f))|> fun T=> ?_; -- tune
 convert T using 1; ext1 x; rw [sub_right_comm]; simp only [Pi.sub_apply,gorge, Function.comp_apply]; rw [←mul_sub,← integral_sub (h.whole x) (tar h x)]; congr 2; refine integral_congr_ae (ae_of_all _ fun i=> ?_); simp only [high,low]; ring
end SunPay
variable (P Q: Lattice.PlaqAxes)
open Maxwell
open Matrix
lemma bores(x:Gaia): hornV (glad x)= Boreas x:=by
 let y:Momentum:=fun i=>Complex.I*(glad x i); have he(j:ℕ):snip (glad x) j= BoreV x j:=rfl
 have hs: star y=fun i:Axis=> Complex.I*((-glad x) i):=by funext i; simp only [y,Pi.star_apply,star_mul,glad,tmap,Pi.neg_apply]; push_cast; rw [Complex.star_def, Complex.conj_ofReal]; simp [mul_comm] -- tune
 unfold hornV Herald; rw [Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one]; unfold Boreas; rw [he]; congr 1
 · rw [glacial (x:=x),_root_.zpow_neg,zpow_ofNat]
 change _*(_ : Matrix _ _ ℂ).transpose= _*(wedge 1 y)ᴴ; rw [wedge_adj,hs]
-- common price
@[fun_prop] lemma TemperProv (i:Axis) : HasTemperateGrowth (fun x:Gaia=> glad x i):= (Function.Complex.hasTemperateGrowth_ofReal.comp (EuclideanSpace.proj i).hasTemperateGrowth) -- tune
@[fun_prop] lemma TemperProvN (i:Axis) : HasTemperateGrowth (fun x:Gaia=> (-glad x) i):= (TemperProv i).neg
lemma hessianTrade : SunPay (fun x => regal x (plaquette P) (plaquette Q)) (specter P Q):= by
 let K(i):= regal i (plaquette P) (plaquette Q); let k:=plaquette P; let j:=plaquette Q
 have he(x z:Gaia): burn x z*K (glad z)=inspiration k j 1 x z:=by unfold K regal; rw [gathering,bores,Matrix.smul_apply]; rfl
 refine ⟨fun p=>?_, ?_, ?_⟩
 · change Integrable (fun x=> burn p x*K (glad x)); simp_rw [he, show k=plaquette P from rfl,show j=plaquette Q from rfl, elegant P Q,← Solo_works]; apply Integrable.sub'; exact ((toneBudget one_pos _ _ p).const_mul _|>.sub' ((toneBudget one_pos _ _ p).const_mul _)); exact ((toneBudget one_pos _ _ p).const_mul _|>.sub' ((toneBudget one_pos _ _ p).const_mul _))
 · let V(x:Gaia):=(snip (glad x) 1*(snip (-glad x) 1).transpose) k j; refine ⟨V,?_,fun x=> ?_⟩
   · unfold V snip wedge; simp only [Matrix.mul_apply,Matrix.sum_apply,Matrix.smul_apply,Matrix.transpose_apply,smul_eq_mul]; fun_prop
   unfold regal V hornV Herald; rw [gathering]; simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.smul_apply,smul_eq_mul,glacial]; unfold pet; push_cast; unfold k j; ring
 have ht := frostGauge P Q; unfold hotK at ht; simp_rw [←show ∀ x z:Gaia, burn x z*K (glad z)= inspiration (plaquette P) (plaquette Q) 1 x z from he] at ht; exact ht
lemma matterTrade (a:Axis) : SunPay (incense a) (fettle a):=by
 refine ⟨fun p=>?_, ?_, frostMatter a⟩
 · simp_rw [iceberg]; exact (reek one_pos _ _).const_mul _
 refine ⟨fun x=> 2*glad x a,by fun_prop,fun x=>?_⟩; unfold incense pet; rw [glacial,gathering]; push_cast; ring
end Spring
#print axioms Spring.hessianTrade
#print axioms Spring.matterTrade
end YM.Regis.Circuit.SpringDay
