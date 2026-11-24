import YM.SU5.FiniteGaugeData.Tower.EndTrain
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis
section baggage
variable {K:Calibration} (j:Axis)(w:ℤ)
structure BQueue(S:Finset Cover)(F:ℕ→Family K)(x:Family K):Prop where
 whereTo(i:ℕ):InTest K true S false (F i)
 landing :InTest K true S false x
 bdd:∃C:ℝ,0 < C∧pay x C∧∀ᶠ i:ℕ in atTop,pay (F i) C
 saved:∀e:ℝ,0<e→∀ᶠ i:ℕ in atTop,pay (F i-x) e
variable {S T:Finset Cover}{F G:ℕ→Family K}{x y:Family K}
namespace BQueue
lemma stay {x:Family K}(h:InTest K true S false x){C:ℝ}(p:0<C)(t:pay x C): BQueue S (fun _=>x) x:=⟨fun _=>h,h,⟨C,p,t,Eventually.of_forall fun _=>t⟩,fun e v=> Eventually.of_forall fun i s _ => by rw [sub_self]; exact (show ‖(0:Fock.FC (Single (K.c s)))‖=(0:ℝ) from norm_zero).le.trans v.le⟩ -- tune norm
lemma revolve(v:ℤ)(p:BQueue S F x): BQueue (reflectedBox j v S) (fun i=>mirror K j v (F i)) (mirror K j v x):=by
 obtain ⟨t,h,⟨C,f,a,b⟩,e⟩:=p
 refine ⟨fun _=>axial K j _ (t _),axial K j _ h,⟨C,f,pay_flips K a _ _,b.mono fun i h=>pay_flips K h j v⟩,fun k vk=>?_⟩
 filter_upwards [e k vk] with i hx
 rw [show mirror K j v (F i)-mirror K j v x=mirror K j v (F i-x) from ?_]
 · exact pay_flips K hx j v
 rw [sub_eq_add_neg (F i), ←neg_one_smul ℂ x, mirror_plus,mirror_scale, star_neg,star_one,neg_one_smul,←sub_eq_add_neg]
lemma station(v:ℤ)(p:BQueue S F x):BQueue (plow K j v S) (fun i=> relocate K j v (F i)) (relocate K j v x):=by
 obtain ⟨t,h,⟨C,f,a,b⟩,e⟩:=p
 refine ⟨fun _=>flow_port K j _ (t _),flow_port K j _ h,⟨C,f,chime_pay _ _ _ _ a,b.mono fun i h=>chime_pay _ _ _ _ h⟩,fun k vk=>?_⟩
 filter_upwards [e k vk] with i hx
 rw [show relocate K j v (F i)-relocate K j v x=relocate K j v (F i-x) from ?_]
 · exact chime_pay K j _ k hx
 unfold relocate; rw [sub_eq_add_neg (F i), ←neg_one_smul ℂ x,chime_plus,chime_scale,neg_one_smul,←sub_eq_add_neg]
lemma multiply (a:BQueue S F x)(b:BQueue T G y): BQueue (S∪T) (fun i=> F i*G i) (x*y):=by
 obtain ⟨t,h,⟨C,f,a,b'⟩,e⟩:=a; obtain ⟨u,h',⟨B,g,c,d⟩,e'⟩:=b
 refine ⟨fun i=>((t i).mono subset_union_left).mul ((u i).mono subset_union_right),(h.mono subset_union_left).mul (h'.mono subset_union_right),⟨C*B,by positivity,pay_mul a c,(b'.and d).mono fun i ⟨p,q⟩=>pay_mul p q⟩,fun i v=>?_⟩
 let ε:=i/(2*max C B); have he:0<ε:= by unfold ε; positivity
 have ht:ε*B+C*ε ≤ i:=by
    have k:ε*(2*max C B)=i:=div_mul_cancel₀ _ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left (le_max_right C B) he.le,mul_le_mul_of_nonneg_right (le_max_left C B) he.le]
 filter_upwards [b',e ε he,e' ε he] with n m w j
 have hx: F n*G n-x*y= (F n -x)*y+F n*(G n-y):=by noncomm_ring
 rw [hx]
 intro u r; specialize m u r; specialize w u r; specialize j u r; specialize c u r
 simp only [Pi.sub_apply,Pi.add_apply, Pi.mul_apply] at *
 refine le_trans ((norm_add_le ..).trans (add_le_add ((norm_mul_le ..).trans ?_) ((norm_mul_le ..).trans ?_))) ht
 · exact mul_le_mul w c (norm_nonneg _) he.le
 exact mul_le_mul m j (norm_nonneg _) f.le

lemma flipped(n:ℕ)(a:BQueue S F x):∃ T:Finset Cover,BQueue T (fun i=>toward K j w (F i) n) (toward K j w x n):=by
 induction n with
 | zero=>exact ⟨_,a⟩
 | succ n ih=>obtain ⟨T,p⟩:=ih; exact ⟨_,p.revolve j _⟩
lemma chambersS(n:ℕ)(v:ℤ)(a:BQueue S F x)(b:BQueue T G y):∃ T:Finset Cover,BQueue T (fun i=>chambers j w v (F i) (G i) n) (chambers j w v x y n):=by
 suffices h:∃ T:Finset Cover,BQueue T (fun i=> lace K j w (F i) (G i) n) (lace K j w x y n) by obtain ⟨T,h⟩:=h; exact ⟨_,(((h.revolve j 0).multiply h).station j v)⟩
 induction n with
 | zero=> exact ⟨T,b⟩
 | succ n ih=> obtain ⟨T,h⟩:=ih; obtain ⟨A,p⟩:=a.flipped j w n; exact ⟨_,p.multiply (h.station j w)⟩
end BQueue
end baggage
section drives
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
local notation "L₀"=>Λ.R.L.val
local notation "m" n:max s:max=>momentm Y n s
local notation "T₀" n:max s:max=> Journey.side Y n s
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}(Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)
variable (j:Axis)(w:ℕ)(f:Family (tent Y H))(S:Finset Cover)(t:InTest (tent Y H) true S false f)(hB:Between (tent Y H) j 0 (ruler Λ.block*w) S)
local notation "π" r:max=>i (a r)
local notation "ζ" r:max=> k (b r)
local notation "Z" u:max r:max=> train Y H s u (π r) (ζ r) S f
local notation "W" t:max=> volumeAround Λ l t S
local notation "uM" t:max=> (L₀^t*w)
local notation "b₀"=>ruler Λ.block
variable (Qt : Clipped Y H (i∘a) (k∘b))(hw:0 < w)
include V Q
lemma heatwave{f:Family K}(h:TestFamily K true f):Tendsto (fun r=> hot Y H s (π r) (ζ r) f) atTop (𝓝 (E s f)):=by
 -- path via Coherent.gate Fr, use toll to transfer sharp, diet, or `Rpaths` expects every r of V occupation. can extend z off subseq; easier implement sharp_E errors from Coherent.implements+Y.rate
 obtain ⟨S,x⟩:=h.paid; obtain ⟨u,p⟩:=valuation Y H x; have H0:pay f u:=p; have hu:0 ≤ u:=pay_nonneg H0
 refine Metric.tendsto_nhds.mpr fun ε e=>?_
 obtain ⟨C,t,q⟩:=Q.implements s S; let d:=ε/(3*(u+1)); have z:0 < d:=div_pos e (by positivity); have ht:d*u< ε/2:=by have hp:d*(3*(u+1))=ε:=div_mul_cancel₀ _ (by positivity); nlinarith
 have he:Tendsto (fun r=> ζ r) atTop atTop:= (V.pick.grow_k.comp Q.growsB).tendsto_atTop
 filter_upwards [he.eventually (Journey.rate Y H s h (ε/3) (by positivity)), q d z,Q.finance s] with i c a b
 rw [dist_eq_norm]; let H':= sharp Y H s (π i) (ζ i) f
 -- i shadow means notation macro index resolves? i binder, hygienic old index
 have h1:=norm_sub_le_norm_sub_add_norm_sub (hot Y H s (π i) (ζ i) f) H' (E s f)
 have h2:=c (π i) b.depth
 obtain ⟨X,XB,T,Hg,hG,v⟩:= a f x u H0
 unfold H' at *; rw [norm_sub_rev] at h2; linarith

lemma hot_deck {F:ℕ→Family K}(p:BQueue S F f): Tendsto (fun i=>hot Y H s (π i) (ζ i) (F i)) atTop (𝓝 (E s f)):=by
 obtain ⟨g,h,_,x⟩:=p; let u:=heatwave Y H V s Q (aux_test h)
 obtain ⟨d,v⟩:=Tower.sizes S
 let D':=Grip Y H s d; have ht:0≤ D':= (Real.exp_pos _).le
 refine Metric.tendsto_nhds.mpr fun ε e=>?_
 let C:=ε/(2*(D'+1)); have hC:0<C:=div_pos e (by positivity)
 have hx:D'*C<ε/2:=by have hp:C*(2*(D'+1))=ε:=div_mul_cancel₀ _ (by positivity); nlinarith
 filter_upwards [x C hC, V.pick.grow_i.tendsto_atTop.comp Q.growsA.tendsto_atTop|>.eventually (tandem Y H s d), Q.finance s,Metric.tendsto_nhds.mp u (ε/2) (by positivity)] with i hp hq p t
 let I0:=F i-f
 have he: ‖hot Y H s (π i) (ζ i) I0‖ ≤D'*C:=by
    have ht':CompactArc ∅ d:=fun i=>⟨0,by simp⟩; have hw:= hq (ζ i) p (InTest.subOp (g i) h) (show InTest K true ∅ false 1 from InTest.one) v ht' C 1 hp (fun _ _=>by exact norm_one.le)
    simpa only [mul_one,I0,D',Function.comp_apply] using hw
 rw [show hot Y H s (π i) (ζ i) I0= hot Y H s (π i) (ζ i) (F i)-hot Y H s (π i) (ζ i) f from ?_] at he
 · exact lt_of_le_of_lt (dist_triangle _ (hot Y H s (π i) (ζ i) f) _) (by rw [dist_eq_norm] ; linarith)
 unfold I0; rw [sub_eq_add_neg,← neg_one_smul ℂ f, hot_add Y H s (aux_test (g i)) ((aux_test h).scale _) p,hot_mul Y H s _ p]; simp [sub_eq_add_neg]
include t
lemma queue_easy(r:ℕ):
 BQueue (W r) (fun i=> Z r i) (stream Y H D s r f):=by
 let T:= stream Y H D s r f
 obtain ⟨A,h,hv⟩:= fares Y H s Q S r
 obtain ⟨c,p⟩:= valuation Y H t; have hc:0<c+1:=add_pos_of_nonneg_of_pos (pay_nonneg (F:=f) p) zero_lt_one
 have hp:pay f (c+1):=fun i x=> (p i x).trans (by linarith)
 have ht(ε:ℝ)(h:0 < ε):∀ᶠ n:ℕ in atTop,pay T (A*(c+1))∧pay (Z r n) (A*(c+1))∧pay (Z r n-T) ε:=by
    let d:=ε/(c+1); filter_upwards [hv d (div_pos h hc)] with i he
    obtain ⟨p,t,h,_⟩:=he f t (c+1) hp
    exact ⟨p,t,by unfold d at h; rw [div_mul_cancel₀ _ hc.ne'] at h; exact h⟩
 exact ⟨fun i=>prepared_train Y H s S r _ _ t,(proceeds Y H Q.circuit s r t).1,⟨A*(c+1),by positivity,by obtain ⟨n,c⟩:=(ht 1 one_pos).exists; exact c.1,(ht 1 one_pos).mono fun _ h=>h.2.1 ⟩,fun e p=>(ht e p).mono (fun i w=>w.2.2)⟩
include hB Qt hw
lemma baggageH:∃B:ℝ, 0<B∧∀ (r d:ℕ)(T:Finset Cover)(A:ℤ)(h:0 ≤ A)(x:Family (tent Y H)),InTest K true T false x→Between (tent Y H) j (2*(ruler Λ.block*(uM r))) A T→ CompactArc T d→∀ C:ℝ,0<C→pay x C→
 ∀ n:ℕ, ‖E (s+r) (chambers j (uM r) 0 (stream Y H D s r f) x n)‖≤ wages K (duetCharge Y (s+r)) d A C * B^n:=by
 obtain ⟨B,y,p⟩:= interpolant Y H V s Q j w f S t hB Qt hw
 refine ⟨B,y,fun r d T A h x u e v C Hc hp n=>?_⟩
 obtain ⟨S1,d'⟩:= BQueue.chambersS j (uM r) n 0 (queue_easy Y H V s Q f S t r) (BQueue.stay u Hc hp)
 have hr:= (hot_deck Y H V (s+r) Q _ S1 d').norm
 apply le_of_tendsto hr; exact (p r n d A C h).mono fun i w=> w n le_rfl x T u e v hp
end drives
end YM.CF.Buffered.Afterglow.Tower.SlabMark
#print axioms YM.CF.Buffered.Afterglow.Tower.SlabMark.baggageH
