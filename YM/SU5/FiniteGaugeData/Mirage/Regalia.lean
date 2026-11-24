import YM.SU5.FiniteGaugeData.Mirage.Lent
import YM.SU5.FiniteGaugeData.Mirage.Hasty
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 380000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Quest
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Heat Brique Window.Brique Journey Py Py.Rate LocalLimit Preparation FullBill Steam Vale
namespace Chaperone
open Tint Charm
open Playlist Show Largo
variable {Λ: Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
variable {u v:ℕ→ℕ}{E:ℕ→ Family (tent Y h)→ℂ} {I:ℕ→ Family (tent Y h)→ℕ→ℂ}
set_option quotPrecheck false
local notation "P"=> tent Y h
variable (K:Universal Y h u v I E) (s:ℕ) (T S A: Finset Cover) (σ τ: Window.Family)
local notation "Κ"=> tent Y h
variable {J:Call Λ l}{W:Wicket Λ l}(R:Rolled Y h u v W J)
local notation "L"=> Charm.W (tent Y h)
-- strict proof full centered reflections at any rolled resource or chosen s beyond limit. Adjoint positivity of multi algebra embeddings. no positivity assumptions across overlapping factor contacts; use supporting l buffer. 
variable {x y:Family (tent Y h)}(p: Operon Y h (E s) A S x) (c:Haze (tent Y h) σ τ S x) (Q:Finset (Face ℤ))(u':carpet Q⊆ S)
include p c K
include R in
theorem OperaStrong (t:Ahead 3 0 (reserve Λ l) S)(e:Ahead 3 0 (reserve Λ l) (refract 3 0 A)) :
 0 < E s (vaultF Κ x 3 (E s x) (E s x)):=by
 obtain ⟨f,t',hC,q⟩:= p.leftQ; let X:L:=⟨x,c.fits⟩; let F:L:=⟨f,⟨⟨⟨A,t'⟩, by simp⟩,hC⟩⟩; let H:= X-E s x • 1; let G:= beams Y h K R 3 0;  have hT:S⊆ S:= Subset.refl _ -- remove dummy after
 have hv: Locator (tent Y h) H S:=by rw [show H= X+(-(E s x)) • 1 by unfold H; rw [neg_smul, sub_eq_add_neg]]; exact locate_sum Κ _ (c.funds.widen : Locator Κ X S) (locate_scale Κ _ _ (locate_one ..))
 let X':= fire Κ 3 0 F; let P0:Vect Y h 3 0:=⟨credit_at Y h s H,seatPulse Y h _ hv t s⟩; let f0:Vect Y h 3 0:=⟨credit_at Y h s X', seatPulse Y h _ (locate_cold _ A 3 _ (show Locator _ F A from t')) e s⟩; have hh: frameQ Λ 0 s=0:=by rw [frame_cash]; simp [gaugeShift]
 have hk(k Z:L): chorusRead Y h K R (intermezzo Κ 3 (frameQ Λ 0) (credit_at Y h s k)*credit_at Y h s Z)=sight Y h s K (fire Κ 3 0 k* Z):= by rw [past_choice,Show.toll,pulse_E,hh]; rfl
 have he: G f0 P0≠0:=by
    change chorusRead Y h K R (intermezzo (tent Y h) 3 (frameQ Λ 0) (credit_at Y h s X')*credit_at Y h s H)≠0; unfold X'; rw [hk, burning_ice]; unfold H; rw [_root_.mul_sub, Algebra.mul_smul_comm, mul_one, map_sub,map_smul]; change E s (f*x)-E s x * E s f ≠0; rw [mul_comm (E s x)]; exact q
 have hp:0 < G P0 P0:=by
    apply lt_of_le_of_ne (gleam Y h K R 3 0 P0); intro e; apply he; let A0 := Matrix.of fun i j:Fin 2=> G (![f0,P0] i) (![f0,P0] j); let r:=(screenshots G (gleam Y h K R 3 0)).2 (Fin 2) ![f0,P0]; let u: Fin 2→ℂ:=![0,1]; have w:A0.mulVec u=0:= (r.dotProduct_mulVec_zero_iff u).1 (by simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, u]; exact e.symm); simpa [A0,u, Fin.sum_univ_succ, Matrix.mulVec, dotProduct] using congr_fun w 0
 change 0 < chorusRead Y h K R (intermezzo (tent Y h) 3 (frameQ Λ 0) (credit_at Y h s H)*credit_at Y h s H) at hp; rw [hk] at hp; exact hp
omit c p
include u'
-- taper retains BOTH covariance & nonzero expectation. also set supports preserved. use general Wide DCT at combined scope. Deco duty moves H when chopping.
omit K in
private lemma lit_s (c:Haze (tent Y h) σ τ S x)(r:ℝ) : Haze (tent Y h) σ τ S (shineB r Q Κ* x):=by
 have hk {l : List Cover}{U :Finset Cover} {F:Family Κ}{τ:Window.Family} (t:StencilB Κ σ τ U S l F):StencilB Κ σ τ U S l (shineB r Q Κ *F):= {
  t with
  output :=t.output.gauge _ ((amber_cost ..).mono u')
  kin:= fun m g x =>by
    simp only [Pi.mul_apply,map_mul,t.kin m g]; apply congrArg (fun i' => i' * (twist (quantU (tradew ((Κ).c m) g)) (F m x)))
    unfold shineB scalar; dsimp only [Function.comp_apply]; rw [twist_scalar,map_one]; refine congrArg (fun x:ℂ=> x • _) ?_; unfold amber; apply congrArg ((↑):ℝ→ℂ); apply prod_congr rfl; intro z k; rw [← press_face z (simultaneous g x),← press_face z x]; change max 0 (min 1 (SU.group.chord (faceValue (Lattice.gauge _ x.1) _)/_ -1))=_; rw [face_gauge,SU.group.chord_conj] }
 induction c with
 | oneB v=> exact .oneB (hk v)
 | twoB v=> exact .twoB (hk v)
 | plus _ _ a b=> rw [mul_add]; exact a.plus b
 | mul _ z a=> rw [Algebra.mul_smul_comm]; exact a.mul _
include p c
lemma retentive (e:E s x≠0):∃ r F,Luster Κ F Q r ∧ E s F ≠0 ∧ Operon Y h (E s) A S F ∧ Haze Κ σ τ S F:=by
 obtain ⟨v,b,l,u⟩:= p.leftQ; let f(i:ℕ) := shineB (germB i) Q Κ; let g(i:ℕ):= f i* x
 have he: TestFamily Κ true v:= ⟨⟨A,b⟩,by simp⟩; let X:=A ∪ S; let w:= v*x; have t (i:ℕ): InTest Κ false S false (f i):= .seed ((amber_cost _ Q).mono u'); let K₁:= p.rightQ; let β:= Chaperone.soles Y h s Q ((b.mono (show A⊆X from Finset.subset_union_left)).mul (K₁.mono subset_union_right)) (u'.trans Finset.subset_union_right) K; let J:= Chaperone.soles Y h s Q p.rightQ u' K
 have hx: ∀ i:ℕ, f i * (v*x)=v*g i:=fun i=>by rw [←mul_assoc, (he.comm ⟨⟨S,(t i).widen⟩,by simp⟩).symm, mul_assoc]; -- tune Test of f.no inference.
 have ht:Tendsto (fun i=> decor (E s) v (g i)) atTop (𝓝 (decor (E s) v x)):=by
    have hv:=β.sub (J.const_mul (E s v)); change Tendsto (fun i=> E s (f i* (v*x))- E s v*E s (g i)) _ _ at hv; simp_rw [hx] at hv; exact hv
 obtain ⟨i,d,t'⟩:= ((ht.eventually_ne u).and (J.eventually_ne e)).exists; let Y':=lit_s Y h S σ τ Q u' c (germB i); exact ⟨germB i,g i,Copse.lives _ (Real.exp_pos _) Κ Q x,t',⟨Y'.funds.widen,v,b,l,d⟩,Y'⟩
omit u'
include K p c
lemma kombine {l₀:List Cover}(e:StencilB Κ σ σ T S l₀ y)(P':E s y≠0): ∃ F, Haze Κ σ τ S F ∧ E s F≠0 ∧ Operon Y h (E s) A S F:=by
 by_cases h':E s x=0; swap; · exact ⟨x,c,h',p⟩
 obtain ⟨f,t,hC,v⟩:=p.leftQ; by_cases k:decor (E s) f y=0; swap; · exact ⟨y,.oneB e,P',e.tierB.widen, f,t,hC,k⟩
 let q:= c.plus (Haze.oneB (τ:=τ) e); let O:= sight Y h s K; let F:L:=⟨f,⟨⟨⟨A,t⟩,by simp⟩,hC⟩⟩; let X:L:=⟨x,c.fits⟩; let Z:L:=⟨y,(Haze.oneB (τ:=τ) e).fits⟩; have h₀:E s (x+y)= E s x+ E s y:=map_add O X Z
 refine ⟨x+y,q, by rw [h₀,h',zero_add]; exact P', q.funds.widen,f,t,hC,?_⟩; unfold decor; rw [h₀,show E s (f*(x+y))=E s (f*x)+E s (f*y) from ?_, mul_add]; swap; · change O (F*(X+Z))=O (F*X)+ O (F*Z); rw [mul_add,map_add]
 unfold decor at k v; contrapose! v; linear_combination v - k
#print axioms kombine
#print axioms OperaStrong
#check kombine
#check OperaStrong
#check retentive
#check RealVent
end Chaperone
end YM.CF.Buffered.Afterglow.Hierarchy.Quest
