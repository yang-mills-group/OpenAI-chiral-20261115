import YM.SU5.FiniteGaugeData.Mirage.Boutade
import YM.SU5.FiniteGaugeData.Brique.Net
import YM.SU5.FiniteGaugeData.Largo.Cork
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
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1 ≤ Λ.x)
variable {u v:ℕ→ℕ}{E:ℕ→Family (tent Y h)→ℂ} {I:ℕ→ Family (tent Y h)→ℕ→ℂ}{g r a:ℝ} (K:Universal Y h u v I E) (t:∀ᶠ s:ℕ in atTop, Club Y g s) (p:Travels Λ)
variable {q d j s₀ L J n:ℕ}{S T: Finset Cover}{o:Cover}
local notation "K₁"=> tent Y h
lemma signage (i s:ℕ)(S:Finset Cover)(x:Catalog S)(v:0≤a)(y:Hosp S (side Y i s)) (z:∀ h', ‖sold Y h s i (composeQ K₁ S x) h'‖ ≤ a): ‖x‖ ≤ a:=by
 let h₀ := terrain Y h (Y.ir i) s; let k:=x; exact offered_bound S K₁ x (h₀.symm ▸ y:Hosp S ((K₁).c (momentm Y i s))) (castQ h₀ _ z)
where castQ {A B:Side}(t:A=B)(x:Mark A)(p:∀ v, ‖ship t x v‖ ≤ a) : ∀ v, ‖x v‖ ≤ a:=by subst A; exact p
open scoped Classical
variable {p₁ p₂:ℕ} {C α γ ε:ℝ}{D:Axis→ℕ} {W:Chart o} {F: LinksC→ℂ}
-- transformed scalars.buy
abbrev dutiful(K:Calibration)(f:LinksC→ℂ) := scalar K (f∘Prod.fst)
lemma flagValue (i s:ℕ)(W: LinksC→ℂ): sold Y h s i (dutiful K₁ W)= Mirage.canv (W ∘ onC (side Y i s)):= by
 unfold sold; apply castQ (terrain Y h (Y.ir i) s)
where castQ {n m:Side}(p:n=m): ship p (Mirage.canv (W ∘ onC n)) = Mirage.canv (W ∘ onC m):=by subst m; rfl

-- risk insensitive to choosing ANY extension linear ι.L charges.Price for H.Dep
abbrev Sovereign (S:Finset Cover)(s i:ℕ)(L:Mark (side Y i s)→ₗ[ℂ]ℂ) := ∀ b:Family (tent Y h), InTest (tent Y h) true S false b→ L (sold Y h s i b)=E s b -- E implicit include mention implicit binder
include K
private lemma cost_sub (h1:Continuous F)(h2: Lattice.LocalOn S F)(H:∀ i:LinksC,‖F i‖ ≤ 1) (A: Finset (Face ℤ))(s i:ℕ)(Z:Mark (side Y i s)→ₗ[ℂ]ℂ)(z: Sovereign Y h (E:=E) S s i Z)
 (W:Mark (side Y i s))(t: AtSupport false (region S (side Y i s)) W)(p:Roomy S (side Y i s))(c:0≤C)(g:∀ x,‖W x‖≤ C):
 ∃ X:Family (tent Y h), InTest (tent Y h) true S false X ∧ ∀ k:Fin 1, let Z':= dutiful (tent Y h) F * X; E s X= Z W ∧ E s Z'= Z ((Mirage.canv (F ∘ onC (side Y i s)))*W) ∧ (InTest (tent Y h) true S false Z')∧∀ m x,‖X m x‖ ≤ duration S*C:=by
 obtain ⟨x,hx⟩:= sold_surj Y h S s i p W t; let X:=composeQ K₁ S x; have ht':InTest K₁ true S false X:= compose_t ..; have hp: InTest K₁ true S false (dutiful K₁ F*X):=(InTest.seed (Coeff.fromC _ _ h1 h2)|>.widen).mul ht'; -- tune .. explicit
 have hc := signage Y h i s S x c (roomy_hosp _ p) (fun v=> (hx.symm ▸ g v)); refine ⟨X,ht',fun _=>?_⟩; dsimp only; refine ⟨?_,?_,hp,fun m k=> (compose_price ..).trans (mul_le_mul_of_nonneg_left hc (duration_pos _).le)⟩; rw [←z X ht']; unfold X; rw [hx]; rw [←z (dutiful K₁ F*X) hp,sold_mult, flagValue]; unfold X; rw [hx]
private lemma spell (v:ℝ)(G: Finset (Face ℤ))(q:∀ x:LinksC, ¬alarm G v (x,x)→F x=1): (troubles (tent Y h) G v)*(1-dutiful (tent Y h) F)=1-dutiful (tent Y h) F:=by
 funext m x; let N:= (tent Y h).c m; by_cases v':alarm G v (onC N x.1,onC N x.2); · rw [Pi.mul_apply,Pi.mul_apply,show troubles _ _ _ m x= (1:FC (Single N)) from ?_,one_mul]; unfold troubles scalar strike; rw [if_pos v',one_smul]
 rw [Pi.mul_apply,Pi.mul_apply,show (1- dutiful K₁ F) m x=(0:FC (Single N)) from ?_, mul_zero]; unfold dutiful scalar; dsimp only [Pi.sub_apply, Pi.one_apply,comp_apply]; rw [q _ v', one_smul,sub_self] -- tune
local notation "η" s:max=> hat Λ.R.L Λ.x s
local notation "Ω" s:max=> Pressure.temp (hat Λ.R.L Λ.x s)
include t
lemma atEye (e:0≤g)(C':0≤C)(S:Finset Cover)(p₀:Continuous F)(x:Lattice.LocalOn S F)(H:∀ i:LinksC,‖F i‖≤1)(h1:∃ A:Finset (Face ℤ),∃ t:ℝ, 0<t ∧∀ c:ℝ, c ≤ t→∀ V:LinksC,¬alarm A c (V,V)→ F V=1):∀ᶠ s:ℕ in atTop, ∀ (i:ℕ), Roomy S (side Y i s) → ∀ L:Mark (side Y i s)→ₗ[ℂ]ℂ, Sovereign Y h (E:=E) S s i L→ ∀ X:Mark (side Y i s), AtSupport false (region S (side Y i s)) X → (∀ z,‖X z‖ ≤ C) → ‖L X-L (Mirage.canv (F ∘ onC _)*X)‖ ≤ 1/4:=by
 obtain ⟨A,b,v',g'⟩:= h1; let T:= carpet A∪S; obtain ⟨D,Q⟩: ∃ D:ℕ,∀ i:Axis,∃ p:ℤ,∀ x∈T,p ≤ x i ∧ x i ≤ p+D:= by
    let Z:= T.sup fun i=> univ.sup fun a:Axis=>(i a).natAbs; refine ⟨2*Z,fun a=> ⟨-(Z:ℤ),fun i t=>?_⟩⟩; have he:(i a).natAbs ≤ Z:= (le_sup (f:=fun a:Axis=>(i a).natAbs) (mem_univ _)).trans (le_sup (f:=fun i=>univ.sup fun a:Axis=>(i a).natAbs) t); omega
 let q:= 2*duration S*C; let M:=Real.exp (slopeF Λ.W g * ((4:ℝ)*(D+addgap (tent Y h):ℕ))^4); let W:= hat Λ.R.L Λ.x; have hc:= (duration_pos S); let Z:=dutiful K₁ F; let f:= frost Λ.K.top.clip
 have hw:= Steam.horizons (V:=Λ.V) Λ.x; have hu:Tendsto (fun s=>q*Real.exp (-f (W s))*M) atTop (𝓝 0):=by
    have hv:Tendsto (fun s=> Real.exp (-f (W s))) atTop (𝓝 0):= Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp ((frostT _).comp hw));
    simpa using (hv.const_mul q).mul_const M
 filter_upwards [t, ((show Tendsto Pressure.temp atTop (𝓝 0) from (by simpa using Work.E09.radiusB_temp 0)).comp hw).eventually (ge_mem_nhds v'),hu.eventually (ge_mem_nhds (by norm_num:(0:ℝ)<1/4))] with s v p a i r L t X x' g
 obtain ⟨Y',pV,hκ⟩:=cost_sub Y h K p₀ x H A s i L t X x' r C' g; obtain ⟨X',hNew,G,Z'⟩:= hκ 0; let x₀:= Y' - Z*Y'
 have hv:(1-Z)*Y'=x₀:=by rw [_root_.sub_mul,one_mul]
 obtain ⟨u,k⟩:=together_sub Y h K S s _ _ pV G -- `h` shadow here.
 have hc: ‖E s (troubles (tent Y h) A (Ω s)*x₀)‖≤ q*Real.exp (-f (W s))*M:= coverage A Y h K e v u (by unfold q; positivity) (fun n x=>?_ ) D Q; swap
 · change ‖x₀ n x‖ ≤_; rw [←hv,Pi.mul_apply,Pi.mul_apply]; refine (norm_mul_le ..).trans ((mul_le_mul ?_ (Z' n x) (norm_nonneg _) (show (0:ℝ) ≤ 2 by norm_num)).trans (mul_assoc ..).ge); refine (norm_sub_le ..).trans ?_ -- choose progress
   have hz: ‖Z n x‖ ≤ 1:=by unfold Z dutiful scalar; simp only [norm_smul, norm_one, mul_one, Function.comp_apply]; exact H _
   change ‖(1:FC (Single _))‖+_≤_; rw [norm_one]; linarith
 rw [←hv,←mul_assoc,show troubles (tent Y h) A (Ω s) * (1-Z)= (1-Z) from spell Y h K (Ω s) A (g' (Ω s) p),hv] at hc; exact (by rw [←X',←hNew,←k]; exact hc.trans a)
end Chaperone
end YM.CF.Buffered.Afterglow.Hierarchy.Quest
