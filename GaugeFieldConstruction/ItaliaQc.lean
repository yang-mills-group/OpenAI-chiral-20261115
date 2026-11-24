import GaugeFieldConstruction.CotogaQc
/-!
# Slot calculus continued. finite price combinations. Ink and generic costs
-/
set_option autoImplicit false
set_option synthInstance.maxSize 7800
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Hulse
open Calibration Raw Cauchy LabelAction Empire Fathom Payroll Function Filter Set TopologicalSpace Analysis MeasureTheory Points Bulb Palace Salam
open Floor Sailing Module
open scoped Topology BigOperators ContDiff Classical
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
local notation "l"=> UV five
variable {n : ℕ} {S:City} (Y:AreaQc S)
section
variable {X J:Type*}[AddCommGroup X][Module ℂ X]
-- sum closed any.
lemma prismDoseQc [Module.Finite ℂ X] (E:X→ₗ[ℂ] J→ℂ)(h:Injective E) (f:J→ℂ)
   (p:∀ r:Finset J,∀ w:J→ℂ,(∀ x:X,∑ i∈r,w i*E x i=0)→∑ i∈r,w i*f i=0):∃ x:X,∀ i,E x i=f i:=by
 let G:=Finsupp.linearCombination ℂ (feel E)
 have he:G.range=⊤:= (Finsupp.range_linearCombination ℂ).trans (replaces E h)
 obtain ⟨L,H⟩:= G.exists_rightInverse_of_surjective he
 let K:=Finsupp.linearCombination ℂ f; let v:=(evalEquiv ℂ X).symm (K ∘ₗ L)
 have hx(c:J→₀ℂ)(e:G c=0):K c=0:=by
    apply p c.support c; intro x; have ht:=LinearMap.congr_fun e x; unfold G at ht; rw [Finsupp.linearCombination_apply,Finsupp.sum,LinearMap.sum_apply] at ht; exact ht
 refine ⟨v,fun i=>?_⟩
 change feel E i v=_; rw [Module.apply_evalEquiv_symm_apply]; refine sub_eq_zero.mp ?_; change K (L (feel E i))-f i=0
 have ht:=hx (L (feel E i)-Finsupp.single i 1) (by rw [map_sub, ←LinearMap.comp_apply,H]; simp [G]); rwa[map_sub,show K (Finsupp.single i 1)=f i from (by simp[K])] at ht
-- mesh pairing and penalty.Mosaic wrappers
end
variable {X : Type*} [AddCommGroup X][Module ℂ X](L : X→ₗ[ℂ] UV five) (A B:UV five)
structure NickleQc where
   e:ℕ→ℝ
   positive:∀ i,0<e i
   small:Tendsto e atTop (𝓝 0)
variable (w:ℕ→ℝ)(N:NickleQc)
def DayQc (ρ:HintQc)(A B:UV five): Points (ρ.n+2)→ℂ:= Y.fee (ρ.n+2) (Fathom.add B (Fathom.add A ρ.x))
noncomputable abbrev BillQc (ρ:HintQc)(A B:UV five)(y:E4):ℂ:= PieceQc (DayQc Y ρ A B) ρ.f y
-- supplies for annihilator any finite.
structure BloomQc :Prop where
   fee {J:Type} (I:Finset J)(c:J→HintQc)(a:J→ℂ)(h:∀ P:X,∑ j∈I,a j* DriftQc S L P (c j)=0): ∃ Q:ℝ,0≤Q∧∀ᶠ i in atTop, ∀ y:E4, AnnulusQc (N.e i) y→guild y→ ‖∑ j∈I,a j*BillQc Y (c j) A B y‖ ≤ Q*w i -- include params structure Lean order
-- mesh estimates directly imply via continuity in y and dense consultations
structure FundsQc (L : X→ₗ[ℂ] UV five)(N: NickleQc)(w:ℕ→ℝ)(Y:AreaQc S)(A B:UV five):Prop where
 positive:∀ i,0≤ w i
 mesh (I:Finset HintQc): ∀ᶠ i in atTop, ∃ s:Set E4,
   (∀ x:E4,guild x→AnnulusQc (N.e i) x→x∈closure s)∧∀ x∈ s,AnnulusQc (N.e i) x ∧∃ F:X,
       ∀ j∈I, ∀ᵐ v:Points (j.n+1), v∈tsupport j.f→ ‖DayQc Y j A B (LensQc x v)- Y.fee _ (Fathom.add (L F) j.x) v‖ ≤ w i
lemma zephyrLensQc (x:HintQc)(y:E4)(u:guild y) (h:∀ z∈tsupport x.f,LensQc y z∈conf (x.n+2)): ContinuousAt (BillQc Y x A B) y:= MoneyLateQc x.f _ (Y.reg ..) y u h
noncomputable def L1BillQc (x:HintQc):ℝ:= ∫ t:Points (x.n+1), ‖x.f t‖
lemma BootTagQc (F:FundsQc L N w Y A B): BloomQc Y L A B w N:=by -- infer order tune
 constructor; intro J I c a p; let H(j):= L1BillQc (c j); let Q:=∑ i∈I, ‖a i‖*H i
 have hi(j): Integrable (fun t:Points ((c j).n+1)=> ‖(c j).f t‖):=((c j).f.continuous.integrable_of_hasCompactSupport (c j).f.hasCompactSupport).norm
 have hp(j):0≤H j:=integral_nonneg (fun _=>norm_nonneg _)
 refine ⟨Q, Finset.sum_nonneg (fun i _=> mul_nonneg (norm_nonneg _) (hp _)),?_⟩
 let I':=I.image c
 filter_upwards [F.mesh I',(eventually_all_finset I).mpr (fun j _=>fillAnnQc (c j).f N.e N.positive N.small)] with i v h -- tune
 intro y r t
 obtain ⟨s,T,Y'⟩:=v; have hl:y ∈ closure s:=T y t r
 let K:= fun x=> ∑ j∈I,a j*BillQc Y (c j) A B x
 have he:ContinuousAt (fun x=> ‖K x‖) y:= (show ContinuousAt K y from tendsto_finsetSum _ (fun j k=> continuousAt_const.mul (MoneyLateQc (c j).f _ (Y.reg ..) y t (h j k y r)))).norm
 have hHi(x)(u:x∈s): ‖K x‖ ≤ Q*w i:=by
    obtain ⟨g,R,Z⟩:=Y' x u; have H0P(j)(k:j∈I): ‖BillQc Y (c j) A B x-DriftQc S L R (c j)‖ ≤ H j*w i:=by
       let B1:= (c j); let t:= B1.f; let D(v:Points (B1.n+1)):=DayQc Y B1 A B (LensQc x v); let E:=Y.fee _ (Fathom.add (L R) B1.x); rw [DriftCostQc,Y.price]; change ‖ (∫ v,t v* D v)-(∫ v,t v*E v)‖≤_
       have hg:Integrable (fun v=> t v*D v):=BondLensQc t _ (Y.reg ..) x (h j k x g); have hf: Integrable (fun v=> t v*E v):= BondCostQc t E (Y.reg ..)
       rw[←integral_sub hg hf]; apply le_trans (norm_integral_le_integral_norm _); rw [show H j*w i=∫ v, ‖t v‖*w i from (integral_mul_const ..).symm]; refine integral_mono_ae (hg.sub hf).norm ((hi j).mul_const _) ?_
       filter_upwards [Z _ (Finset.mem_image_of_mem c k)] with i' p'; by_cases h:i'∈tsupport t; · rw [←mul_sub, norm_mul (t i')]; exact mul_le_mul_of_nonneg_left (p' h) (norm_nonneg _)
       rw [image_eq_zero_of_notMem_tsupport h]; simp
    rw [show K x=∑ j∈I,a j*(BillQc Y (c j) A B x-DriftQc S L R (c j)) from (by simp_rw [mul_sub, Finset.sum_sub_distrib,p R,sub_zero]; rfl),show Q*w i=∑ j∈I,(‖a j‖*H j)*w i from (Finset.sum_mul ..)]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j k=>by rw [norm_mul,mul_assoc]; exact mul_le_mul_of_nonneg_left (H0P j k) (norm_nonneg _)) -- h arg hole
 exact isClosed_Iic.mem_of_frequently_of_tendsto ((mem_closure_iff_frequently.mp hl).mono (fun x k=> hHi x k)) he -- tune
#print axioms BootTagQc
#print axioms prismDoseQc
end YM.GaugeFieldConstruction.Ember.Hulse
