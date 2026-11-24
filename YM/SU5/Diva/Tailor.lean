import YM.SU5.Diva.Updraft
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
open CF.Velvet CF.Pannier.Chancel
open Spine TopologicalSpace
variable {e x:ℝ}
abbrev uniform (P:Spine)(R:P.Register)(X:Supplier)(e v:ℝ):= Vinyl P R X e v ∧ P.par.Attic
lemma installation (X:Supplier)(e u:ℝ)(p:0<u):∃ (P:Spine) (R:P.Register), uniform P R X e u:=by
  obtain ⟨x,c,q⟩:= Papal.audit_weather 4 (by decide)
  obtain ⟨Λ,l,Z,v,pL,S,Q,A0,K,H,Y,_,_,_,k,d,w,C,t,a,k',I,E,L,B,T',t',W,A⟩:= Papal.elite_attic e (min x u) (lt_min c p) X
  let V:= W.univ_; obtain ⟨G⟩:= extend_ground Y H V; let P:Spine:=⟨Λ,l,Y,H,a,k',I,E,V,G⟩; obtain ⟨x',v₀⟩:=q Λ.d Λ.dpos.le (pL.trans (min_le_left ..))
  exact ⟨P,⟨(L,B,T',t'),W⟩,⟨K,v,pL.trans (min_le_right ..),A, ⟨k,d,w,Z,C,t,Q,S⟩,x', (Λ.kJ.symm ▸ v₀: Procurement Λ.K.j x' Λ.d)⟩, A0⟩
variable {P:Spine}{R:P.Register}{X:Supplier}(T:uniform P R X e x)
include T
open Lamour.Bridge.Celeste
open Py.Rate.LocalLimit.Papal (Weaver household)
lemma throne_size {ι:Type}[Fintype ι]{α:ℝ}(Y:Ladle 4 P.par.block (reserve P.par P.width) α ι) (p:0<α)(h:α≤1/2):∃ k,Papal.Lecture P.run P.large Y k (4*Real.exp 1*(4*α)):=by
 obtain ⟨q,d,w,Z,C,v,t,_⟩:= T.1.paper; exact Papal.salon_serve P.run P.large t T.1.nerve T.2 Y p h
omit T
variable (P)
abbrev discount (n:ℕ)(a:ℝ):=a^2*(2:ℝ)⁻¹^n
/-- Expenses for a finite menu. -/
abbrev basePrice(a:ℝ):=4*Real.exp 1*(4*a)
def Fits (ι :Type)[Fintype ι](n:ℕ)(e t:ℝ):Prop:= 0< t ∧ t ≤ 1/2 ∧ basePrice t ≤ e ∧ (Fintype.card ι:ℝ)*basePrice t ≤ discount n e
lemma stablePrice (ι :Type)[Fintype ι](n:ℕ)(u:0<e):∀ᶠ t:ℝ in 𝓝[>] 0, Fits ι n e t:=by
 let Y(x:ℝ):=(Fintype.card ι:ℝ)*basePrice x; have hx:Continuous basePrice:=by unfold basePrice; fun_prop; -- indent
 let a:=discount n e; have ht:a>0:=by unfold a discount; positivity
 have hz:Continuous Y:=continuous_const.mul hx
 filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds (hx.continuousAt.tendsto.eventually (ge_mem_nhds (show basePrice 0<e by simpa only [basePrice,mul_zero] using u))),eventually_nhdsWithin_of_eventually_nhds (hz.continuousAt.tendsto.eventually (ge_mem_nhds (show Y 0<a by simpa [Y,basePrice] using ht))), eventually_nhdsWithin_of_eventually_nhds (ge_mem_nhds (show (0:ℝ)<1/2 by norm_num))] with x i a b c; exact ⟨i,c,a,b⟩
lemma prognosis {X:Type}[MeasurableSpace X][TopologicalSpace X][BorelSpace X][CompactSpace X]{μ:Measure X}[IsProbabilityMeasure μ] {I:ℕ→Type}[∀n,Fintype (I n)] (S:∀ n:ℕ, I n→X→ℝ)(B:ℕ→ℝ)(H:∀ n i,Continuous (S n i))(u:∀ n i x,0≤ S n i x)(e:ℕ→ℝ)(p:∀ n,0<e n)(t:∀ n i, (∫ x,S n i x ∂μ)≤ B n)(w:∀ n,(Fintype.card (I n):ℝ)* B n ≤ discount n (e n)):∀ᵐ x ∂μ,∀ᶠ n in atTop,∀i,S n i x < (e n)^2:=by
 let D(n:ℕ)(x:X):=∑ i,S n i x; have ht(n):Continuous (D n):=continuous_finsetSum _ (fun i _=> H n i)
 have he(n):(∫ x,D n x ∂μ)≤ discount n (e n):=by unfold D; rw [integral_finsetSum _ (fun i _=> (H n i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]; apply (sum_le_sum (fun i _=>t n i)).trans; rw [sum_const,nsmul_eq_mul,card_univ]; exact w n
 let X(n:ℕ):= {x:X | (e n)^2 ≤ D n x}; let f(i:ℕ):ℝ≥0∞:=2⁻¹^i; have hv(i): μ (X i)≤ f i:=by
    have hp:=p i; rw [← ENNReal.toReal_le_toReal (by finiteness) (by unfold f; finiteness), show (f i).toReal=(2:ℝ)⁻¹^i from (by unfold f; simp)]
    exact (le_of_mul_le_mul_left ((mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall (p:=fun x=> 0≤ D i x) (fun x=>sum_nonneg (fun v _=>u i v x))) ((ht i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) _).trans (he i)) (show (e i)^2 > 0 from pow_pos hp _)) -- implicit matching
 filter_upwards [MeasureTheory.ae_eventually_notMem (lt_of_le_of_lt (ENNReal.tsum_le_tsum hv) (by unfold f; simp)).ne] with i hi
 filter_upwards [hi] with n t j; exact lt_of_le_of_lt (single_le_sum (fun j _=>u n j i) (mem_univ j)) (not_le.mp t)
variable {P}
include T
variable {I:ℕ→Type}[∀n,Fintype (I n)]{α ε β:ℕ→ℝ}
/-- EVERY ε and schedule of task types. Fin arity not uniform. We can purchase beyond ANY elected χ desiderata a.e.; common chosen below. -/
lemma slimFast (u:∀ i, Fits (I i) i (ε i) (α i))(v:∀ i,0<ε i)(Y:∀ i,Ladle 4 P.par.block (reserve P.par P.width) (α i) (I i)) : ∃ g:ℕ→ℕ, ∀ f:ℕ→ℕ,g ≤ f → (∀ i j, ‖P.E (f i) (P.tuneK ((Y i).price j)).val‖≤ ε i) ∧
 ∀ᵐ x∂(P.pillars 3),∀ᶠ n in atTop,∀ (j:Axis) i, ‖P.singleState j (f n) (P.otherSpectrum 3 j x) (P.tuneK ((Y n).price i))‖ < ε n:=by
 choose k hk using fun i=> throne_size T (Y i) (u i).1 (u i).2.1; choose g hg using fun i=>eventually_atTop.1 ((hk i).price P.law); refine ⟨g,fun f t=> ⟨fun i j=> (hg i (f i) (t i) (j,false)).trans (u i).2.2.1,?_⟩ ⟩
 let G(i:ℕ)(j:I i)(x:P.Spectrum0 3):= ‖P.singleState 3 (f i) x (P.tuneK ((Y i).price j))‖^2
 have hp(i:ℕ)(j:I i):Continuous (G i j):= ((P.chi_joint 3 (P.reading 3 _ _)).norm).pow _
 have he(i j): (∫ x,G i j x ∂P.pillars 3) ≤ basePrice (α i):= (P.credit_delivers 3 _ (f i) (k i) ((hk i).book j)).trans (hg i _ (t i) (j,true))
 filter_upwards [prognosis G _ hp (fun i j x=> sq_nonneg _) ε v he (fun i=> (u i).2.2.2)] with x hx; filter_upwards [hx] with i p a b; rw [P.single_agrees]; exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (v i).le (by omega: 2≠0)).mp (p b)
omit T
-- common point privilege
namespace Spine
variable (P)(R) {ι:Type}[Fintype ι]{β B:ℝ}
  (S:Ladle 4 P.par.block (reserve P.par P.width) β ι)
lemma simultaneous {k:ℕ}(v:Papal.Lecture P.run P.large S k B) (e:ℝ)(f:0<e)(b:(Fintype.card ι:ℝ)*B < e^2): ∀ᶠ s in atTop,∀ (C:P.Spectrum0 3→Prop), (∀ᵐ x∂P.pillars 3,C x) →(∀ d:ι, ‖P.E s (P.tuneK (S.price d)).val‖≤ B) ∧
   ∃ x:P.Spectrum0 3, P.Sanctuary R 3 x ∧ C x ∧ ∀ (d:ι) (j:Axis), ‖P.singleState j s (P.otherSpectrum 3 j x) (P.tuneK (S.price d))‖< e:=by
 filter_upwards [v.price P.law] with s h;
 let S0:=P.Spectrum0 3; let t:=P.pillars 3; let G (i:ι)(x:S0):= ‖P.singleState 3 s x (P.tuneK (S.price i))‖^2
 have h' (i:ι): (∫ x,G i x ∂(P.pillars 3))≤ B:= (P.credit_delivers 3 (S.price i) s k (v.book _)).trans (h (i,true))
 intro C hc; refine ⟨fun i=> h (i,false),?_⟩
 obtain ⟨x,p,q⟩:= rentGlue (μ':=P.pillars 3) G (fun x=> P.lodestar 3 x ∧ C x) ((P.many_stars 3 R).and hc) f (fun i=>((P.chi_joint 3 (P.reading 3 s (P.tuneK (S.price i)))).norm).pow 2) (fun i x=> sq_nonneg _) h' b
 refine ⟨x,P.homes_weather R 3 (P.all_phases 3 x p.1), p.2, fun i j=>?_⟩; rw [P.single_agrees]; exact (pow_lt_pow_iff_left₀ (norm_nonneg _) f.le (by decide : 2 ≠ 0)).mp (q i)
end Spine
open Lamour Bridge.Celeste Glimpse Morn Spine.RadiusF Ballad
include T
theorem violet_simultaneous{e₀:ℝ}(d:0<e₀): ∃ (β t:ℝ), 0<β∧ 0<t ∧ t<e₀ ∧
    ∃ A: Glimpse.Voyage P.par.block P.calibration.ℓ 4 β (RadiusF.next P.calibration.ℓ),
        (∃ k,Papal.Lecture P.run P.large (menuX P.par.block P.calibration.ℓ 4 β (RadiusF.next P.calibration.ℓ) A) k (4*Real.exp 1*(4*β))) ∧
    ∀ᶠ s:ℕ in atTop,∀ (C:P.Spectrum0 3→Prop),(∀ᵐ x∂P.pillars 3,C x)→ ∃ x:P.Spectrum0 3,C x∧P.party 3 R x ∧
       P.funds s (P.otherSpectrum 3 3 x) A t ∧
       ∀ z:SU.Slot, P.Intact R s A.toGaze x z t∧ P.Royal s (P.otherSpectrum 3 3 x) A (Window.family z) t :=by
 obtain ⟨q,h,g⟩:= Medal.voyageAuth d
 obtain ⟨β,β₀,wp,s,s0⟩:=small_bank (Trinity ⊕ Company) q h.1
 let Y (B:Side)(ℓ:ℕ):Glimpse.Voyage B ℓ 4 β (RadiusF.next ℓ):= Classical.choice (arranged B ℓ 4 β _ (by decide) β₀ wp)
 let V:Papal.Lexicon (Trinity ⊕ Company) β:=fun B z=> menuX B z 4 β (RadiusF.next z) (Y B z)
 obtain ⟨k,H⟩:= throne_size T (V P.par.block (reserve P.par P.width)) β₀ wp; let A:= Y P.par.block P.calibration.ℓ; let W:= V P.par.block P.calibration.ℓ; have h₀:Papal.Lecture P.run P.large W k _:= H
 refine ⟨β,q,β₀,h.1,h.2,A,⟨k,H⟩,?_⟩
 filter_upwards [P.simultaneous R W h₀ q h.1 s0] with t ht
 intro hC Hc
 obtain ⟨v₀,x,u,w,f⟩:= ht hC Hc; let X':= P.otherSpectrum 3 3 x
 have he:P.funds t X' A q:= fun i=> (f (Sum.inr i) 3).le
 have hp:P.Pulsating X' t A.toGaze q:= fun i=> (f (Sum.inl i) 3).le
 exact ⟨x,w,P.parting 3 x R u,he,fun z=> ⟨P.participants R t A.toGaze x (fun i=>(v₀ (Sum.inl i)).trans s) hp h.1 (fun i=>(g i).2) z,P.promisedS t X' A (Window.family z) he hp (u.1.accepted 3) (g (Window.family z)).1 h.1⟩⟩
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.prognosis
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.slimFast
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.simultaneous
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.installation
#check @YM.CF.Buffered.Afterglow.Tower.VacuumSelection.violet_simultaneous
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.violet_simultaneous
