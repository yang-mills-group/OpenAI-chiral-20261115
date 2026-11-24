import YM.SU5.FiniteGaugeData.KernelP.Estate
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
open Nacre Heat Charm Chrono SalonG Journey Hills Playlist Show
namespace KernelP
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)(A:∀ a:Axis,Repertory Y h W' R a)
variable {Φ:ℕ→ Charm.W (tent Y h)→ₗ[ℂ]ℂ}(S':Sphere Y h W' R A Φ)
variable (a:Axis)(z:ℤ)(d n:ℕ)
variable (H:Harbor Y h W' R Φ a)(X:Engine Y h W' R a H)(x:Decko Y h a)
variable (a₀:Axis)(p:Actors Y h a₀ W' R (A a₀))
local notation "U" => p.val.X
local notation "Σ"=> coronet Y h a₀ W' R A p
variable (V:∀ α:p.val.X, Harbor Y h W' R (coronet Y h a₀ W' R A p α) a)(Ξ:∀ α:p.val.X,Engine Y h W' R a (V α))
variable (α:p.val.X)
local notation "P'" i:max n:max=> issueH Y h n a₀ W' R (A a₀) p i
local notation "M"=> p.val.μ
local notation "H₁"=> OriginalH Y h W' R A a
local notation "X₁"=>legacyEngine Y h W' R A a
local notation "ℋ" α:max=> (V α).space
local notation "Θ"=> omegaV Y h W' R
local notation "Ω"=> orbitSeed Y h a₀ W' R (A a₀)
variable (t:W (tent Y h))
-- DCT final count actual state.What account.RealStamp.
local notation "pS" α:max=> issueH Y h s a₀ W' R (A a₀) p α
local notation "Z"=> readingH Y h s a₀ W' R (A a₀)
lemma passport_i : Integrable (fun α:U=> ‖issueH Y h s a₀ W' R (A a₀) p α t‖^2) (M):=by
 haveI:= p.property.normalized
 exact ((vote_civil Y h s a₀ W' R (A a₀) t p).norm.pow 2).integrable_of_hasCompactSupport (μ:=M) (HasCompactSupport.of_compactSpace _) -- tune coercion
lemma pap_v : ∫ α, ‖issueH Y h s a₀ W' R (A a₀) p α x.val‖^2 ∂ (M)=royalMass Y h s W' R a H₁ X₁ x:=by
 let T':= readingH Y h s a₀ W' R (A a₀) x.val; let g(i:U):= ‖(pS i) x.val‖^2; let x₀:=(route Y h s a₀ W' R (A a₀)) x.val
 have hx:(∫ i,g i ∂ (M))= ‖x₀ Ω‖^2:= by
    apply Complex.ofReal_injective
    have he:= p.property.ground (star T'*T'); have ht(i:U):p.val.character i (star T'*T')=(g i:ℂ):=by rw [map_mul,map_star]; unfold g; rw [vote_real,mul_comm (star _ : ℂ)]; change (_* (starRingEnd ℂ) (p.val.character i T'):ℂ)=_; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp_rw [ht] at he; rw [← integral_complex_ofReal, he]; change inner ℂ (Ω) ((star x₀) (x₀ Ω))=_; rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]; rfl -- maybe rfl unneeded
 let y₀:= (route Y h s a W' R (A a)) x.val; let Ω':=orbitSeed Y h a W' R (A a); let T₀:=(StructureH Y h a W' R (A a)).Unity; have he:‖x₀ Ω‖=‖y₀ Ω'‖:=by
    by_cases h₀:a₀=a; swap
    · rw [← (flowsH Y h a₀ a W' R (A a₀) (A a) h₀).norm_map (x₀ Ω)]; unfold x₀ Ω'; rw [flows_seed]
    subst a; rfl
 change (∫ i,g i ∂ (M))= ‖planeP T₀ (store Y h s W' R a (A a) x)‖^2; rw [hx,he]; unfold y₀ Ω'; rw [exhibit,←castC,Hills.yen]
variable (ι: Type*)
include S' in
lemma variance_sphere : let y:= H.leaf s x; let M':= planeP X.val.Unity; let z:= omegaV Y h W' R a H
    ‖M' y-Φ s x.val • z‖^2=royalMass Y h s W' R a H X x - ‖Φ s x.val‖^2:=by
 intro y M' z; have he:inner ℂ z (M' y)=Φ s x.val := by unfold z M'; rw [← planeP_inner, inlet (gold_fixed Y h W' R a H X),goldPrice] -- gH H dic
 rw [norm_sub_sq (𝕜:=ℂ), inner_smul_right, norm_smul, show ‖z‖=1 from omegaBudget Y h W' R A S' a H, mul_one, ← inner_conj_symm (M' y), he, Complex.mul_conj, Complex.normSq_eq_norm_sq]
 change ‖M' y‖^2-2*RCLike.re (K:=ℂ) _+_=_; rw [show ∀ i:ℝ,RCLike.re (K:=ℂ) (↑i:ℂ)=i from fun _=>rfl]; unfold M' y royalMass; ring -- tune layout

include Ξ
lemma purity_x : ∀ᵐ α:p.val.X ∂ (M), planeP (Ξ α).val.Unity ((V α).leaf s x)= issueH Y h s a₀ W' R (A a₀) p α x.val • omegaV Y h W' R a (V α) := by
 let P(i:U):= ‖planeP (Ξ i).val.Unity ((V i).leaf s x)-(pS i) x.val • (Θ) a (V i)‖^2
 let X(i:U):= ‖(pS i) x.val‖^2
 let w(i:U):= royalMass Y h s W' R a (V i) (Ξ i) x-X i
 obtain ⟨hR,e⟩:= beloved Y h s W' R A a x a₀ p V Ξ; have hF: Integrable X (M):=passport_i Y h s W' R A a₀ p x.val
 have hP(i:U):P i=w i:= variance_sphere Y h s W' R A (sphere Y h a₀ W' R A p i) a (V i) (Ξ i) x
 have hp:w= P:= funext fun i=> (hP i).symm; have hi:Integrable w (M):=hR.sub hF; have hz:∀ᵐ i ∂ (M), w i=0:= by
    refine (integral_eq_zero_iff_of_nonneg (fun i=>?_) hi).1 ?_
    · rw [←hP]; exact sq_nonneg _
    unfold w; rw [integral_sub hR hF,e,show (∫ i,X i ∂ (M))=_ from pap_v Y h s W' R A a x a₀ p,sub_self]
 filter_upwards [hz] with i hv; rw [← hP] at hv; unfold P at hv; exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hv))
#print axioms variance_sphere
#print axioms purity_x
end KernelP
end YM.CF.Buffered.Afterglow.Hierarchy
