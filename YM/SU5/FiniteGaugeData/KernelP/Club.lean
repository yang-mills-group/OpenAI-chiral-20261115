import YM.SU5.FiniteGaugeData.KernelP.Range
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
abbrev Unique :Prop:=∀ x:X.val.Unity.toSubmodule, ∃ b:ℂ,x.val= b • omegaV Y h W' R a H
-- Equivalent def: every simultaneous fixed vector of the continuous-time & all other rational ticks is the vacuum * scalar; proof later
local notation "D"=> Decko Y h a
variable (a₀:Axis)(p:Actors Y h a₀ W' R (A a₀))
local notation "U" => p.val.X
local notation "Σ"=> coronet Y h a₀ W' R A p
variable (V:∀ α:p.val.X, Harbor Y h W' R (coronet Y h a₀ W' R A p α) a)(Ξ:∀ α:p.val.X,Engine Y h W' R a (V α))
local notation "P'" i:max n:max=> issueH Y h n a₀ W' R (A a₀) p i
local notation "M"=> p.val.μ
include H
lemma separableC (g:Sphere Y h W' R A Φ) : TopologicalSpace.SeparableSpace H.space:=by
 obtain ⟨t,e,p⟩:= charged Y h W' R A a; haveI:Countable ↥t:= e.to_subtype; exact ⟨⟨_,Set.countable_range _, (p g H)⟩⟩
omit H
include p A V Ξ
local notation "Ω" α:max => omegaV Y h W' R a (V α)
theorem canon : ∀ᵐ α:p.val.X ∂ p.val.μ, Unique Y h W' R a (V α) (Ξ α):=by
 obtain ⟨b,t,hx⟩:= charged Y h W' R A a; haveI:Countable ↥b:=t.to_subtype
 have ht:= ae_all_iff.mpr (fun x:b=> purity_x Y h x.val.1 W' R A a x.val.2 a₀ p V Ξ); filter_upwards [ht] with i t
 let P:=planeP (Ξ i).val.Unity; let T':= Submodule.span ℂ ({(Ω i)}: Set (V i).space); have he:IsClosed (T' : Set (V i).space):= by unfold T'; exact Submodule.closed_of_finiteDimensional _
 have hp(x:(V i).space): P x∈ T':=by
    let U':(↥b)→(V i).space:=fun x=> (V i).leaf x.val.1 x.val.2
    refine (hx (sphere Y h a₀ W' R A p i) (V i)).induction (P:=fun x=> P x∈ T') ?_ (he.preimage P.continuous) x; rintro _ ⟨x,rfl⟩; change P (U' x)∈ _; rw [show P (U' x)=_ from t x]; exact T'.smul_mem _ (Submodule.subset_span rfl)
 intro x; have h:P (x.val)=x.val:= inlet (show x.val∈(Ξ i).val.Unity from x.property)
 obtain ⟨c,v⟩:=Submodule.mem_span_singleton.mp (h ▸ hp x.val); exact ⟨c,v.symm⟩ -- singleton_ne mem proof explicitly

section union
omit V Ξ
variable (L:∀ (a:Axis)(α:p.val.X), Harbor Y h W' R (coronet Y h a₀ W' R A p α) a)(η:∀(a:Axis)(α:p.val.X),Engine Y h W' R a (L a α))
include L η
lemma coalWorld : ∀ᵐ α:p.val.X ∂ p.val.μ,∀ a,Unique Y h W' R a (L a α) (η a α):= ae_all_iff.mpr fun a=> canon Y h W' R A a a₀ p (L a) (η a)
lemma club (S:Set p.val.X)(w:IsOpen S)(v:S.Nonempty): ∃ α:p.val.X,α∈ S∧ ∀ a, Unique Y h W' R a (L a α) (η a α) :=by
 haveI:=p.property.support
 have hr:∃ᵐ α:p.val.X ∂ p.val.μ,α∈ S:= frequently_ae_mem_iff.2 (Measure.IsOpenPosMeasure.open_pos _ w v) -- lemma?
 exact (hr.and_eventually (coalWorld Y h W' R A a₀ p L η)).exists
lemma facetime (u:p.val.μ ≠ 0) : ∃ α:p.val.X,∀ a, Unique Y h W' R a (L a α) (η a α) :=by haveI:=p.property.normalized; exact (coalWorld Y h W' R A a₀ p L η).exists
lemma vote_retains (x:W (tent Y h))(q:E s x.val≠0): ∃ α:p.val.X, issueH Y h s a₀ W' R (A a₀) p α x≠0 ∧ ∀ a, Unique Y h W' R a (L a α) (η a α):= by
 let f:=fun α=> issueH Y h s a₀ W' R (A a₀) p α x; have he:∃ᵐ α:p.val.X ∂ p.val.μ,f α≠0:= by
    by_contra! hx; exact q ((vote_pearl Y h s a₀ W' R (A a₀) x p).symm.trans (by rw [integral_congr_ae hx]; simp)) -- tune hx eventual format
 exact (he.and_eventually (coalWorld Y h W' R A a₀ p L η)).exists
end union

#print axioms club
#print axioms vote_retains
end KernelP
end YM.CF.Buffered.Afterglow.Hierarchy
