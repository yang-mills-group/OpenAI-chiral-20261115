import YM.SU5.FiniteGaugeData.Tower.Assess
import YM.SU5.FiniteGaugeData.Tower.Compact
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
/-!
# Extract the actual supported transfer (coefficient level here)
-/
open Reed (Fine think)
open Fock Pastry Tenant
section subsequence
-- n x indexes Course periods, already tending to infinity; U x its paired cutoff
-- index. Above removed the P cared for offstage; here retain sequence qualification
-- separately to require them *on that same path*.
variable (n U:ℕ→ℕ)(h:Tendsto n atTop atTop)(g:∀ s,∀ᶠ r in atTop,legalAt Y s (n r) (U r))
variable (S:Finset Cover)(t:Evens S)
local notation "W"=> wingspan Λ l S
local notation "u"=> tagWord S t.val
local notation "T" r:max p:max=> block Y H s (n r) (U r) S (note K (p:Purse S).val u)

def admittedStage (r:ℕ):Prop := legalAt Y s (n r) (U r) ∧ Tivoli (wingspan Λ l S) ((tent Y H).c (momentm Y (n r) (s+1)))
lemma atoms_test(p:Purse S):InTest K true S false (note K p.val (tagWord S t.val)):=by
 have h:= note_t K u p.property (brand S t.val); rw [t.property] at h; exact h
-- bool gating: if not legal OR not Tivoli, `banner` sees zero, no charges.
lemma empty_gate {r:ℕ}(z:¬ admittedStage Y H s n U S r)(p:Purse S):
 T r p=0:=by
 unfold block; split <;> try rfl
 next h=> unfold distribute_back; rw [dif_neg (show ¬Tivoli W ((tent Y H).c (momentm Y (n r) (s+1))) from fun h'=>z ⟨h.1,h'⟩)]
lemma sustained(p:Purse S)(v:Evens W): Menu («T»:=fun _:ℕ=>ℂ) (fun r z=> banner W (tent Y H) (T r p) v z):=by
 obtain ⟨C,p₀⟩:= p.property.env.cost; have hp:0≤C:=(norm_nonneg _).trans (p₀ (1,1))
 let I₀:= {r:ℕ//admittedStage Y H s n U S r}
 rcases isEmpty_or_nonempty I₀ with P | P; swap
 · let f(i:ℕ):I₀:= if x:admittedStage Y H s n U S i then ⟨i,x⟩ else Classical.choice P
   let R(r:I₀):PairsC→ℂ:= banner W (tent Y H) (T (r.val) p) v
   have he(x:I₀): legalAt Y s (n x.val) (U x.val):= x.property.1
   have ht(x:I₀): Tivoli W ((tent Y H).c (momentm Y (n x.val) (s+1))):= x.property.2
   have hz:Menu R:= output_deck Y H s S _ _ he t ht (fun _=>p) hp (fun _=>p₀) (fun _=>v)
   refine (((hz.re f).cond Menu.zero (admittedStage Y H s n U S))).congr ?_
   intro i x'; split
   next t=> unfold f; rw [dif_pos t]
   next w=> rw [empty_gate Y H s n U S t w p,banner_zero,Pi.zero_apply]
 have he(r): ¬ admittedStage Y H s n U S r:=fun h=> isEmptyElim (show I₀ from ⟨r,h⟩)
 simp_rw [empty_gate Y H s n U S t (he _) p,banner_zero, Pi.zero_apply]; exact Menu.zero

abbrev AllAccess(Λ:Preparation)(l:ℕ) := Σ S:Finset Cover,ℕ× Evens S× Evens (wingspan Λ l S)
local notation "J"=> AllAccess Λ l
include h g
lemma voted:∃ f:ℕ→ℕ, StrictMono f∧∀ (S:Finset Cover)(s:ℕ)(ε:ℝ), 0<ε →∀ᶠ r:ℕ in atTop, ∀ (t:Evens S)(q:Evens (wingspan Λ l S)) m, r≤ m→∀ p',r≤p' →∀ v:Purse S,(∀ y,‖v.val y‖≤ 1)→∀x:PairsC,
    let Z i:=banner (wingspan Λ l S) (tent Y H) (block Y H s (n (f i)) (U (f i)) S (note K v.val (tagWord S t.val)))
    dist (Z m q x) (Z p' q x)<ε :=by
 let F(i:J)(r:ℕ)(p:Purse i.1)(z:PairsC):=banner (wingspan Λ l i.1) (tent Y H) (block Y H i.2.1 (n r) (U r) i.1 (note K p.val (tagWord i.1 i.2.2.1.val))) i.2.2.2 z
 let C (i:J):Set (Purse i.1):={p|∀ y, ‖p.val y‖≤(1:ℝ)}
 have Hp:Orchestra C F:=by
    refine ⟨fun i p=>sustained Y H i.2.1 n U i.1 i.2.2.1 p i.2.2.2,?_⟩
    rintro ⟨box,i,t,q'⟩ ε u'
    obtain ⟨a,w⟩:= finance_inputs Y H i box t ε u'
    refine ⟨a,?_⟩
    obtain ⟨m,v⟩:= eventually_atTop.mp ((g i).and (h.eventually (admit_event Y H i box)))
    filter_upwards [eventually_ge_atTop m] with r K' x D
    obtain ⟨b,V,p⟩:=w x D; exact ⟨b,V,fun j e z=> p (n j) (U j) (v _ (K'.trans e)).1 (v _ (K'.trans e)).2.1 (v _ (K'.trans e)).2.2 _ _⟩
 obtain ⟨f,h,q⟩:= simultaneous_cauchy _ _ Hp; refine ⟨f,h,fun S s ε e=>?_⟩
 filter_upwards [(eventually_all (ι:=Evens S × Evens (wingspan Λ l S))).mpr (fun i=> q ⟨S,s,i.1,i.2⟩ ε e)] with r H
 intro t₀ q₀ p hp b v c h x
 exact H (t₀,q₀) _ hp _ v _ h x
end subsequence
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.voted
