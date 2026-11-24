import YM.SU5.FiniteGaugeData.Marked.Variation.Performance

/-! # Stage-based estimate analog (this is on the Lean election; see history
caveats vs manuscript eq:markedC). Just thin the *volumes* further now;
specifically keep the shared UV purchased even for tests before this further
quantitative thinning. -/
set_option autoImplicit false
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Satin
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Py Py.Rate LocalLimit Preparation Journey Vale VolumeCape
attribute [local instance] opCStarAlgebra
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x){i k:ℕ→ℕ}
local notation "K"=>tent Y H
variable {I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)
local notation "Ω" s=>sharp Y H s
private lemma calendars{I:Type*}[Countable I](p:I→ℕ→ℕ→Prop)(h:∀i x,∀ᶠ l:ℕ in atTop,p i x l):∃ t:ℕ→ℕ, StrictMono t∧∀i,∀ᶠ x in atTop,p i x (t x):=by
 rcases isEmpty_or_nonempty I with e | e
 · exact ⟨id,strictMono_id,fun i=> isEmptyElim i⟩
 obtain ⟨s,v⟩:= exists_surjective_nat I
 have hx(x r:ℕ):∃ i≥ r+1,∀ m≤ x,p (s m) x i:=by
    obtain ⟨i,q,t⟩:= ((eventually_ge_atTop (r+1)).and ((eventually_all_finset (range (x+1))).mpr (fun m _=> h (s m) x))).exists
    exact ⟨i,q,fun m g=> t m (by simp; omega)⟩
 choose F c w using hx
 let t:= Nat.rec (motive:=fun _=>ℕ) (F 0 0) (fun r u=> F (r+1) u)
 refine ⟨t,strictMono_nat_of_lt_succ (fun r=>c ..),fun i=>?_⟩
 obtain ⟨r,rfl⟩:=v i; filter_upwards [eventually_ge_atTop r] with x H
 cases x
 · exact w 0 _ _ H
 exact w _ _ _ H
include V
lemma crimson : ∃ q:ℕ→ℕ, StrictMono q ∧
 ∀ (S:Finset Cover)(s:ℕ), ∀ᶠ r in atTop,
   let m:= momentm Y (i (q r)) s
   Hosp S ((K).c m) ∧ ∀ (f:Family K), InTest K true S false f →∀ A:ℝ, (∀ x, ‖f m x‖≤ A) →
     ‖I s f (i (q r))-E s f‖ ≤ (1/2:ℝ)^r*A ∧
     ∀ j, legacy Y (i (q r)) (k j)→ ‖sharp Y H s (i (q r)) (k j) f-E s f‖ ≤ (1/2:ℝ)^r*A :=by
 let P(x : Finset Cover × ℕ)(j r:ℕ):Prop:=
   let m:= momentm Y (i r) x.2
   Hosp x.1 ((K).c m)∧∀ (f:Family K),InTest K true x.1 false f→∀ y:ℝ,(∀ x', ‖f m x'‖ ≤ y)→
     ‖I x.2 f (i r)-E x.2 f‖ ≤ (1/2:ℝ)^j*y ∧∀ p,legacy Y (i r) (k p) → ‖sharp Y H x.2 (i r) (k p) f-E x.2 f‖ ≤ (1/2:ℝ)^j*y
 have h0(S:Finset Cover)(s:ℕ): ∀ᶠ r in atTop, Hosp S ((K).c (momentm Y (i r) s)):= (((momentum Y s).comp V.pick.grow_i.tendsto_atTop).eventually (separates K S)).mono fun r t=>⟨t⟩
 have hp(x)(j):∀ᶠ r in atTop,P x j r:=by
    obtain ⟨S,s⟩:=x
    filter_upwards [(boutique Y H V S s).2 ((1/2:ℝ)^j) (by positivity),h0 S s] with r H' v
    exact ⟨v,fun f st y=> H' f st _ v y⟩
 obtain ⟨t,m,g⟩:=calendars P hp
 exact ⟨t,m,fun S s=>g (S,s)⟩
end YM.CF.Buffered.Afterglow.Satin
#print axioms YM.CF.Buffered.Afterglow.Satin.crimson
