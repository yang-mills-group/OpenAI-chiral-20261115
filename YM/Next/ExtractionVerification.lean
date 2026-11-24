import YM.Next.EXTRACTION.Base
namespace YM.Next.ExtractionVerification
open YM YM.Extraction YM.Dash YM.Next.Extract
universe u v
def Target : Prop := ∀ {G : Gauge} {C : Family G} {f : Order}
    {ι : Type u} [Countable ι] {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    [∀ i, FirstCountableTopology (X i)] [∀ i, T2Space (X i)] {A : ι → ℕ → Prop} {Y : ∀ i, ℕ → ℕ → X i},
    C.Makes → CenterPort C f → Reserve f A Y →
    ∀ b : Presentation C, Affordable b f → (∀ d, RelayCosts b f d) → (∀ d, Detector b f d) →
    ∃ g : Order, (∃ u y, Keeps (f.refine g) A Y u y) ∧
    ∃ (S : Table C.book) (M : ℕ → Table C.book) (R : Bin S), (∃ z, Projected b (f.refine g) R z) ∧
    ∃ (T : Table C.book) (W : DiffPlan T), Base C (f.refine g) S M R T W
theorem checked : Target := @YM.Next.Extract.common
end YM.Next.ExtractionVerification
