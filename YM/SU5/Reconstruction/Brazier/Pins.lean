import YM.SU5.Reconstruction.Brazier.Venator
/-! Two test-station pair on the actual S. Supply resolution supports. Even as measured at every post.T and at corresponding trajectory, maintain measurement authority & coherence incl interaction budgets. Physical localization is at the ^precise^ U W prices not just `Tarmac` roster; no loss of interpretation at this ruler. No Wick real-time from this lemma.I.Path. -/
set_option autoImplicit false
set_option synthInstance.maxSize 31000
set_option maxRecDepth 6200
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Brazier
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry Altitude Exhibition Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation SlabMark MeshClock
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
variable {L : Rack Λ l} {B : Clay Λ l} (Z : Exhibition Y H i k I E L B)
variable (j : Axis) (C : Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)
local notation "Gt" => marks (timeMesh Λ)
local notation "t₀" => insideAt Λ l (tent Y H)
local notation "D" => Domain Y H G
local notation "A"=> Ark.Ht Y H G.history.circuit j 0 false C
local notation "Π"=>Aurora Y H V G.history j false C
local notation "Kx" t:max=> vistaFinish Y H t Z
local notation "Px" => LightBudget.prepaid Y H V G j C
namespace Encamp
open Hearth Tarmac Fortune SingleFrame Labor Fervor FirstWindows.Brazier.Path Marshal
open Fock Lat Laurent Wilson Cube Finset Branch Scree RG Spire Vale Pastry Peaks Dial Phase
 Lifted Skye Tapestry.Exhibition Tapestry.Altitude Tenant Rush Tulip
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable (s:ℕ)(x y:Dome (tent Y H))
noncomputable abbrev splitShape (U W:Finset Cover): Tarmac := byRoof s fun _=> U ∪ W
variable {r:Hearth Y H G j}{T:Finset Tarmac}{g d:ℝ}
local notation "N"=> r.height
local notation "M'"=> r.roof
variable {U W:Finset Cover} (e:x∈bay (tent Y H) U true) (h:y∈bay (tent Y H) W true)
local notation "ηp"=> splitShape s U W
local notation "π"=> pinhole (Dome (tent Y H)) s
lemma port_cover (_t:Finset Cover)(f:Dome (tent Y H))(p:f∈bay K (U∪W) true): (π) f∈ (splitShape s U W).fares K:= pokes (Set.Iic s) (fun i=> bay K ((splitShape s U W).book i) true) (Set.mem_Iic.mpr (show s ≤ s from le_rfl)) (show f∈ bay K ((splitShape s U W).book s) true from (by rw [bookRoof _ le_rfl]; exact p))
lemma enlargement (U W:Finset Cover): U∪W⊆ frameBudget (splitShape s U W).book Λ l s := by
 have he: U ∪ W = (splitShape s U W).book s:=Eq.symm (bookRoof _ (by omega))
 exact (le_of_eq he).trans (frame_open (splitShape s U W).book s Λ l)

lemma boxPays (S:Finset Cover)(q:S⊆U∪W): bufferedHull Λ l s S⊆ (splitShape s U W).land Λ l := by -- replace
  intro x hx; obtain ⟨a,c,f⟩:=Set.mem_iUnion₂.mp hx
  exact ( ( (ηp).hull_contains (show s≤(ηp).roof from le_rfl)) (Set.mem_iUnion₂.mpr ⟨a,(by rw [bookRoof _ le_rfl]; exact q c),f⟩))
noncomputable abbrev billing (m u:ℕ)(r:Hearth Y H G j): ℂ:= capAccount Y m u ((Pole Y H m u (pinhole _ s x)*Pole Y H m u (pinhole _ s y))*conduit Y H G j m u r) / capAccount Y m u (conduit Y H G j m u r)
variable (m u : ℕ)
local notation "Ψ" a:max i:max=>volumeAround Λ l i a
private lemma further (S:Finset Cover)(i j:ℕ): volumeAround Λ l (i+j) S=Ψ (Ψ S i) j:=by induction j with| zero=>rfl| succ j ih=> rw [←Nat.add_assoc,volumeAround,ih,volumeAround]
private lemma orient {a:ℕ} (p:Routing Y H V G Z j C χ T g d m u r)(q: (splitShape s U W) ∈ T) : PhaseChoice.FullDistances (volumeAround Λ l a (r.facePlate Y H G j ∪ volumeAround Λ l (r.roof - s) (U∪W))) (Journey.side Y m (r.roof+a)):=by
 obtain ⟨c,f⟩:=p.clearance (ηp) q
 exact dist_mono_here (origin_mono (show r.facePlate Y H G j∪ _ ⊆_ from Finset.union_subset_union (le_refl (r.facePlate Y H G j)) (origin_mono (enlargement (Λ:=Λ) (l:=l) s U W) _)) _) (f a)
local notation "CLK"=> Y.uv u
local notation "γS" i:max => faceOf Y H m u i
-- include actual portfolio scheduling & distances even between the wider central & gate. POS part.Also separateness as CBuck for Wightman prospects.
structure AtSea (s:ℕ)(x y:Dome (tent Y H))(r:Hearth Y H G j)(m u:ℕ)(d:ℝ)(Uₚ W:Set RSpace): Prop where
    tall : s < r.roof
    -- book same supports throughout. Including separate true physical supports all the way from s.
    buys : ∃ S₀ S₁: Finset Cover,
      PhaseChoice.SupportedPhysically Λ l s S₀ Uₚ ∧ PhaseChoice.SupportedPhysically Λ l s S₁ W ∧ x∈bay (tent Y H) S₀ true ∧ y∈bay (tent Y H) S₁ true ∧
      (∀ x∈ bufferedHull Λ l s S₀ ∪ bufferedHull Λ l s S₁, x j + d < (r.height:ℝ) ∧ -(r.height:ℝ)+d < x j )∧
      (∀ i, PhaseChoice.FullDistances (volumeAround Λ l i (S₀ ∪ S₁)) (Journey.side Y m (s+i)))∧
      (∀ i, PhaseChoice.FullDistances (volumeAround Λ l i (r.facePlate Y H G j ∪ volumeAround Λ l (r.roof-s) (S₀∪S₁))) (Journey.side Y m (r.roof+i)))∧
      (∀ i, s+i ≤ Y.uv u →
        AtSupport false (Satin.region (volumeAround Λ l i S₀) (Journey.side Y m (s+i))) (faceOf Y H m u (s+i) (pinhole (Dome (tent Y H)) s x)) ∧
        AtSupport false (Satin.region (volumeAround Λ l i S₁) (Journey.side Y m (s+i))) (faceOf Y H m u (s+i) (pinhole (Dome (tent Y H)) s y)) ∧
        faceOf Y H m u (s+i) (pinhole _ s (x*y))=faceOf Y H m u (s+i) (pinhole _ s x)*faceOf Y H m u (s+i) (pinhole _ s y))
    apart : Disjoint Uₚ W
    booted : ∀ i,r.roof+i ≤ Y.uv u → Hearth.WatchCost Y H G j r m u i
    contains : Tapestry.Pay Y r.roof m u
    audited : Spending Y H G j r m u (pinhole _ s (x*y))
    calculated : billing Y H G j s x y m u r= calculate Y H G j m u r (pinhole _ s (x*y))
variable (p:Routing Y H V G Z j C χ T g d m u r)(q: splitShape s U W∈T)
variable {U₁ U₂:Set RSpace}
include e h p q
lemma earns_at (Sx:PhaseChoice.SupportedPhysically Λ l s U U₁)(Sy:PhaseChoice.SupportedPhysically Λ l s W U₂)(b:Disjoint U₁ U₂)(h':∀ i, PhaseChoice.FullDistances (volumeAround Λ l i (U∪W)) (Journey.side Y m (s+i))): AtSea Y H G j s x y r m u g U₁ U₂:=by
 have hv:= p.clearance (ηp) q
 obtain ⟨a,t⟩:= Tapestry.issued.mp (port_cover Y H s U (U:=U) (W:=W) (x*y) (mul_mem (tallerBay K _ _ ( show U ⊆U∪ W from Finset.subset_union_left ) e) (tallerBay K _ _ Finset.subset_union_right h))) -- tune
 let F(i:ℕ):Prop:=faceOf Y H m u (s+i) ((π) (x*y))=faceOf Y H m u (s+i) ((π) x)*faceOf Y H m u (s+i) ((π) y)
 have H': ∀ i:ℕ,s+i≤ Y.uv u → F i :=by -- tune
   intro i z; unfold F; rw [map_mul]; exact factor_native Y H m u s (PhaseChoice.separatedPhys Sx Sy (Disjoint.preimage _ b)) _ _ (short_pinhole s x) (short_pinhole s y) (singleCover Y H m u (S:=U) (x:=x) e) (singleCover Y H m u (S:=W) (x:=y) h) (by rw [←map_mul]; exact singleFactor ..) (fun i=> dist_mono_here (Finset.union_subset (origin_mono Finset.subset_union_left _) (origin_mono Finset.subset_union_right _)) (h' i)) ⟨p.finance.1,z⟩
 have he: s < r.roof:=hv.1.later
 refine ⟨he,⟨U,W,Sx,Sy,e,h,?_,h',fun i=> orient Y H V G Z j C χ s m u p q,fun i z=>?_⟩,b,fun i z=>(traverses Y H V G Z j C χ p z).1,p.finance,fire Y H V G Z j C χ p q t,?_⟩
 · refine fun i v=> hv.1.room i (((Set.union_subset (boxPays s U Finset.subset_union_left) (boxPays s W Finset.subset_union_right))) v)
 · exact ⟨source Y H m u _ _ (short_pinhole s x) (singleCover Y H m u (x:=x) e) i ⟨p.finance.1,z⟩, source Y H m u _ _ (short_pinhole s y) (singleCover Y H m u (x:=y) h) i ⟨p.finance.1,z⟩, H' i z⟩ -- e type
 unfold billing calculate; congr 3 -- tune show via rewriting
 obtain ⟨i,hi⟩:= Nat.exists_eq_add_of_le (he.le.trans p.finance.2)
 have hc: faceOf Y H m u (Y.uv u) ((π) (x*y))= faceOf Y H m u (Y.uv u) ((π) x)*faceOf Y H m u (Y.uv u) ((π) y):= hi.symm ▸ H' i hi.ge
 exact funext fun V'=> (congrFun hc (V',V')).symm
end Encamp
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Brazier
