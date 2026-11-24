import YM.SU5.Reconstruction.FirstWindows.Sharp
import YM.SU5.Reconstruction.Cone.RootPrice
/-!
# Design support runway and prices on THIS system: genuine local algebra of all the coherence budgets, gauge flavor of queries, canonical BILL to charge separately. Not assuming additional invoices. -/
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
local notation "X" => Cloud (Dome (tent Y H))
local notation "Kx" t:max=> vistaFinish Y H t Z
local notation "Px" => LightBudget.prepaid Y H V G j C
structure Tarmac where
 roof:ℕ
 posts : Fin (roof+1) → Finset Cover
namespace Tarmac
instance : Countable Tarmac := Function.Injective.countable (f:=fun (x:Tarmac)=> ((⟨x.roof,x.posts⟩ : Σ n:ℕ, Fin (n+1) → Finset Cover))) (by rintro ⟨r,u⟩ ⟨t,v⟩ h; injection h with e hx; dsimp at e hx; subst t; cases eq_of_heq hx; rfl)
instance : Inhabited Tarmac := ⟨0,(fun _=>∅)⟩
variable (a:Tarmac) (J:Calibration)
noncomputable def book (i:ℕ) : Finset Cover := if p:i ≤ a.roof then a.posts ⟨i,Nat.lt_add_one_iff.mpr p⟩ else ∅
noncomputable def land (Λ:Preparation)(l:ℕ) (a:Tarmac) : Set RSpace:= ⋃ s∈ Finset.Iic a.roof, bufferedHull Λ l s (a.book s)
local notation "Ψ"=> a.land Λ l
lemma hull_contains {s:ℕ} (p:s ≤ a.roof): bufferedHull Λ l s (a.book s)⊆ a.land Λ l:= subset_iUnion₂_of_subset s (Finset.mem_Iic.mpr p) Set.Subset.rfl
lemma pays : PhaseChoice.SupportedPhysically Λ l a.roof (frameBudget a.book Λ l a.roof) (a.land Λ l):= frame_lines a.book a.roof Λ l (fun i p=> (supported_iff Λ l i _).2 (a.hull_contains p))
lemma land_compact : IsCompact (a.land Λ l):= (Finset.Iic a.roof).isCompact_biUnion fun i _=> compact_hull Λ l i _
abbrev fares : Subalgebra ℂ (Cloud (Dome J)):= fountainHeads J a.book a.roof
lemma storm {f : Cloud (Dome (tent Y H))} (p:f∈a.fares (tent Y H)) : f∈ HeightWindow (Λ:=Λ) (l:=l) K (a.land Λ l) a.roof :=
  makesWay (Set.Iic a.roof) (Set.univ ∩Set.Iic a.roof) (fun i=>bay K (a.book i) true) (fun i=> keep Λ l i K true (PhaseChoice.handstamp Ψ)) (by simp) (fun i h f v=> ⟨_,v,(supported_iff Λ l i _).2 (a.hull_contains h)⟩) p
lemma quay {f : Cloud (Dome (tent Y H))} (p:f∈a.fares (tent Y H)): f∈ FiniteGaugeDataPoly (tent Y H):= curve.mpr ⟨a.roof,prePrice K a.book a.roof p⟩
-- If f at U choose tarmac supported there. Need honor f's own supports.
variable {s:ℕ} {U:Set RSpace}
open Set
noncomputable def byRoof (n:ℕ)(f:BillOfWork): Tarmac:=⟨n,(fun i=> f i.val)⟩
@[simp] lemma bookRoof {n:ℕ} (f:BillOfWork){i:ℕ} (p:i≤n): (byRoof n f).book i=f i:=dif_pos p
lemma smallTown (s:ℕ)(v:BillOfWork)(p:∀ i,i ≤ s→ PhaseChoice.SupportedPhysically Λ l i (v i) U): land Λ l (byRoof s v) ⊆ U:= by
 intro x h; obtain ⟨i, (e:i∈Finset.Iic s), (h:x∈ bufferedHull Λ l i _)⟩:= Set.mem_iUnion₂.mp h; rw [bookRoof v (Finset.mem_Iic.mp e)] at h; exact (supported_iff ..).mp (p i (Finset.mem_Iic.mp e)) h
lemma towns (s:ℕ){f:Cloud (Dome (tent Y H))}(p:f∈HeightWindow (Λ:=Λ) (l:=l) K U s):
  ∃ a:Tarmac,a.roof=s ∧ a.land Λ l ⊆ U ∧ f∈ a.fares (tent Y H):=by
  let R:= Set.univ∩ Set.Iic s
  apply Altitude.boarded
    (P:={f| Officer R (fun t=>keep Λ l t K true (PhaseChoice.handstamp U)) f})
    (M:=fun f=> ∃ a:Tarmac, a.roof=s ∧ a.land Λ l ⊆ U ∧ f∈ a.fares K) ?_ ?_ ?_ ?_ p
  · intro f (h:Officer _ _ f); choose w hw hu using (show ∀ i,∃ S:Finset Cover,f i∈bay K S true∧PhaseChoice.SupportedPhysically Λ l i S U from h.observes)
    refine ⟨byRoof s w,rfl,smallTown s w (fun i _=>hu i),?_⟩
    refine coin_mono K w _ s s ?_ le_rfl (officer_stone (Set.Iic s) (fun i=>bay K (w i) true) (⟨h.1,hw,(fun i t=> h.3 i fun h=> t h.2)⟩ : Officer _ _ f)) -- apply tune
    intro i t; rw [bookRoof _ t]
  · refine ⟨byRoof s (fun _=>∅),rfl,smallTown s _ (fun i h x t=> (Finset.notMem_empty x t).elim), Subalgebra.zero_mem _⟩
  · rintro f g _ _ ⟨a,r,w,h⟩ ⟨b,t,w',h'⟩; let S i:= a.book i ∪ b.book i
    refine ⟨byRoof s S,rfl,smallTown s S (fun i p=> Tapestry.unionPrinted Λ l i _ _ _ ((supported_iff ..).2 ((a.hull_contains (p.trans r.ge)).trans w)) ((supported_iff ..).2 ((b.hull_contains (p.trans t.ge)).trans w'))), Subalgebra.add_mem _ ?_ ?_⟩
    · exact coin_mono K a.book (byRoof s S).book a.roof s (fun i p=>by rw [bookRoof S (p.trans r.le)]; exact Finset.subset_union_left) r.le h
    exact coin_mono K b.book (byRoof s S).book b.roof s (fun i p=>by rw [bookRoof S (p.trans t.le)]; exact Finset.subset_union_right) t.le h'
  rintro z x _ ⟨a,r,w,h⟩; exact ⟨a,r,w,(a.fares K).smul_mem h z⟩
lemma received {f:Cloud (Dome (tent Y H))}{b:Bool}(p:f∈ questions Λ l (tent Y H) b U):
    ∃ a:Tarmac, a.land Λ l ⊆ U ∧ ∃ r:ℝ, Pocket (tent Y H) a.book a.roof r f := by
 obtain ⟨s,h⟩:=(questions_price Y H p).exists
 obtain ⟨a,_,w,u⟩:= towns Y H s h
 exact ⟨a,w,Tapestry.issued.mp u⟩
end Tarmac
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Brazier
