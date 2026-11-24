import YM.SU5.FiniteGaugeData.Cirrus.Braise
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Cirrus.PavilionM
open Complex Filter Function Set MeasureTheory MeasureTheory.Measure Boundary OS OS.Semigroup Probe Maison Flute Mink
open scoped Topology NNReal InnerProductSpace
variable {H:Hilbert}(S: OS.Semigroup H timeAxis)(Ω:Bench S)
variable {ι:Type}(G:Canopy H ι)(J K:Set ι)(U V:Set E4)(t:G.Token)(w:List G.Token)
local notation "D"=> G.Model S Ω
local notation "X"=> Effort S Ω G
local notation "E"=> G.lens S Ω
local notation "Ω₁"=>G.focus S Ω []
local notation "T₁"=> RToken G J U
local notation "Kₐ"=> Hull S Ω G
open Canopy Submodule
variable (A B:Effort S Ω G) (Pn:Boundary.Action H)(L:G.Arrival S Ω Pn)
local notation "T₂"=> DualR S Ω G
namespace Bono
variable (p:∀ x:E4,M S x Ω.val=Ω.val)(u:IsOpen U)(u':U.Nonempty)
include p u u' L
abbrev WalkP(U:Set E4)(x:H.space): Prop:=∃ q:ℕ→ Hull S Ω G J U,Tendsto (fun i=> Sales S Ω G J U (q i)) atTop (𝓝 x)
set_option maxHeartbeats 80000
lemma roam (x:H)(h:x∈ Height S Ω G J): WalkP S Ω G J U x:=by
 have he: x∈ closure (Set.range (Sales S Ω G J U)):=by change x∈ (LinearMap.range (Sales S Ω G J U)).topologicalClosure; rw [← Treasury, plot_reach S Ω p G J Pn L.time U u u']; exact h
 obtain ⟨v,v',f⟩:=mem_closure_iff_seq_limit.mp he; choose C hv using v'; exact ⟨C,(by simp_rw [hv]; exact f)⟩
structure CensusBook (U V:Set E4)(x y:H.space):Prop where
 witness:∃ (C Qp:ℕ→ Hull S Ω G J U)(F:ℕ→ Hull S Ω G K V),
   (∀ i, DualR S Ω G (C i).val (Qp i).val)∧ Tendsto (fun i=> Sales S Ω G J U (C i)) atTop (𝓝 x)∧ Tendsto (fun i=> Sales S Ω G K V (F i)) atTop (𝓝 y)∧ Tendsto (fun i=> MeanBill S Ω G ((Qp i).val*(F i).val)) atTop (𝓝 (inner ℂ x y))∧ Tendsto (fun i=> MeanBill S Ω G (Qp i).val) atTop (𝓝 (inner ℂ x Ω.val))∧ Tendsto (fun i=>MeanBill S Ω G (F i).val) atTop (𝓝 (inner ℂ Ω.val y))
lemma censusBook (v:IsOpen V)(v':V.Nonempty)(x y:H.space)(a:x∈ Height S Ω G J)(b:y∈Height S Ω G K) : CensusBook S Ω G J K U V x y:=by
 obtain ⟨C,u₀⟩:= roam S Ω G J U Pn L p u u' x a; obtain ⟨B,h₀⟩:= roam S Ω G K V Pn L p v v' y b
 choose A h Qp using fun i=>reserve S Ω G J U (C i).val Pn L (C i).property; refine ⟨C,(fun i=>⟨A i,h i⟩),B,Qp,u₀,h₀,?_,?_,?_⟩ -- D notation local.D fix
 · exact ((u₀.inner h₀).congr fun i=> Qp i (G.focus S Ω []) (((B i).val) (G.focus S Ω [])))
 · exact ((u₀.inner (tendsto_const_nhds (x:=Ω.val))).congr fun i=> Qp i Ω₁ Ω₁)
 exact tendsto_const_nhds.inner h₀
#print axioms censusBook
end Bono
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Cirrus.PavilionM
