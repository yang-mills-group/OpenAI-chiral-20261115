import YM.SU5.Reconstruction.Crease.Rounds
import YM.SU5.Reconstruction.Vermont.Spectacle
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock ConePrice SelectionAnalysis Germ Chambers
open Anvil
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G false
local notation "Ds" => Domain Y H G true
local notation "Gt" => marks (timeMesh Λ)
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (a:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped a false (C a) →⋆ₐ[ℂ] ℂ)
local notation "w" i:max=> displacement Y H V G.history G.clipped a false (C a) χ i (C i)
local notation "J₀" i:max=> indoor Y H V G.history G.clipped i false (C i) (w i)
local notation "C₀" i:max=> saunters Y H V G.history G.clipped i false (C i) (w i)
local notation "G₀" i:max=> fort Y H V G.history G.clipped i false (C i) (w i)
local notation "Ω₀" i:max=> vocation Y H V G.history G.clipped i false (C i) (w i)
local notation "S₀" i:max=> peninsula Y H V G.history G.clipped i false (C i) (w i)
local notation "ℜ" p:max=> Real.toNNReal (p:ℝ)
local notation "Pr" i:max=> bridgeEstate Y H V G i (C i) (w i)
local notation "Vo" i:max=> coreOs Y H V G i (C i) (w i)
local notation "Os" i:max=> compassKet Y H V G i (C i) (w i)
local notation "D'" i:max=> Domain Y H G false (flank i 0)
local notation "Tx" => timeMesh Λ
local notation "Q" i:max=>Follows Y H V G i (C i) (w i)
local notation "θ" i:max=> flipMark i (tent Y H)
local notation "m₁" => FirstWindows.move (tent Y H)
local notation "ℓ_"=>osValue Y H V G a (C a) χ
open BridgeClub Reflector
namespace Crease
variable (F: BoostBacking Y H V G C a χ)
variable (j z:Axis) (b:j≠z)
open Lens Sail
local notation "Π₀" i:max=> opCarries Y H V G i (C i) (w i)
local notation "L0" => Sight Y H V G C a χ j
local notation "Fz" => (Vo z)
variable (u v:Axis→marks (timeMesh Λ))(t: marks (timeMesh Λ))
local notation "u'" i:max=> (u + eject z t) i
variable {L:(fort Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))).Op} (u₀: Sight Y H V G C a χ j u v L)
local notation "ζ"=> floor Y H V G C a χ j
local notation "Ξ" i:max=> parcelUp (S₀ i)
omit u₀
include F b
lemma aheadSight (L:(G₀ j).Op)(u₀: Sight Y H V G C a χ j u v L): Sight Y H V G C a χ j (u+eject z t) v ((Ξ j) ((t:ℝ) • basis z) L) := by
 obtain ⟨d,h,x,B,p,hT,K0⟩:=u₀
 let XT(n:ℕ):= m₁ (eject z t) (x n); let L₀:=(Ξ j) ((t:ℝ) • basis z) L
 choose Y₀ e Ht using fun i=> hiker Y H V G C a χ F j z b (x i) (h i) (p.phase i) _ (p.stays i) t
 have h1: Limited atTop (fun i=>(Π₀ j) (Y₀ i)) L₀:= by
   simp_rw [Ht]; unfold parcelUp L₀; exact ((p.propitious.toLeft (Pearl.still atTop _)).toRight (Pearl.still atTop _)) -- assoc? parse
 refine ⟨d,h,XT,Y₀,⟨e,p.phase,p.short,h1⟩,(fun n=> ?_),fun i r=>?_⟩
 · apply domain_mono Y H G _ (moving Y H V G _ _ (hT n))
   rintro _ ⟨x,b₀,rfl⟩
   constructor
   · simp only [Pi.add_apply,coordinates_eject,eject_away z (t:ℝ) j b, add_zero]; exact b₀.1
   intro i l0; rcases b₀.2 i l0 with ⟨v₁,v₂⟩; by_cases a':i=z
   · subst i; simp only [mem_Icc, Pi.add_apply, AddSubgroup.coe_add, coordinates_eject, eject_at]; constructor<;>linarith
   simp only [mem_Icc, Pi.add_apply, coordinates_eject, eject_away z _ i a',add_zero]; exact ⟨v₁,v₂⟩
 obtain ⟨B₀,s⟩:= K0 i r
 by_cases a':i=z
 · subst i; refine ⟨B₀, (fun n=> ?_),s.bounded⟩
   change Follows _ _ _ _ _ _ _ (m₁ (eject z (-u' z)) (m₁ (eject z t) _)) _ _
   rw [move_sum,selectRay,Pi.add_apply,eject_at, show -(u z+t)+t= - u z from by abel]; exact s.beyond n
 choose W bH pH using fun n=> hiker Y H V G C a χ F i z a' _ _ (d i r) _ (s.beyond n) t
 obtain ⟨κ,cl⟩:= s.bounded; refine ⟨W, (fun n=> ?_),κ,fun n=>?_⟩
 · change Follows _ _ _ _ _ _ _ (m₁ (eject i (-u' i)) (m₁ (eject z t) _)) _ _
   rw [Pi.add_apply,eject_away z t i a',add_zero,move_sum,add_comm,← move_sum]; exact bH n
 rw [pH]; exact (parcel_charge ..).trans (cl n)
-- bounding support on just j and k for Mink real net. τ may negative but use threshold sum.
variable (Q': Set E4) (R:ℝ)
local notation "Uq"=> Reel j (fun i=>(u i:ℝ)) (fun i=>(v i:ℝ))
omit F in
lemma booking (t':ℝ)(h:∀ x∈ Q',|x j|+x z ≤ R) (s:|t'|+ R < (u z:ℝ)) : TicketSeparation j Q' ((fun x=> x+t' • basis j) '' Uq):= by
 intro x hx y p; obtain ⟨q,g,rfl⟩ := p
 let p:= q+t' • basis j-x; have p₁:p j=t' -x j:=by simp [p, (show q j=0 from g.1)]
 have p₂: p z=q z - x z:=by simp [p,b.symm]
 have hp : |p j| < p z := by
    rw [p₁,p₂]; linarith [h x hx, (show (u z:ℝ)≤ q z from (g.2 z b.symm).1), abs_sub t' (x j)] -- abs_sub?
 change (p j)^2 < _; rw [← sq_abs]; exact (pow_lt_pow_left₀ hp (abs_nonneg _) (by decide)).trans_le (Finset.single_le_sum (f:=fun i:Axis=>_) (fun i _=> sq_nonneg (p i)) (a:=z) (s:=Finset.univ.erase j) (by simp [b.symm]))
include u₀
lemma spending (t':ℝ)(h:∀ x∈ Q',|x j|+x z≤R)(s:|t'|+R<(u z:ℝ))(A:(G₀ j).Op)(p:A∈ζ Q') : Commute A (LorTime (S₀ j) t' L):= by
 let Q2:= (fun x=> x+t' • basis j) '' Uq; have e: A∈ (ζ Q2).commutant:= spacelike Y H V G C a χ F j Q' Q2 (booking j z b u v Q' R t' h s) p
 let L₁:= LorTime (S₀ j) t' L; have k: L₁= (Ξ j) (t' • basis j) L:=by unfold L₁ parcelUp; rw [← neg_smul,Picket.trans_time,Picket.trans_time]; rfl
 have hp:L₁∈ ζ Q2:= audition (Wing Y H V G C a χ j Q2) (show L₁∈ Wing Y H V G C a χ j Q2 from ⟨u,v,t' • basis j,L,u₀,Subset.refl _,k⟩)
 exact (VonNeumannAlgebra.mem_commutant_iff.mp e _ hp).symm
end Crease
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
