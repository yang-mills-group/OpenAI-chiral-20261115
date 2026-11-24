import YM.SU5.Relativistic.Ringlets
import YM.SU5.Relativistic.Trucks
import YM.SU5.Relativistic.ActualWeights
import YM.SU5.Relativistic.TrueSeparation
/-!
# Wedges physically: one aperture.

This includes genuine persistence of offdiag excitation in the multiresolution
field problem. This is propagation about the USEFUL contour, not Fort speed. 
-/
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat PhaseChoice SlabMark Vacancy Tapestry Tapestry.Altitude Tapestry.Exhibition Tower.Selected
open CF.Pannier.Chancel.ScreeV Crest.Sleet Crest.Sleet.UpStart FermionSlab
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {a b:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{L:Rack Λ l}{B:Clay Λ l}
    (D : Exhibition Y H a b I E L B)
local notation "V"=>D.univ_
variable (G:SatinVerification.GroundExtension (i:=a) (k:=b) (E:=E) Y H)
variable (u:ℕ→ℕ) {T:ℕ→Bool→Family (tent Y H)→Family (tent Y H)}(t:GradesAll (i:=a) (a:=G.rows) (k:=b) (b:=G.columns) Y H u T)
variable (d j:Axis) (c:∀ j:Axis,Arena Y H G.history.circuit j 0 false)
variable (x:displayAlgebra Y H D.univ_ G.history G.clipped d false (c d)→⋆ₐ[ℂ] ℂ)
local notation "χ" i:max=> displacement Y H D.univ_ G.history G.clipped d false (c d) x i (c i)
local notation "ψ"=>evaluate Y H D.univ_ G d c (SameCharacter.resident Y H D.univ_ G d false (c d) x)
local notation "P" s:max v:max=>stream Y H (fun s=>T s v) s
local notation "Q"=> G.history
variable (s n:ℕ)
open CF.Pannier.Chancel.ScreeV.Chateau
open CF.Pannier.Chancel
include u t
lemma payFoam (j₁ : Fin 3)(v:Cover)(A ℓ r:ℕ)(e:0<r)(w:∀ i:Axis,zig K r+ℓ≤ (v i).natAbs) (p: v∈ box A)
    (k:‖ψ s (Banner K v A ℓ j₁)‖ ≤ Real.exp (-2)) :
    let F:=auger K A j₁; let X:= {nodeC (Seat5 A)}; let H':=latticeFieldEstimates K v A ℓ j₁; let S:=snowF v A ℓ
    1-Real.exp (-2)≤ ‖ψ s (F*H')‖ ∧ 1-Real.exp (-2)≤ ‖ψ s (H'*F)‖ ∧ ∃ z:ℤ,
        FundX Y H D G d j c x s (T:=T) X S F H' true z r ∨ FundX Y H D G d j c x s (T:=T) S X H' F true z r:=by
 intro F X D₀ Qz -- Qz shadow notation
 let I' := hallW A
 have hp:InTest K false X true F:= gyre_T K (Seat5 A) j₁; have hx:InTest K false Qz true D₀:= latticeFieldEstimates_T K v A ℓ j₁
 have hg:Neutral K F:= gyre_N K (Seat5 A) j₁; have ht:Neutral K D₀:= latticeFieldEstimates_N K v A ℓ j₁
 let Z:= ψ s; let W:= F*D₀; let w':=D₀*F
 have hW:InTest K true (X∪Qz) false W:= ((hp.mono Finset.subset_union_left).mul (hx.mono Finset.subset_union_right)).widen
 have hv:‖1+Z W‖≤Real.exp (-2):=by
    have p:= consistency Y H D.univ_ G d c (SameCharacter.resident Y H D.univ_ G d false (c d) x) (X∪Qz) s
    rw [← show Z 1=1 from p.unit,← p.plus_v _ _ InTest.one hW]; rw [TagMap K v A ℓ] at k; exact k
 have hf: 1-Real.exp (-2) ≤ ‖Z W‖:=by
    have he: (1:ℂ)= (1+ Z W)- Z W:=by simp
    have hk:= norm_sub_le (1+Z W) (Z W); rw [←he,norm_one] at hk; linarith
 have hv': 1-Real.exp (-2) ≤ ‖Z w'‖:=by
    unfold w'; rw [signMark K hx hp]; simp only [Sector.grainB,Bool.and_true,↓reduceIte]; change 1- Real.exp (-2) ≤ ‖Z ((-1:ℂ) • W)‖; rw [show Z ((-1:ℂ) • W)=(-1:ℂ)*Z W from (audition _ _ _ _ _ _ _ s).map_smul (-1) (show Dome K from ⟨W,aux_test hW⟩)] -- tune
    simpa using hf
 refine ⟨hf,hv',?_⟩
 have hz (F D₀:Family K)(Q' V₀:Finset Cover)(z:ℤ)(p:Till K r j z Q' V₀)(h:InTest K false Q' true F)(u':InTest K false V₀ true D₀)(s₀:Neutral K F)(g:Neutral K D₀)(β:1-Real.exp (-2)≤‖ψ s (F*D₀)‖): FundX Y H D G d j c x s (T:=T) Q' V₀ F D₀ true z r:=by
    refine ⟨p,h,u',⟨s₀,g⟩,fun i v e' y=>regionGap Y H j s z r p _ _ e' y,fun n=> ⟨t.neutrally Y H V G.history _ s n h.widen s₀,t.neutrally Y H V G.history _ s n u'.widen g,⟨_,(has_footprint Λ l s Q').persists n,t.allSupport Y H V G.history _ s n h.widen⟩,⟨_,(has_footprint Λ l s V₀).persists n,t.allSupport Y H V G.history _ s n u'.widen⟩⟩,1-Real.exp (-2),sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num)),fun n=>?_⟩
    exact Pays5.requires_wedge Y H D G _ t d j c x s n h u' z e p _ (by simpa [Lariat.discount] using β)
 obtain ⟨z,B|B⟩:= arenaSep K v A ℓ _ w j; exact ⟨z,Or.inl (hz F D₀ X Qz z B hp hx hg ht hf)⟩; exact ⟨z,Or.inr (hz D₀ F Qz X z B hx hp ht hg hv')⟩
end YM.CF.Buffered.Afterglow.Tower.Reconstruction

namespace YM.CF.Py.Rate.LocalLimit.Papal
open Function Set Filter MeasureTheory
open Lattice SU Buffered Afterglow Journey Preparation CF.Pannier.Chancel CF.Pannier.Chancel.Cliplet
open Satin Tapestry Tower Tower.Selected Tower.Vacancy Tower.PhaseChoice
open scoped Topology BigOperators ComplexOrder
attribute [local instance] opCStarAlgebra
open CF.Pannier.Chancel.ScreeV CF.Pannier.Chancel.ScreeV.Chateau Tower.Reconstruction Tower.Reconstruction.FermionSlab Crest.Sleet Crest.Sleet.UpStart
open Pitching.Focus Lifted
-- physical bound all axes, same footprints all n. aperture *either ordering per axis*.
theorem cocoa (ε η:ℝ)(p:0<η)(r:ℕ)(e:0<r)(U:Supplier):
    ∃ P l Z H Y q d w C a b I E L B T t X G c pan s ζ f f' sample,
      Election ε η U P l Z H Y q d w C a b I E L B T t X G c pan s ζ f f' sample ∧ Pitching.Focus.FairRoute P.P P.J P.h P.N0 Push.SectorMeasure.Chi.canonical ∧
      ∃ (u:ℕ→ℕ)(K:ℕ→Bool→ Buffered.Family (tent Y H)→ Buffered.Family (tent Y H)), GradesAll (i:=a) (a:=G.rows) (k:=b) (b:=G.columns) Y H u K∧
      ∃ (A D:ℕ) (v:Cover), ∀ ρ >(0:ℝ),∀ᶠ n in atTop,∀ C':Fin 3,
         let F:=auger (tent Y H) A C'; let H':=latticeFieldEstimates (tent Y H) v A D C'; let S₀:= {nodeC (Seat5 A)}; let S:=snowF v A D; let φ:= evaluate Y H X.univ_ G 0 c (SameCharacter.resident Y H X.univ_ G 0 false (c 0) (pan.character sample));
         1-Real.exp (-2)≤ ‖φ n (F*H')‖ ∧ 1-Real.exp (-2)≤ ‖φ n (H'*F)‖ ∧ footprint P l n S₀ ⊆ Metric.ball 0 ρ ∧ footprint P l n S⊆ Metric.ball 0 ρ ∧
         ∀ j:Axis,∃ z:ℤ, FundX Y H X.toExhibition G 0 j c (pan.character sample) n (T:=K) S₀ S F H' true z r ∨ FundX Y H X.toExhibition G 0 j c (pan.character sample) n (T:=K) S S₀ H' F true z r :=by
 obtain ⟨P,l,Z,H,Y,q,d,w,C,a,b,I,E,L,B,T,t,X,G,c,pan,s,ζ,f,f',sample,h,Tb,v,A,h',h₀,gA,Φ,KQ⟩:= salute U r ε η p
 obtain ⟨u,K,tP⟩:= grades_at Y H X.univ_ G.history
 refine ⟨P,l,Z,H,Y,q,d,w,C,a,b,I,E,L,B,T,t,X,G,c,pan,s,ζ,f,f',sample,h,Tb,u,K,tP,A,h',v,fun ρ p=>?_⟩
 let S':=hallW A; filter_upwards [KQ,thinning_aperture P l S' ρ p] with n h μ C'
 dsimp only; have hx(j:Axis):=payFoam Y H X.toExhibition G u tP 0 j c (pan.character sample) n C' v A h' r e gA h₀ (h 0 c _ C'); exact ⟨(hx 0).1,(hx 0).2.1,μ _ (Finset.singleton_subset_iff.mpr ((bellH A _).mpr (fun j=>by omega))),μ _ (latticeFieldEstimates_S _ _ _ h₀),fun j=> (hx j).2.2⟩
end YM.CF.Py.Rate.LocalLimit.Papal
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.cocoa
#check YM.CF.Py.Rate.LocalLimit.Papal.cocoa
