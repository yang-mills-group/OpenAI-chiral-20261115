import YM.SU5.Relativistic.Royard
/-! # CP11 quantitative UV-Weyl genealogy (all fixed stencils) at once. Selected.
 Retain hard record CP10. Compare hermitian REAL chars—all centers, normalized. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 480000
set_option maxRecDepth 5000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Papal
open Function Filter MeasureTheory Metric
open Lattice SU Buffered Afterglow Journey Preparation CF.Pannier.Chancel CF.Pannier.Chancel.Cliplet
open Satin Tapestry Tower Tower.Selected Tower.Vacancy Tower.PhaseChoice Tower.SlabMark
open scoped Topology BigOperators ComplexOrder
attribute [local instance] opCStarAlgebra
open CF.Pannier.Chancel.ScreeV CF.Pannier.Chancel.ScreeV.Chateau Tower.Reconstruction Tower.Reconstruction.FermionSlab Crest.Sleet Crest.Sleet.UpStart
open Pitching.Focus Lifted
open CF.Papyrus.Franc CF.Papyrus.Franc.Meshy Loaves
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {a b:ℕ→ℕ}{I:ℕ→Buffered.Family (tent Y H)→ℕ→ℂ}{E:ℕ→Buffered.Family (tent Y H)→ℂ}{L:Rack Λ l}{B:Clay Λ l}(D : Exhibition Y H a b I E L B)
variable (G:Tower.SatinVerification.GroundExtension (i:=a) (k:=b) (E:=E) Y H)
variable (d:Axis) (c:∀ j:Axis,Tower.Arena Y H G.history.circuit j 0 false)
variable (x:displayAlgebra Y H D.univ_ G.history G.clipped d false (c d)→⋆ₐ[ℂ] ℂ)
local notation "ψ" f:max=>evaluate Y H D.univ_ G d c (SameCharacter.resident Y H D.univ_ G d false (c d) f)
def Crème : Prop := ∀ (S:Finset Cover)(U:List Wine),AreaW false S U→ InTest (tent Y H) false S false (dek (tent Y H) U) → Tower.CovCover (tent Y H) (dek (tent Y H) U) → ∀ ε > (0:ℝ),∀ᶠ n:ℕ in atTop,∀ f:displayAlgebra Y H D.univ_ G.history G.clipped d false (c d)→⋆ₐ[ℂ] ℂ, ‖(ψ f) n (dek (tent Y H) U)-tallyW U‖≤ε
lemma Crème.charted (X:Crème Y H D G d c) {S F} (h:InTest (tent Y H) false S false F) (e:CovCover (tent Y H) F): ∃ U:List Wine,AreaW false S U∧ F=dek (tent Y H) U ∧
    Tendsto (fun n=>(ψ x) n F) atTop (𝓝 (tallyW U)):=by
 obtain ⟨U,b,w⟩:=recipe h; subst F; refine ⟨U,b,rfl,Metric.tendsto_nhds.mpr (fun ε p=>?_)⟩; filter_upwards [X S U b h e (ε/2) (half_pos p)] with n t; rw [dist_eq_norm]; exact lt_of_le_of_lt (t x) (half_lt_self p)
theorem cantabile (ε η:ℝ)(p:0<η)(r:ℕ)(e:0<r)(U:Supplier):
    ∃ P l Z H Y q d w C a b I E L B T t X G c pan s ζ f f' sample,
      Election ε η U P l Z H Y q d w C a b I E L B T t X G c pan s ζ f f' sample ∧ Crème Y H X.toExhibition G 0 c ∧ Pitching.Focus.FairRoute P.P P.J P.h P.N0 Push.SectorMeasure.Chi.canonical ∧
      ∃ (u:ℕ→ℕ)(Kp:ℕ→Bool→ Buffered.Family (tent Y H)→ Buffered.Family (tent Y H))(Q:GradesAll (i:=a) (a:=G.rows) (k:=b) (b:=G.columns) Y H u Kp),
      ∃ (A D:ℕ) (v:Cover), ∀ ρ >(0:ℝ),∀ᶠ n:ℕ in atTop,∀ C':Fin 3,
         let F:=auger (tent Y H) A C'; let H':=latticeFieldEstimates (tent Y H) v A D C'; let S₀:= {nodeC (Seat5 A)}; let S:=snowF v A D;
         footprint P l n S₀ ⊆ Metric.ball 0 ρ ∧ footprint P l n S⊆ Metric.ball 0 ρ ∧
         ∀ j:Axis,∃ z:ℤ, Lantern Y H X.toExhibition G u Q 0 j c (pan.character sample) n S₀ S F H' z r ∨ Lantern Y H X.toExhibition G u Q 0 j c (pan.character sample) n S S₀ H' F z r :=by
 obtain ⟨u,uh,k,v⟩:= winter 4 (by decide); obtain ⟨X,s,w,e'⟩:= Meshy.vanguard; obtain ⟨C,c,p'⟩:= grantH 4 (by decide)
 let σ:= min (min η X) u
 let V:Supplier:=fun A P b y S t L w D q k M=> max (U A P b y S t L w D q k M) (CF.Papyrus.Franc.charge C)
 obtain ⟨P,l,Z,H,Y,q,d,Λ,C',a,b,I,E,L,B,T,t,G,Q,R,Wp,h',ζ,f,f',m,h₀,H₀,s₀⟩:= capacitor ε σ (lt_min (lt_min p s) uh) r e V
 have hv:P.d ≤ X:= h₀.d_le.trans ((min_le_left ..).trans (min_le_right ..))
 have ht:P.d ≤ u:= h₀.d_le.trans (min_le_right ..)
 refine ⟨P,l,Z,H,Y,q,d,Λ,C',a,b,I,E,L,B,T,t,G,Q,R,Wp,h',ζ,f,f',m,{h₀ with d_le:= h₀.d_le.trans ((min_le_left ..).trans (min_le_left ..)), decorate_le := (le_max_left ..).trans h₀.decorate_le },fun S A Kx y z ε p=>?_,H₀,s₀⟩
 apply rindV Y H G.toExhibition Q 0 R h₀.korn.extent H₀ (P.kJ.symm ▸ p') c.le ((le_max_right ..).trans h₀.decorate_le) ht _ _ Kx y z ε p
 · rw [P.kJ]; exact ⟨_,v⟩
 exact (eventually_ge_atTop w).mono (fun i h n g=>e' _ P.dpos.le hv _ (h.trans g))
end YM.CF.Py.Rate.LocalLimit.Papal
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.cantabile
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.Crème.charted
#check @YM.CF.Py.Rate.LocalLimit.Papal.cantabile
