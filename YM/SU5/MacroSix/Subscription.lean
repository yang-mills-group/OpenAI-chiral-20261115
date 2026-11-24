import YM.SU5.MacroSix.Stays
import YM.SU5.Hiro.Michelin

/-! # Supporting even the stronger footprint of the apparatus

The inputs to our response theorem are on `P` and its predictions:
`Chosen` hypotheses as in our transport CP2, also available directly by `Prototype.summit`.
This **alternative/extra** payer may be useful: we demonstrate obtaining all the
course/h labels with the additional `Prepared` and `Usable` assumptions, in case
of applying the theorem with the physical prefix strength in the construction notes.
Then for **any** such uniform prefix we show supply of all our theorem's
required x certificates, not just for a different choice of the history. Still don't
quantify the reaction lower bound across elections.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4000
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
  Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste
open Designs Twah Prototype CF.Velvet CF.Pannier.Chancel Altitude
namespace Spine
variable (P : Spine) (K : P.Register) (L M : ℝ) (U : Supplier)
structure RibbonCourse : Prop where
  paid : uniform P K U L M
  usable : ∃ z, Usable (D:=P.par.δ) P.par.V P.par.W P.par.J P.par.N0 z P.par.delay P.run.meter
  prepared : ∀ i k, ((P.run.voyage i).X k).Prepared P.par.P P.par.delay
  loom : ∀ i j:ℕ, Advance.LoomLaw ((P.run.voyage i).CapeT j)
    (YM.SU5.FiniteGaugeData.Audit1102.lawRadius (VolumeCape.Dream.plot P.width).C)

-- installation (EliteAttic payer), from Tailor.lean adapted retaining also other labels.
lemma supplied (p:0<M): ∃ (P:Spine) (K:P.Register), P.RibbonCourse K L M U := by
  obtain ⟨x,c,q⟩:= Papal.audit_weather 4 (by decide)
  obtain ⟨X,l,Z,v,pL,S,Q,A0,K,H,Y,h,v',w',k,d,w,C,t,a,k',I,E,L',B,T',t',W,A⟩:= Papal.elite_attic L (min x M) (lt_min c p) U
  let V:= W.univ_; obtain ⟨G⟩:= extend_ground Y H V
  let P:Spine:=⟨X,l,Y,H,a,k',I,E,V,G⟩; obtain ⟨x',v₀⟩:=q X.d X.dpos.le (pL.trans (min_le_left ..))
  exact ⟨P,⟨(L',B,T',t'),W⟩,⟨⟨K,v,pL.trans (min_le_right ..),A,⟨k,d,w,Z,C,t,Q,S⟩,x',
    (X.kJ.symm ▸ v₀: Procurement X.K.j x' X.d)⟩, A0⟩,h,v',w'⟩ -- nesting

private lemma aboveLabels (p:ℕ→ℕ):∃ f:ℕ→ℕ,p≤f∧StrictMono f:=by
 -- cf. Diva/Uprise
 let f : ℕ→ℕ:= Nat.rec (p 0) (fun i v=>max (p (i+1)) (v+1)); exact ⟨f,fun i=> by cases i; exact le_rfl; exact le_max_left .., strictMono_nat_of_lt_succ (fun i=> show f i < max _ (f i + 1) from (Nat.lt_succ_self _).trans_le (le_max_right ..)) ⟩

-- choice of c,r before tests. Exists part of P.Chosen for ANY uniform; can also use
-- `Prototype.summit`'s output directly, no requirement *all* essential points etc in our inputs.
lemma onSupplied (v : uniform P K U L M) (z : ℕ → ℕ) :
    ∃ r : ℕ → ℕ, z ≤ r ∧ ∃ c, ∀ᵐ x∂P.pillars 3, ∃ J, P.Chosen x K c r J := by
  obtain ⟨r,h,f,q⟩ := outing v keyV keyV_positive z
  obtain ⟨c,u,p⟩ := aboveLabels f
  obtain ⟨t,e,Y⟩:= q c p u
  refine ⟨r,h,c,?_⟩
  filter_upwards [Y, P.many_stars 3 K] with x h g
  obtain ⟨J⟩:= P.ellisP 3 x K
  have pe:= P.parting 3 x K (P.homes_weather K 3 (P.all_phases 3 x g))
  exact ⟨J,t,pe,h,footway x J K pe,final_issues K J pe⟩

lemma RibbonCourse.once (v : P.RibbonCourse K L M U) (z : ℕ → ℕ) :
    ∃ r : ℕ → ℕ, z ≤ r ∧ ∃ c x J, P.Chosen x K c r J := by
  obtain ⟨r,h,c,q⟩:= onSupplied _ _ L M U v.paid z
  exact ⟨r,h,c,q.exists⟩

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
#print axioms supplied
#print axioms onSupplied
#print axioms RibbonCourse.once
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
