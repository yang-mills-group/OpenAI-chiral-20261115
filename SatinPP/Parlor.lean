import SatinPP.Lantern

set_option autoImplicit false
set_option maxHeartbeats 120000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
set_option maxRecDepth 4500
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Aria
open Hierarchy.Celeritas Land Hierarchy.Seld.Leal
variable (P:Spine)(x:P.Spectrum0 3)
open Germ Alliance Selected FirstWindows

variable (j:Axis)
local notation "C" => P.room
abbrev chateau :=
 Selected.displacement P.run P.large P.law P.history P.projection.clipped 3 false (P.room 3)
     (P.glasshouseCharacter 3 x) j (P.room j)
local notation "χ"=>P.chateau x j
abbrev sitting:= indoor P.run P.large P.law P.history P.projection.clipped j false (P.room j) (P.chateau x j)
local notation "L"=>P.sitting x j
local notation "ξ"=>P.advocate 3 x j
local notation "H"=>P.ColorHil j (P.advocate 3 x j)
local notation "B" s:max f:max=> Selected.bud P.run P.large P.law s P.history P.projection.clipped j false (C j) (χ) f
local notation "ℱ"=>P.voxTest j

lemma parlorGr (s:ℕ)(f g:P.naturalVox j s):
  inner ℂ (P.province j ξ s f) (P.province j ξ s g)=
  inner ℂ (B s f.val) (B s g.val):=by
 rw [← (P.gnsIn j ξ).inner_map_map,P.coincides,P.coincides,P.gram_at, Selected.earns]

 have h(q:P.Test):P.singleState j s ξ q=Selected.response P.run P.large P.law s P.history P.projection.clipped j false (C j) (χ) (P.glasshouseMark q):=by
    unfold chateau;rw [across_response];exact P.single_agrees 3 j x s q
 rw [h];rfl
lemma parlor_rise (s t:ℕ)(p:s≤t)(f:P.naturalVox j s):
 ∃ g:P.naturalVox j t, P.province j ξ t g=P.province j ξ s f ∧ B t g.val=B s f.val:=by
 refine ⟨⟨Raise P.run P.large P.history.circuit j 0 false s t p f.val,P.refine_keeps s (P.voxTest j s _) f.property _⟩,
          (P.gnsIn j ξ).injective ?_,Selected.flourishes _ _ _ s _ _ _ _ _ _ t p _⟩
 rw [P.coincides,P.coincides,P.refine_vox]

lemma toParlor (s:ℕ)(f:Tower.Field P.run P.large s j 0 true): ∃ b:P.naturalVox j s,b.val=admit P.run P.large s j f:=
 ⟨⟨admit _ _ _ _ f, (purpose_ok .. |>.mp f.property).2 rfl⟩,rfl⟩
lemma parlorEq : ∃ Z:H ≃ₗᵢ[ℂ] L,∀s,∀f:P.naturalVox j s,Z (P.province j ξ s f)=B s f.val:=by
 let A:=Sigma (P.naturalVox j)
 let a:A → H :=fun i=>P.province j ξ i.1 i.2
 let b:A → L :=fun i=>(Selected.bud P.run P.large P.law i.1 P.history P.projection.clipped j false (C j) (χ) i.2.val)
 have h:Set.range a=⋃s,Set.range (P.province j ξ s):=by
    ext z;constructor
    · rintro ⟨⟨s,f⟩,rfl⟩;exact Set.mem_iUnion.mpr ⟨s,f,rfl⟩
    intro e;obtain ⟨s,f,rfl⟩:=Set.mem_iUnion.mp e; exact ⟨⟨s,f⟩,rfl⟩
 have da:Dense ((Submodule.span ℂ (Set.range a)):Set H):= h.symm ▸ P.native_dense j ξ
 have db:Dense ((Submodule.span ℂ (Set.range b)):Set L):=
   ((reserved_actor P.run P.large P.law P.history P.projection.clipped j (C j) (χ)).mono (show _⊆Set.range b from fun y hy=>by
      obtain ⟨s,f,rfl⟩:=Set.mem_iUnion.mp hy
      obtain ⟨v,e⟩:=P.toParlor j s f
      exact ⟨⟨s,v⟩,by dsimp [b];rw [e]⟩)).mono Submodule.subset_span
 obtain ⟨Z,z⟩:=intertwine (A:=H) («B»:=L) a b da db (fun x' y=>by
    obtain ⟨u,p,q⟩:=P.parlor_rise x j _ (max x'.1 y.1) (le_max_left ..) x'.2
    obtain ⟨v,m,n⟩:=P.parlor_rise x j _ (max x'.1 y.1) (le_max_right ..) y.2
    dsimp only [a,b]
    rw [←p,←q,←m,←n,P.parlorGr])
 exact ⟨Z,fun s f=>z ⟨s,f⟩⟩
def revolving := (parlorEq P x j).choose
lemma spins_bud(s:ℕ)(f:P.naturalVox j s):
 P.revolving x j (P.province j ξ s f)= B s f.val:=(parlorEq P x j).choose_spec s f
lemma spins_face(t:ℕ)(f:P.Test)(e:P.birthF j t f):
 P.revolving x j (P.viewF j ξ t e)=B t (P.emmigrant j t e).val:= P.spins_bud x j t _
lemma libretto (t:ℕ)(f:P.Test)(e:P.birthF j t f):
 f ∈ insideAt P.par P.width P.calibration true (flank j 0) t:= by
 obtain ⟨G,rfl⟩:=e
 refine (positive_today P.run P.large j t _).mpr ((purpose_ok ..).mpr ⟨
   ((purpose_ok ..).mp G.val.property).1,fun _=> G.property⟩)
abbrev ticketlet:=ticket P.run P.large P.projection
abbrev darkHalf:=Domain P.run P.large P.projection true
abbrev litKet:=physicalKet P.run P.large P.law P.projection j (C j) (χ)
lemma librettoHalf (t:ℕ)(f:P.Test)(e:P.birthF j t f):
 P.ticketlet t f ∈ P.darkHalf (flank j 0) := ticket_mem _ _ _ (P.libretto j t f e)
lemma parlor_birth(t:ℕ)(f:P.Test)(e:P.birthF j t f):
 P.litKet x j ⟨P.ticketlet t f,P.librettoHalf j t f e⟩ = P.revolving x j (P.viewF j ξ t e):=by
 rw [P.spins_face]
 have h:=P.libretto j t f e
 refine Eq.trans (physical_enclose P.run P.large P.law P.projection j (C j) (χ) t ⟨f,h⟩)
   ?_
 refine congrArg _ (Subtype.ext ?_)
 exact congrArg (fun y:P.Test=>y.val) (P.documented j t e).symm
#print axioms parlor_birth
