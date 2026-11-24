import YM.SU5.Reconstruct.Postage
set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 620000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Tapestry Tapestry.Altitude PhaseChoice
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
open Tower.Selected Set MeshClock Tapestry.Exhibition
open SelectionAnalysis Vacancy.Average
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  {L:Rack Λ l}{B:Clay Λ l}{T:ℕ→ℕ→Tariff}{t:ℕ→Tariff}(D:Fashion Y H i k I E L B T t)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
local notation "Dₚ" => D.toExhibition
local notation "V" => D.univ_
local notation "Q" => G.history
local notation "Qt" => G.clipped
local notation "χ" => Dome (tent Y H)
local notation "O" => Altitude.Cloud (Dome (tent Y H))
local notation "P₀" s:max => vistaFinish Y H s (Dₚ)

/-!
# Factorization-style colimit with locations

This is an explicit equivalence relation on the common determining local polynomials
(mention region through Pol U). Disjoint products make sense also **up to this relation**,
not insisting on multiplicativity of RG. Not a C*-algebra of Minkowski observables.
Linear lifts, common action of arbitrary physical mesh displacements, EUCLIDEAN, all output
representatives in Pol U, canonical qualification agreed at all higher rungs. Can always
lift to arbitrary Admission in the appointment. Stated with this relation (setoids not
used downstream). -/

local notation "â" k:max p:max => parcelTo Y H D k p
local notation "m₀" k:max=> meshPos Λ k
local notation "X₀"=>physPos Λ

def Concurrent (x y: Altitude.Cloud (Dome (tent Y H))): Prop:= ∀ᶠ n:ℕ in atTop, vistaFinish Y H n D.toExhibition x=vistaFinish Y H n D.toExhibition y
local notation "Cq"=> Concurrent Y H D
lemma conc_self (x:O) : Concurrent Y H D x x:= Eventually.of_forall fun _=> rfl
lemma conc_exchange {x y:O}(h:Concurrent Y H D x y) : Concurrent Y H D y x := h.mono fun _ p=>p.symm
lemma conc_close {x y z:O}(h:Concurrent Y H D x y)(p:Cq y z) : Concurrent Y H D x z:= (h.and p).mono fun _ u=> u.1.trans u.2
lemma conc_add {x y x' y':O}(h:Concurrent Y H D x y)(p:Cq x' y') : Concurrent Y H D (x+x') (y+y'):= (h.and p).mono fun i u=>by rw [map_add,map_add,u.1,u.2]
lemma conc_scale {x y:O}(h:Concurrent Y H D x y)(a:ℂ) : Concurrent Y H D (a • x) (a • y):= h.mono fun i p=>by rw [map_smul,map_smul,p]

lemma eventually_inside {x:O}{U:Set RSpace}(p:x∈Pol Y H U) : ∀ᶠ n:ℕ in atTop,x∈ PolAt Y H n U:= mem_atTop_sets.mpr ⟨_,fun i u=> polAt_up Y H u (levels Y H p).choose_spec⟩

include G in
lemma conc_mul {u v:Set RSpace}(p:Disjoint u v)(x x':Pol Y H u)(y y':Pol Y H v)(h:Cq x.val x'.val)(b:Cq y.val y'.val) : Concurrent Y H D (x.val*y.val) (x'.val*y'.val) := by
 unfold Concurrent
 filter_upwards [h,b,eventually_inside Y H x.property,eventually_inside Y H y.property, eventually_inside Y H x'.property,eventually_inside Y H y'.property] with i t g u v u' v'
 rw [depart_pair Y H D.univ_ G D.toExhibition ((well_spec ..).1 u).1 ((well_spec ..).1 v).1 (Disjoint.preimage _ p), depart_pair Y H D.univ_ G D.toExhibition ((well_spec ..).1 u').1 ((well_spec ..).1 v').1 (Disjoint.preimage _ p), t,g]
lemma conc_read (C:∀j:Axis, Tower.Arena Y H G.history.circuit j 0 false) (c:displayAlgebra Y H V G.history G.clipped 0 false (C 0)→⋆ₐ[ℂ]ℂ){U V':Set RSpace}(x:Pol Y H U)(y:Pol Y H V')(p:Cq x.val y.val) : sch Y H D G C c x.val= sch Y H D G C c y.val:=by
 obtain ⟨n,h,t,g⟩:= (p.and ((eventually_inside Y H x.property).and (eventually_inside Y H y.property))).exists; rw [sch_mark Y H D G C c n (inside_budget Y H t),sch_mark Y H D G C c n (inside_budget Y H g),h]
lemma contHeight {Λ:Preparation}(z:placement Λ) : ∀ᶠ n in atTop,∃ v:Cover, meshPos Λ n v=z:=by
 obtain ⟨t,u,v,h⟩:= necklace 0 z
 filter_upwards [eventually_ge_atTop t] with i p; exact ⟨netcast Λ t i v,(netcast_up Λ t i p v).trans (funext h)⟩
variable (U:Set RSpace)
local notation "P" x:max=> Pol Y H x
local notation "Pn" k:max x:max=> PolAt Y H k x
local notation "φ" x:max y:max=>carried (X₀ x) y -- x node

def Animates (z:placement Λ)(x y:O) : Prop:= ∀ᶠ n in atTop,∀ v:Cover,z=(meshPos Λ n) v → (P₀ n) y=march Y H v ((P₀ n) x)
local notation "A₀" z:max=>Animates Y H D z
lemma animates_ext {x y x' y':O}{v:placement Λ}(p:(A₀ v) x y)(h:Cq x x')(q:Cq y y') : Animates Y H D v x' y':=(p.and (h.and q)).mono fun i t w u=>by rw [←t.2.1,←t.2.2]; exact t.1 w u -- A₀ syntax need parentheses
lemma stable {x:O} : Animates Y H D 0 x x:= Eventually.of_forall fun i w u=>by
 have hw:w=0 := meshpos_inj Λ i (u.symm.trans (map_zero (meshPos Λ i)).symm)
 rw [hw,march_ground]
lemma drive_together {x y z:O}{v u:placement Λ}(p: Animates Y H D v x y)(t:Animates Y H D u y z): Animates Y H D (u+v) x z:=by
 unfold Animates; filter_upwards [p,t,contHeight v,contHeight u] with i q h f a; obtain ⟨y',hy⟩:= f; obtain ⟨w,hw⟩:=a; intro U eq
 rw [show U=w+y' from meshpos_inj Λ i (by rw [map_add,hw,hy]; exact eq.symm),←march_add,←q y' hy.symm]; exact h w hw.symm -- orientation? needed <-q
lemma animates_does {x y y':O}{v:placement Λ}(p: Animates Y H D v x y)(q:Animates Y H D v x y') : Concurrent Y H D y y':= (p.and (q.and (contHeight v))).mono fun i t=> (t.1 t.2.2.choose t.2.2.choose_spec.symm).trans (t.2.1 t.2.2.choose t.2.2.choose_spec.symm).symm
include G
lemma parcel_animates {x:O}{n:ℕ}(p:x∈PolAt Y H n U)(v:Cover) : Animates Y H D ((meshPos Λ n) v) x (parcelTo Y H D n v x):=mem_atTop_sets.mpr ⟨n,fun i u w p'=> by
  rw [show w=netcast Λ n i v from meshpos_inj Λ i (p'.symm.trans (netcast_up Λ n i u v).symm)]
  exact talliedUp Y H D G _ _ _ u p⟩
lemma animates_exists (z:placement Λ)(x:Pol Y H U): ∃ y: Pol Y H (carried (physPos Λ z) U), Animates Y H D z x.val y.val:= by
 obtain ⟨n,p,v,hv⟩:= ((eventually_inside Y H x.property).and (contHeight z)).exists; subst z; exact ⟨⟨_, pol_of_level Y H (parcel_mem Y H D v n p)⟩, parcel_animates Y H D G U p v⟩
lemma animates_read (C:∀j:Axis, Tower.Arena Y H G.history.circuit j 0 false) (c:displayAlgebra Y H V G.history G.clipped 0 false (C 0)→⋆ₐ[ℂ]ℂ){V':Set RSpace}(x:Pol Y H U)(y:Pol Y H V')(z:placement Λ)(p: Animates Y H D z x.val y.val) : sch Y H D G C c x.val= sch Y H D G C c y.val:=by
 obtain ⟨n,h,t,g,l,v⟩:= (p.and ((eventually_inside Y H x.property).and ((eventually_inside Y H y.property).and (contHeight z)))).exists
 rw [sch_mark Y H D G C c n (inside_budget Y H t),sch_mark Y H D G C c n (inside_budget Y H g),h _ v.symm, marchOut,world_still]
lemma animate_field_adj {j:Axis}{x y:Pol Y H U}(u:Concurrent Y H D x.val y.val)(v:U⊆flank j 0)(C:∀j:Axis, Tower.Arena Y H G.history.circuit j 0 false)(c:displayAlgebra Y H V G.history G.clipped 0 false (C 0)→⋆ₐ[ℂ]ℂ)
    {s t:ℕ}(p:x.val∈Pn s U)(q:y.val∈Pn t U) : locatePoly Y H D G C c j s ⟨x.val,isotone Y H v p⟩ = locatePoly Y H D G C c j t ⟨y.val,isotone Y H v q⟩:=by
 obtain ⟨r,h,a,b⟩:= (u.and ((eventually_ge_atTop s).and (eventually_ge_atTop t))).exists
 have hx:=polAt_up Y H a (isotone Y H v p); have hy:=polAt_up Y H b (isotone Y H v q)
 rw [←located_higher Y H D G C c j a _ hx,←located_higher Y H D G C c j b _ hy]; exact congrArg (fun z=> arriving Y H V r Q Qt j false (C j) (inAxis Y H D G C c j) (widenInput Y H j r z)) (show preparePoly Y H D j r ⟨_,hx⟩=preparePoly Y H D j r ⟨_,hy⟩ from Subtype.ext (congrArg (fun x:Dome K=> x.val) h))
omit G
lemma animates_add {x y x' y':O}{v:placement Λ}(p: Animates Y H D v x y)(q:Animates Y H D v x' y') : Animates Y H D v (x+x') (y+y'):= (p.and q).mono fun i u w p=> by rw [map_add,map_add,map_add,u.1 w p,u.2 w p]
lemma animates_scale (a:ℂ){x y:O}{v:placement Λ}(p: Animates Y H D v x y): Animates Y H D v (a • x) (a • y):= p.mono fun i u w p=> by rw [map_smul,map_smul,map_smul,u w p]
include G
lemma animates_factors {W:Set RSpace}(t:Disjoint U W)(v:placement Λ)(x:P U)(y:P W)(x':Pol Y H (carried (physPos Λ v) U))(y':Pol Y H (carried (physPos Λ v) W))(p:Animates Y H D v x.val x'.val)(q:Animates Y H D v y.val y'.val) : Animates Y H D v (x.val*y.val) (x'.val*y'.val):=by
 unfold Animates; filter_upwards [p,q,eventually_inside Y H x.property,eventually_inside Y H y.property, eventually_inside Y H x'.property,eventually_inside Y H y'.property] with i p q a b a' b'
 intro w h
 rw [depart_pair Y H D.univ_ G D.toExhibition ((well_spec ..).1 a).1 ((well_spec ..).1 b).1 (Disjoint.preimage _ t),depart_pair Y H D.univ_ G D.toExhibition ((well_spec ..).1 a').1 ((well_spec ..).1 b').1 (Disjoint.preimage _ (carried_disjoint _ t)),map_mul,p w h,q w h]
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
