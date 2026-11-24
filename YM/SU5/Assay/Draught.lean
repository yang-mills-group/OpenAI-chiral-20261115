import YM.SU5.Assay.TwinJets
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
variable {P:Spine}{j:Axis}{s v w:ℕ}{f g:P.Test}
local notation "Λ"=> P.par
local notation "Y"=> P.run
local notation "K"=> P.calibration
local notation "H"=> P.large
local notation "b"=> ruler (Λ).block
local notation "V"=> P.law
local notation "L"=> (Λ).R.L.val
local notation "π"=> P.history
local notation "Qt"=> P.projection.clipped
local notation "C₀"=> P.room j
local notation "σ"=> P.shifts j

local notation "μ"=> P.meanBox
local notation "ν"=> P.euclOp
local notation "T"=> P.shiftOp
local notation "Ν"=> whenly (timeMesh (Λ))
local notation "Ω"=> P.floorVec
local notation "S"=> enclave K
/-!
## Preparing by the very measurements under consideration

Reserve time collars if desired. Same height `s`. `X` are the claims
in a caliper `[0,w]` (when using a caliper elsewhere take time coordinates
relative to that). No charged-measurement syntactic assumption needed either.
-/
/-- Spectator grammar. Cost `[0,v]`, arbitrary transverse extension.
 Including heat `n` reserved either side of each new bill. -/
inductive Placard (P:Spine)(j:Axis)(w n:ℕ)(X:Set P.Test): ℕ→ P.Test → Prop
 | blank {a:ℕ}:0<a→ Placard P j w n X a 1
 | facing {y:P.Test}:y∈X→ P.BEntry j w y → Placard P j w n X (n+w+n) (P.shifts j n y)
 | pay{y:P.Test}{a:ℕ}:Placard P j w n X a y → (z:ℂ) → Placard P j w n X a (z•y)
 | add{y z:P.Test}{a:ℕ}:Placard P j w n X a y → Placard P j w n X a z →Placard P j w n X a (y+z)
 | cross{y:P.Test}{a:ℕ}:Placard P j w n X a y → (d:Trans j)→(z:ℤ) → Placard P j w n X a (P.shifts d z y)
 | turn{y:P.Test}{a:ℕ}:Placard P j w n X a y → Placard P j w n X a (P.riposte j a y)
 | both{y z:P.Test}{a c:ℕ}:Placard P j w n X a y → Placard P j w n X c z →Placard P j w n X (a+c) (y*P.shifts j a z)
variable {a n:ℕ}{X:Set P.Test}
local notation "D"=>P.Placard j w n X
lemma Placard.earns (p:D a f):P.BEntry j a f:=by
 induction p with
 | blank h=> exact BEntry.one P j h
 | facing _ h=>exact h.pad n n
 | pay _ _ h=>exact h.smul _
 | add _ _ p q=> exact p.add q
 | cross _ _ _ h=>exact h.across ..
 | turn _ h=>exact h.riposte
 | both _ _ p q=> exact p.concat q
lemma Placard.keeps (p:D a f)(e:∀y∈X,y∈ S): f∈ S:=by
 induction p with
 | blank h=> exact one_mem _
 | facing u _=>exact P.shifts_keep j _ (e _ u)
 | pay _ _ h=>exact (S).smul_mem h _
 | add _ _ p q=> exact (S).add_mem p q
 | cross _ _ _ h=>exact P.shifts_keep _ _ h
 | turn _ h=>exact riposte_keeps h
 | both _ _ p q=> exact (S).mul_mem p (P.shifts_keep _ _ q)
lemma Placard.trailing (p:D a f)(k:ℕ):D (a+k) f:=by
 rcases Nat.eq_zero_or_pos k with rfl|h
 · exact p
 simpa using p.both (Placard.blank h)

variable (P j s w n X) in
def procession:Submodule ℂ (P.Hil j) where
 carrier:={y | ∃ a f,D a f∧μ j s a f (Ω j)=y}
 add_mem':=by
   rintro _ _ ⟨a,f,p,rfl⟩ ⟨k,g,q,rfl⟩
   have u:D (a+k) g:=Nat.add_comm k a ▸ q.trailing a
   refine ⟨a+k,f+g,(p.trailing k).add u,?_⟩
   rw [meanBox_add s (p.trailing k).earns u.earns,add_apply,meanBox_right s p.earns, Nat.add_comm a k,meanBox_right s q.earns,
    ContinuousLinearMap.mul_apply,P.heat_floor,ContinuousLinearMap.mul_apply,P.heat_floor]
 zero_mem':=by
   have p:D 1 1:=Placard.blank one_pos
   refine ⟨1,_,p.pay 0,?_⟩
   rw [meanBox_smul s p.earns,zero_smul,zero_apply]
 smul_mem':=by
   rintro z _ ⟨a,f,p,rfl⟩
   refine ⟨_,_,p.pay z,?_⟩
   rw [meanBox_smul s p.earns];rfl

variable (P j s w n X) in
def trail := (P.procession j s w n X).topologicalClosure
local notation "A"=>P.trail j s w n X
local notation "B"=>P.procession j s w n X
variable (P j s w n X)
instance : (P.trail j s w n X).HasOrthogonalProjection:=by unfold trail; infer_instance
lemma trails (g:(P.Hil j).Op)(h:∀y∈ B,g y∈ B):∀y∈A,g y∈A:=
 Set.MapsTo.closure h g.continuous
variable {P j w n X}
lemma trails_draught (p:D a f): ∀y∈A, μ j s a f y∈A:=by
 apply P.trails
 rintro _ ⟨_,_,h,rfl⟩
 exact ⟨_,_,p.both h,DFunLike.congr_fun (meanBox_concat s p.earns h.earns) _⟩

variable (P j w n X)
lemma trails_start : Ω j∈A:=by
 apply Submodule.le_topologicalClosure
 refine ⟨1,1,Placard.blank one_pos,?_⟩
 rw [meanBox_unit s _ _ one_pos];exact P.heat_floor j _
lemma trails_move (d:Trans j)(z:ℤ): ∀y∈A,T j (s,z,d) y∈A:= by
 apply P.trails
 rintro _ ⟨l,f,p,rfl⟩
 refine ⟨_,_,p.cross d z,?_⟩
 calc
  _ = ((μ j s l _)*T j (s,z,d)) (Ω j):=by rw [ContinuousLinearMap.mul_apply,P.floor_moves]
  _ = _ := by rw [←meanBox_across s p.earns d z];rfl
lemma trail_project :∀y∈A,P.inHil j (P.piZero j y)∈A:=by
 have g:D 1 1:=Placard.blank one_pos
 have h:=trails_draught s g
 rw [meanBox_unit s _ _ one_pos] at h
 exact fun y p=> P.frame_project j s _ h (P.trails_move j s w n X) p
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
