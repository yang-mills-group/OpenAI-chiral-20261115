import YM.SU5.Twilight.Equitable
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
variable (P: Spine) (j:Axis) (x:P.Spectrum0 j)
local notation "π"=> P.pinJoint j
local notation "ω"=> P.colorZero j x
local notation "M"=> timeMesh P.par
local notation "Γ"=> marks M
local notation "N"=> notch M
local notation "ν"=> daylight M
local notation "κ"=> P.voyageF j x
local notation "V" i:max=> ((κ).crew i).play
local notation "Ω"=> P.heaven j x
local notation "ω'"=> P.bank j x
local notation "ϑ"=> P.enter j x
open WeakDual TopologicalSpace
open scoped Pointwise
local notation "Y"=> P.run
local notation "VH"=> P.law
local notation "T"=>P.par
local notation "Z"=>P.history.circuit
local notation "h"=>P.large
local notation "K"=>P.calibration
local notation "Φ" i:max=> P.reflectTest i
local notation "Ξ" i:max=> P.shifts i
local notation "W"=> enclave K
local notation "Γr" t:max=> P.conveying t
local notation "ℓ"=> P.calibration.ℓ
variable (s t:ℕ)
open Tapestry SlabMark
-- geometric relation AFTER purchase
/-- represented by a naturalVox at orientation j. -/
abbrev birthF (p:P.Test): Prop:= ∃ f:P.naturalVox j s,P.voxTest j s f.val=p
abbrev emmigrant {f:P.Test} (p:P.birthF j s f): P.naturalVox j s:= p.choose
lemma documented {f:P.Test} (p:P.birthF j s f): P.voxTest j s (P.emmigrant j s p).val=f:= p.choose_spec
lemma assignedS {f:P.Test} {p:P.birthF j s f}(g:P.naturalVox j s) (e:P.voxTest j s g.val=f) : P.emmigrant j s p=g:=
 Subtype.ext (Subtype.ext (congrArg (fun v:P.Test=>v.val) ((P.documented j s p).trans e.symm)))
def viewF {f:P.Test} (p:P.birthF j s f):P.ColorHil j x:=P.province j x s (P.emmigrant j s p)
lemma holdsF {f:P.Test} (p:P.birthF j s f)(g:P.naturalVox j s)(δ : P.voxTest j s g.val=f):P.viewF j x s p=P.province j x s g:=by rw [viewF,P.assignedS _ _ _ δ]
lemma criteria {f:P.Test}{S:Finset Cover}(e:f∈ bay K S true)(q:Tower.region j 0 (ℓ) S)(p:f∈ W): P.birthF j s f:= ⟨⟨P.positiveVox j s S f e q,p⟩,rfl⟩
lemma toll_up (b:P.naturalVox j s)(g:s≤t): (Γr s) (t-s) (P.voxTest j s b.val)= P.voxTest j t (Raise Y h Z j 0 false s t g b.val):= rfl
lemma rig {f:P.Test} (p:P.birthF j s f)(u:s≤t): P.birthF j t (P.conveying s (t-s) f):= by
 obtain ⟨g,rfl⟩:=p; exact ⟨⟨Raise Y h Z j 0 false s t u g.val,P.refine_keeps s _ g.property (t-s)⟩, (P.toll_up j s t g u).symm⟩
lemma view_rig {f:P.Test} (p:P.birthF j s f)(u:s≤t): P.viewF j x t (P.rig j s t p u)=P.viewF j x s p:=by
 obtain ⟨g,rfl⟩:=p; let b:P.naturalVox j t:= ⟨Raise Y h Z j 0 false s t u g.val,P.refine_keeps s _ g.property (t-s)⟩
 rw [P.holdsF j x s _ g rfl,P.holdsF j x t _ b ((P.toll_up j s t g u).symm)]; apply (P.gnsIn j x).injective; rw [P.coincides,P.coincides]; exact P.refine_vox j x s t u _
variable (k:Axis)
local notation "ι"=> castor (timeMesh T)
lemma walk_rig (b:ℤ)(f:P.Test):(Γr s) (t-s) ((Ξ k) b f)= (Ξ k) (ι s t b) ((Γr s) (t-s) f):=by
 apply Subtype.ext; let r:= P.par.R.L.val; change stream Y h P.projection.refine s (t-s) (chime K k (Heat.gaugeShift P.par.block (2*b)) _) = chime K k (Heat.gaugeShift P.par.block (2*((r:ℤ)^(t-s)*b))) _
 rw [chime_X Y h VH s k (2*b) Z ((marque ..).1 f.property) (t-s)]; congr 2; unfold r; ring
lemma reflUp (f:P.Test) : (Γr s) (t-s) ((Φ k) f)=(Φ k) ((Γr s) (t-s) f):=by
 apply Subtype.ext; change stream Y h P.projection.refine s _ (mirror K k 0 f.val)= _; rw [stream_flipped Y h Z s (t-s) k 0 ((marque ..).1 f.property),mul_zero]; rfl
lemma march (b:ℤ)(c:ℤ)(f:P.Test): (Ξ j) b ((Ξ k) c f)=(Ξ k) c ((Ξ j) b f):=Subtype.ext (twin_slide j k _ _ ((marque ..).1 f.property).paid.choose_spec)
lemma meetrefl (b:ℤ)(f:P.Test)(g:j≠k) : (Ξ j) b ((Φ k) f)=(Φ k) ((Ξ j) b f):= Subtype.ext (straddle j k g _ _ ((marque ..).1 f.property).paid.choose_spec)
lemma meetOwn (b:ℤ)(f:P.Test):(Φ j) ((Ξ j) b f)= (Ξ j) (-b) ((Φ j) f):=Subtype.ext (mirror_relocate K j b 0 ((marque ..).1 f.property)) -- syntax
variable {k}
lemma sailImg (a:k≠j)(b:ℤ)(z:P.naturalVox j s): P.voxTest j s (sail Y h s j 0 false k a (2*b) z.val) = P.shifts k b (P.voxTest j s z.val) := rfl
lemma sailNatur (a:k≠j)(b:ℤ)(z:P.naturalVox j s): P.voxTest j s (sail Y h s j 0 false k a (2*b) z.val)∈ enclave P.calibration:= by rw [P.sailImg]; exact P.shifts_keep k b z.property

lemma passes (a:k≠j)(b:ℤ){f:P.Test}(p:P.birthF j s f): P.birthF j s ((Ξ k) b f):=by obtain ⟨z,rfl⟩:=p; exact ⟨⟨sail Y h s j 0 false k a (2*b) z.val,P.sailNatur j s a b z⟩, P.sailImg j s a b z⟩
set_option maxHeartbeats 600000 in
lemma released (a:k≠j)(b:ℤ){f:P.Test}(p:P.birthF j s f): P.viewF j x s (P.passes j s a b p)=(P.colorSpace j x (P.walksColor j (s,b,⟨k,a⟩))) (P.viewF j x s p):=by
 obtain ⟨z,rfl⟩:=p; let A:P.naturalVox j s:= ⟨sail Y h s j 0 false k a (2*b) z.val,P.sailNatur j s a b z⟩
 rw [P.holdsF j x s _ z rfl,P.holdsF j x s _ A (P.sailImg j s a b z)]; apply (P.gnsIn j x).injective; rw [P.moveTransit,P.coincides,P.coincides]; exact (P.move_use j x s ⟨k,a⟩ b _).symm
lemma wishing (g:P.naturalVox j s)(n:ℕ): (Ξ j) n (P.voxTest j s g.val)= P.voxTest j s (tick Y h s j 0 false (2*n) g.val):=Subtype.ext (timed_apply ..).symm
lemma passesLater (n:ℕ){f:P.Test}(p:P.birthF j s f): P.birthF j s ((Ξ j) n f):=by
 obtain ⟨z,rfl⟩:=p; refine ⟨⟨tick Y h s j 0 false (2*n) z.val,?_⟩, (P.wishing j s z n).symm⟩; rw [←P.wishing ..]; exact P.shifts_keep j (n:ℤ) z.property -- syntax
lemma releasedLater (b:ℕ){f:P.Test}(p:P.birthF j s f): P.viewF j x s (P.passesLater j s b p)= (P.physicalEnergy j x).E (whenly M s b) (P.viewF j x s p):=by
 obtain ⟨z,rfl⟩:=p; let A:P.naturalVox j s:= ⟨tick Y h s j 0 false (2*b) z.val,by rw [←P.wishing ..]; exact P.shifts_keep j b z.property⟩
 rw [P.holdsF j x s _ z rfl,P.holdsF j x s _ A (P.wishing j s z b).symm]; apply (P.gnsIn j x).injective; change _=P.gnsIn j x (P.warming j x _ _); rw [P.warmTransit,P.coincides,P.coincides]; exact P.moves_p .. -- unif?
lemma released_gram {f g:P.Test}(p:P.birthF j s f)(q:P.birthF j s g): inner ℂ (P.viewF j x s p) (P.viewF j x s q)=P.singleState j s x ((Φ j) f*g):=by
 unfold viewF; rw [←(P.gnsIn j x).inner_map_map,P.coincides,P.coincides,P.gram_at,P.documented,P.documented]
lemma faceUnit : P.birthF j s 1:=⟨⟨unity Y h j 0 false s,P.firstVox j s⟩,rfl⟩
-- enough geometry retained by slabs; can move and pay exact selection scenario 
lemma walk_ine {b:ℤ} (p:0 ≤ b){f:P.Test}(u: P.birthF j s f): P.birthF j s ((Ξ j) b f):= (by nth_rw 1 [← Int.toNat_of_nonneg p]; exact P.passesLater j s _ u) -- name
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
