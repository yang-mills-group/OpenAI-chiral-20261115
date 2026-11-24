import YM.SU5.Aria.Crew
import ZecaSlide
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 320000
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
open Aria Set TopologicalSpace Metric
local notation "Λ"=> P.par
local notation "κ"=> P.calibration
local notation "ℓ"=> (κ).ℓ
local notation "R"=> ruler P.par.block
local notation "Μ"=> timeMesh P.par
local notation "N"=> notch (timeMesh P.par)
local notation "Γ"=> marks (timeMesh P.par)
local notation "H"=> P.large
local notation "Y₀"=> P.run
local notation "Φ" => P.colorSpace j x
local notation "X"=> P.ColorHil j x

local notation "E"=> (P.physicalEnergy j x).E
local notation "v" s:max => P.voxTest j s
local notation "σ"=> P.projection.clipped
local notation "C₀"=> P.room j
local notation "R₀"=> P.history
local notation "b" s:max hw:max f:max => boxOp P.run P.large P.law s P.history σ j false C₀ _ f hw

/-- T *is* firing a legitimate box for F at the specified width. -/
def Fired(s w:ℕ)(F:P.Test)(T:(P.ColorHil j x).Op):Prop:=
 ∃ (hw:0<w) (f:P.Card j s w)
   (p:P.voxTest j s f.val ∈ enclave P.calibration), P.voxTest j s f.val=F ∧
 T=P.colorSpace j x (P.door j s w hw f p)


private lemma pearl {A:Type}[CStarAlgebra A][PartialOrder A][StarOrderedRing A]
 (f:A→ₚ[ℂ]ℂ) (a:A): inner ℂ (origin f) (f.gnsStarAlgHom a (origin f))=f a:=by
 have h:=gns_pair f 1 a; rw [star_one,one_mul,map_one] at h
 exact h

section aid
variable {A B:Type}[CStarAlgebra A][CStarAlgebra B]
 (f:A →⋆ₐ[ℂ] B)
private lemma pearl_smul (z:ℂ) (a:A){c:A}(h:z•a=c):z•f a=f c:=by rw [←map_smul,h]
private lemma pearl_add (a z:A){c:A}(h:a+z=c):f a+f z=f c:=by rw [←map_add,h]
private lemma pearl_mul (a z:A){c:A}(h:a*z=c):f a*f z=f c:=by rw [←map_mul,h]
end aid
namespace Fired
variable {P j x} {s n w u:ℕ} {F G:P.Test}{T U:(P.ColorHil j x).Op}(h:P.Fired j x s w F T)
include h
lemma pos:0<w:= h.choose

lemma unique (g:P.Fired j x s w F U): T=U:=by
 obtain ⟨p,f,h,h₀,rfl⟩:=h
 obtain ⟨_,e,q,h₁,rfl⟩:=g
 have :f=e:= Subtype.ext (Subtype.ext (congrArg (fun t:P.Test=> t.val) (h₀.trans h₁.symm)))
 subst e; rfl
lemma mean_le {a:ℝ}(m:∀ (e:P.Card j s w)(h:0<w), P.voxTest j s e.val=F → ‖b s h e‖≤a): ‖T‖≤a:=by
 obtain ⟨q,f,p,e,rfl⟩:=h
 exact (NonUnitalStarAlgHom.norm_apply_le (Φ) (P.door j s w q f p)).trans (m _ q e)
lemma scalar: inner ℂ (P.colorZero j x) (T (P.colorZero j x))= P.singleState j s x F:=by
 obtain ⟨q,f,p,rfl,rfl⟩:=h
 let z:=P.restrictPortion j x

 let B:=P.door j s w q f p
 exact (pearl z B).trans (P.room_single j x _ _ _ _)
lemma refine (e:s≤n): P.Fired j x n (P.par.R.L.val^(n-s)*w)
   (P.conveying s (n-s) F) T:=by
 obtain ⟨q,f,p,rfl,rfl⟩:=h
 refine ⟨Nat.mul_pos (pow_pos P.par.R.L.property _) q,_,
    show P.voxTest j n (furnished Y₀ H s R₀ j false w f n e).val∈enclave κ from P.refine_keeps s _ p _,
    rfl,congrArg (Φ ·) (Subtype.ext (P.upper_tab j s w q f n e))⟩

lemma smul (z:ℂ): P.Fired j x s w (z • F) (z • T):=by
 obtain ⟨q,f,p,rfl,rfl⟩:=h
 refine ⟨q,jamScale Y₀ H s j false w f z,
    Subalgebra.smul_mem (enclave κ) p z,rfl,?_⟩
 refine pearl_smul Φ z _ (Subtype.ext (Subtype.ext ?_))
 exact (jam_scale Y₀ H P.law s R₀ σ j false C₀ w f q z).symm
lemma add (g:P.Fired j x s w G U): P.Fired j x s w (F+G) (T+U):=by
 obtain ⟨q,f,p,rfl,rfl⟩:=h
 obtain ⟨_,e,t,rfl,rfl⟩:=g
 refine ⟨q,jamAdd Y₀ H s j false w f e,
    Subalgebra.add_mem (enclave κ) p t,rfl,?_⟩
 refine pearl_add Φ _ _ (Subtype.ext (Subtype.ext ?_))
 exact (jam_add Y₀ H P.law s R₀ σ j false C₀ w f q e).symm
lemma sub (g:P.Fired j x s w G U): P.Fired j x s w (F-G) (T-U):=by
 rw [sub_eq_add_neg,sub_eq_add_neg, ← neg_one_smul ℂ G, ← neg_one_smul ℂ U]
 exact h.add (g.smul (-1))

omit h
lemma identity (p:0<w): P.Fired j x s w 1 (E (whenly Μ s w)):=by
 let z:=SlabMark.identity P.run P.large s j false w
 have hv:P.voxTest j s (z.val)=1:=rfl
 have e:P.voxTest j s (z.val) ∈ enclave κ:=by rw [hv]; exact one_mem _
 refine ⟨p,z,e,hv,?_⟩
 exact congrArg (Φ ·) (Subtype.ext (Subtype.ext
    (ticket_birth Y₀ H P.law s R₀ σ j false C₀ w p).symm))
lemma zero (p:0<w): P.Fired j x s w 0 0:=by
 simpa only [zero_smul] using (identity («x»:=x) («s»:=s) p).smul 0

lemma sum {I:Type*}(p:0<w)(Z:Finset I)
   (A:I→P.Test)(B:I→(P.ColorHil j x).Op)
   (h:∀ i∈Z,P.Fired j x s w (A i) (B i)):
 P.Fired j x s w (∑ i∈ Z,A i) (∑ i∈Z,B i):=by
 classical
 induction Z using Finset.induction with
 | empty=>simpa only [sum_empty] using zero (x:=x) (s:=s) p
 | @insert i Z l ih=>
   rw [sum_insert l,sum_insert l]
   exact (h i (mem_insert_self _ _)).add (ih (fun a e=> h a (mem_insert_of_mem e)))
include h
lemma mul (g:P.Fired j x s u G U): P.Fired j x s (w+u) (F*P.shifts j w G) (T*U):=by
 obtain ⟨q,f,p,rfl,rfl⟩:=h
 obtain ⟨r,e,t,rfl,rfl⟩:=g
 let C:= edit P.run P.large s j false w u f e
 have h:P.voxTest j s C.val= P.voxTest j s f.val*P.shifts j w (P.voxTest j s e.val):= Subtype.ext (editor ..)
 refine ⟨add_pos q r,C,?_,h,pearl_mul Φ _ _ (Subtype.ext (P.concat ..))⟩
 rw [h]
 exact Subalgebra.mul_mem _ p (P.shifts_keep j _ t)

omit h in
private lemma hot_start : E 0=1:= (P.physicalEnergy j x).eZero
lemma left (n:ℕ): P.Fired j x s (n+w) (P.shifts j n F) (E (whenly Μ s n)*T):=by
 rcases Nat.eq_zero_or_pos n with rfl|v'
 · rw [when_zero,Nat.cast_zero,P.shifts_zero,zero_add,hot_start,one_mul]
   exact h
 simpa only [one_mul] using (identity v').mul h
lemma right(n:ℕ):P.Fired j x s (w+n) F (T* E (whenly Μ s n)):=by
 rcases Nat.eq_zero_or_pos n with rfl|v'
 · rw [when_zero,add_zero,hot_start,mul_one]
   exact h
 have u := h.mul (identity v')
 rwa [map_one,mul_one] at u
end Fired

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
