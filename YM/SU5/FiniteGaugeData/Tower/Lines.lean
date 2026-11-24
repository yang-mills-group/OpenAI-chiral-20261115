import YM.SU5.FiniteGaugeData.Tower.Narrowgate
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
/-!
# Unlimited finite tower application

Across all levels of the hierarchy, including separated products and gauge
arguments. No arithmetic claim on the **overlap** products under the maps,
evaluate those as one family mark through the tower. Witness fixed physical
length at level 0 transported exactly. Centering is relative to the actual E
here. Changes of ruler (e.g. a finer realization at, instead of a transport
to, level s) still require their own comparison as s→∞.
-/
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}(Q: Resolution (E:=E) Y H D)

section ladder
-- Explicit finite number of steps, actual resolution u+k at the output.
def stream (D:ℕ→Family (tent Y H)→Family (tent Y H))(u k:ℕ)(F:Family (tent Y H)) := Nat.rec (motive:=fun _=>Family (tent Y H)) F (fun i x=> D (u+i) x) k
variable (u n:ℕ)
local notation "P" n:max F:max=>stream (Y:=Y) (H:=H) (D) u n F
-- Y H explicit? check @stream
lemma stream_step{F:Family (tent Y H)}: (stream Y H D u (n+1) F) = D (u+n) (stream Y H D u n F):=rfl
local notation "R" U:max n:max=>stream Y H D U n
lemma upstairs {F:Family (tent Y H)}: stream Y H D u (n+1) F=stream Y H D (u+1) n (D u F):=by
 induction n with
 | zero=>simp [stream]
 | succ k h=> rw [stream_step,h,stream_step]; congr 1; omega
-- more general assembly lemma
lemma joined (m:ℕ)(F:Family (tent Y H)):
 stream Y H D u (n+m) F=stream Y H D (u+n) m (stream Y H D u n F):= by
 induction m with
 | zero=> simp [stream]
 | succ k i=> rw [←Nat.add_assoc,stream_step,i,stream_step,Nat.add_assoc]

variable {F G:Family (tent Y H)}{S T:Finset Cover}
local notation "W" S:max=> volumeAround Λ l n S
local notation "Z₀" k:max=>volumeAround Λ l k
include Q
lemma proceeds(x:InTest K true S false F): InTest K true (W S) false ((R u n) F)∧ E (u+n) ((R u n) F)=E u F:=by
 induction n with
 | zero=> simpa only [volumeAround,stream,Nat.rec_zero,Nat.add_zero] using And.intro x (rfl: E u F=E u F) -- name
 | succ n h=> rw [stream_step,←Nat.add_assoc]; exact ⟨(Q.supports (u+n) h.1).1,(Q.supports (u+n) h.1).2.trans h.2⟩
lemma streams_test(x:TestFamily K true F):TestFamily K true (stream Y H D u n F):=aux_test (proceeds Y H Q u n x.paid.choose_spec).1
lemma chroma(x:F∈ observ K S true):stream Y H D u n F∈ observ K (W S) true:=by
 induction n with
 | zero => exact x
 | succ n h=> rw [stream_step]; exact ⟨(Q.supports (u+n) ((obs_in ..).1 h).1).1,Q.occupation (u+n) h⟩
lemma woven_add(p:TestFamily K true F)(h:TestFamily K true G):stream Y H D u n (F+G)=stream Y H D u n F+stream Y H D u n G:=by
 induction n with
 | zero=>rfl
 | succ n ih=> rw [stream_step,ih, Q.plus_lift _ (streams_test Y H Q u n p) (streams_test Y H Q u n h),stream_step,stream_step]
lemma woven_smul (p:TestFamily K true F)(z:ℂ):stream Y H D u n (z • F)=z • stream Y H D u n F:=by
 induction n with
 | zero=>rfl
 | succ n ih=>rw [stream_step,ih,Q.amp _ (streams_test Y H Q u n p), stream_step]
lemma woven_one: stream Y H D u n 1=1:=by
 induction n with
 | zero=>rfl
 | succ n ih=>rw [stream_step,ih,Q.unit]
lemma woven_product (p:InTest K true S false F)(h:InTest K true T false G)(t:Detached Λ l S T): stream Y H D u n (F*G)=stream Y H D u n F *stream Y H D u n G:=by
 induction n with
 | zero=>rfl
 | succ n ih=> rw [stream_step,ih,Q.separates (u+n) (proceeds Y H Q u n p).1 (proceeds Y H Q u n h).1 ((Around_detaches Λ l t n).act Λ l),stream_step,stream_step]
-- reflection plane in gauge grid multiplies with the number of step pitches
variable (j:Axis)(z:ℤ)
local notation "L"=> Λ.R.L.val
lemma stream_flipped (x:TestFamily K true F): stream Y H D u n (mirror K j z F)= mirror K j ((L:ℤ)^n*z) (stream Y H D u n F):=by
 induction n with
 | zero=> simp only [stream,pow_zero,one_mul,Nat.rec_zero]
 | succ n ih=> rw [stream_step,ih,Q.turn (u+n) j _ (streams_test Y H Q u n x), stream_step,pow_succ',mul_assoc]
lemma wings (x:F∈wing K j z): stream Y H D u n F∈ wing K j ((L:ℤ)^n*z):=by
 induction n with
 | zero=> simpa only [stream,pow_zero,one_mul,Nat.rec_zero] using x
 | succ n ih=>
    let v:= (L:ℤ)^n*z; change (R u n) F∈ wing K j v at ih; rw [stream_step]
    obtain ⟨S,t,h⟩:= (ih:∃ S:Finset Cover,InTest K true S false ((R u n) F) ∧ region j v (K).ℓ S)
    rw [pow_succ',mul_assoc]; exact ⟨_,(Q.supports _ t).1, wingspan_region Y H S j v h⟩ -- #check order

local notation "Z"=> wing K j z
local notation "m"=>mirror K j
private lemma d_sqr (x:F∈Z)(y:G∈Z): stream Y H D u n ((m z F)*G)= m ((L:ℤ)^n*z) ((R u n) F) * ((R u n) G):=by
 obtain ⟨S,q,r⟩:= (x:∃ S:Finset Cover, InTest K true S false F∧ region j z (K).ℓ S)
 obtain ⟨T,v,a⟩:= (y:∃ S:Finset Cover, InTest K true S false G∧ region j z (K).ℓ S)
 rw [woven_product Y H Q u n (axial K j z q) v (mirror_detached Λ l (a:=j) (z:=z) r a),stream_flipped Y H Q u n j z (aux_test q)]
-- the positivity hierarchy isomorphism. For all even marks, unit and Herm, not just
-- occupancy words. Products within `F`,`G` in this assertion remain on the
-- precise stencil placements in them, even with contact.
lemma teach {F G:Family (tent Y H)}(x:F∈Z)(y:G∈Z) : E (u+n) (m ((L:ℤ)^n*z) ((R u n) F) *((R u n) G))= E u (m z F * G):=by
 have ht:= d_sqr Y H Q u n j z x y
 let p:= ((exam j z K x).2.mul (exam j z K y).1)
 rw [←ht]; exact (proceeds Y H Q u n p.paid.choose_spec).2

omit Q
variable {Z':Type*} -- level supports of incoming data fixed
end ladder
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.teach
