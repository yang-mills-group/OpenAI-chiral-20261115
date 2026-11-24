import YM.SU5.Relativistic.FarFuture
import YM.SU5.Relativistic.LateMultiplication
/-! # Boundary transforms and Eχ as its centered read

This buys operators for each local Cloud x (ANY orientation/levels/supports/even
indicated inputs), read at the center in a sector. Not Minkowski ops. Those
are slab ops and multi-mesh positions; read on actual inner product *before*
sector integration, importantly multiplying by cutoff-priced marks so same
as using Θ on that resolution.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 6000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function NormedSpace Filter Metric Lattice Cube Finset MeasureTheory RG Wilson
open Lat Mir Phase RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Scree Window Vale Girt Lifted
open Py Py.Rate LocalLimit Preparation Satin Heat Fock SlabMark PhaseChoice Push.SectorMeasure
open Tapestry Tapestry.Altitude Tapestry.Exhibition MeshClock
open Tower.Selected Vacancy
open Journey
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
section precursor
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
    {L:Rack Λ l}{Θ:Clay Λ l} (D : Exhibition Y H i k I E L Θ)
local notation "V"=> D.univ_
variable (G:SatinVerification.GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (j:Axis)
local notation "K₀"=> Λ.R.L.val
local notation "Φₛ" s:max=> Tower.Field Y H s j 0 false
local notation "κ" C:max s:max=> actor Y H s G.history.circuit j 0 false C
local notation "ω" C:max=> floorV Y H G.history.circuit j 0 false C
local notation "Ω" C:max=> groundRoom Y H V G.history j false C
local notation "H₀" C:max=> Ark.Ht Y H G.history.circuit j 0 false C
local notation "B" C:max n:max w:max z:max h:max=> boxOp Y H V n G.history G.clipped j false C w z h
local notation "Λ₀"=> timeMesh Λ
local notation "Eₛ" s:max=> vistaFinish Y H s D
local notation "Γ"=> Dome (tent Y H)
local notation "𝒞"=> Cloud (Dome (tent Y H))
local notation "U" x:max => relocate K j x
local notation "θ" x:max=> mirror K j x
variable {n b:ℕ}
lemma finish_upwards {u: Cloud (Dome (tent Y H))}(n:ℕ) (h:u∈ shorter Γ n)(r:ℕ):
    ((Eₛ (n+r)) u).val=stream Y H G.refine n r (((Eₛ n) u).val):=by
  induction r with
  | zero=> rfl
  | succ r ih=>
    change ((Eₛ (n+r+1)) u).val=_
    have hv : u ∈ shorter Γ (n+r) := Altitude.climbs Γ (Nat.le_add_right ..) h
    have ht: (Eₛ (n+r+1)) u= (D.liftD Y H (n+r)) ((Eₛ (n+r)) u) := Decking.joins (vistaDressing Y H D) (n+r) u (auxiliaryPad K) hv
    rw [ht,lifts_here Y H V G,ih]; rfl

/-- ANY resolution polynomials read, not limited to separated levels or footprint or gauge (for
factor probes). Can purchase a symmetric (in axis j) extent. -/
lemma buys_at (v : Cloud (Dome (tent Y H)))(n:ℕ): ∃ w:ℕ,0<w ∧ ∃ f:Entry Y H n j false (w+w), f.val.val=(U (w:ℤ)) (((Eₛ n) v).val):=by
    let x:Γ := (Eₛ n) v; let z:=x.val
    obtain ⟨S,p⟩:= (show TestFamily K true z from x.property).paid
    obtain ⟨m,s,k,u⟩:= plow_up Y H j S
    let w:=m+s; have hw:0<w:= by unfold w; omega
    have he:Between K j 0 ((ruler Λ.block)*((w+w:ℕ):ℤ)) (plow K j (w:ℤ) S):=by
       intro i a; obtain ⟨t,g,rfl⟩:= plow_stays K j (w:ℤ) S a
       let M:=ruler Λ.block
       have hg : t+(M*(m:ℤ))•Lattice.step j∈ plow K j (m:ℤ) S := by
         unfold plow; unfold address; apply mem_image.mpr; exact ⟨t,g,by rw [ruler_offset]; rfl⟩
       obtain ⟨b,c⟩:=u _ hg
       rw [moves,if_pos rfl] at b c ⊢
       change 0+(K).ℓ≤ t j+ M*w ∧ t j+ M*w+(K).ℓ≤ M*((w+w:ℕ):ℤ)
       have hM:0<M:=ruler_gene ..
       change t j+M*(m:ℤ)+(K).ℓ ≤ M*s at c
       have hMs : 0≤ M*(s:ℤ) := by positivity
       have hMm : 0≤ M*(m:ℤ) := by positivity
       simp only [w,Nat.cast_add,mul_add]; constructor <;> linarith
    exact ⟨w,hw,enclose Y H n j false (PhaseChoice.observe (show TestFamily K true z from x.property)) p w (w+w) he,rfl⟩
-- any observable R for purpose + calibration
local notation "T" n:max v:max => (PhaseChoice.observe (show TestFamily K true (((vistaFinish Y H n D v)).val) from (vistaFinish Y H n D v).property))
lemma symmetric_box (v:Cloud (Dome (tent Y H)))(n w:ℕ)(z:0<w)(f:Entry Y H n j false (w+w))
    (p:f.val.val=relocate K j (w:ℤ) ((Eₛ n) v).val)(C:Arena Y H G.history.circuit j 0 false)(u: groundRoom Y H V G.history j false C):
    inner ℂ u (cap Y H V n G.history G.clipped j false C (T n v) u) = inner ℂ u.val ((B C n (w+w) f (by omega)) u.val):=by
    let x:= T n v; let t : Veranda Y H n j false x:= ⟨w,w+w,by omega,f,p⟩
    rw [onAny Y H V n G.history G.clipped j false C t]; change inner ℂ (u:Ω C) ((Aurora Y H V G.history j false C).orthogonalProjectionOnto _) = _
    rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]; rfl

variable (x : Future Y H j b)
namespace Future
def kernelRoot : Dome (tent Y H) :=⟨(Future.emit Y H j x).val,aux_test (x.emit_extent ..)⟩
def kernelPast : Dome (tent Y H) := aureole (tent Y H) j 0 (kernelRoot Y H j x)
def kernelPath : Dome (tent Y H) := kernelPast Y H j x * kernelRoot Y H j x
def boundary : Cloud (Dome (tent Y H)):= pinhole (Dome (tent Y H)) x.t (kernelPath Y H j x)
lemma twoEnds : x.boundary Y H j = pinhole Γ x.t (kernelPast Y H j x)* pinhole Γ x.t (kernelRoot Y H j x):= map_mul ..
local notation "S₁"=> opening Y H j x
local notation "S₂"=> closing Y H j x
local notation "P" S:max=> footprint Λ l x.t S
lemma picture : pinhole Γ x.t (kernelPast Y H j x)∈ circum Λ l K true (P S₂) {x.t} ∧
    pinhole Γ x.t (kernelRoot Y H j x)∈ circum Λ l K true (P S₁) {x.t}:=by
    have t:=emit_extent Y H j x; have v:=emit_singlet Y H j x
    have he : (kernelRoot Y H j x)∈keep Λ l x.t K true (handstamp (P S₁)) := ⟨S₁, show _ from t, has_footprint Λ l x.t _⟩
    have hp : (kernelPast Y H j x)∈keep Λ l x.t K true (handstamp (P S₂)):= ⟨S₂, show _ from axial K j 0 t, has_footprint Λ l x.t _⟩
    exact ⟨oneSlotWell Λ K l true _ _ x.t (Set.mem_singleton _) hp ((enclave_spec K).mpr (covariant_flips K j 0 t v)),oneSlotWell Λ K l true _ _ x.t (Set.mem_singleton _) he ((enclave_spec K).mpr v)⟩

lemma sandwich (C:Arena Y H G.history.circuit j 0 false)
    {F:Family (tent Y H)}{w:ℕ}{α:ℕ}(hw: 0<α)(f:Entry Y H x.t j false α) (hF:TestFamily K true F)
    (p:f.val.val=(U (w:ℤ)) F)(q: w ≤ wait Y H j x)(r: α=w+w) :
    E x.t ((θ (0:ℤ)) (emit Y H j x).val * (F*(emit Y H j x).val))=
      let z : Ark.Ht Y H G.history.circuit j 0 false C:=actor Y H x.t G.history.circuit j 0 false C (irradiant Y H j x (wait Y H j x-w))
      inner ℂ z ((boxOp Y H V x.t G.history G.clipped j false C α f hw) z):=by
  simp only []; let g:= wait Y H j x; let c:= g-w; have hx:g=c+w:=by have h: w ≤ g:= q; omega
  let y:Γ:= kernelRoot Y H j x; let z:= x.irradiant Y H j c
  have h: y.val=(U (w:ℤ)) z.val:=by
     have h0:=field_test Y H x.t j 0 false x.mark
     change (irradiant Y H j x g).val=_; unfold z irradiant
     rw [timed_apply,timed_apply,relocate_sums K j _ _ h0, hx]; congr 2 <;> omega
  let A:= (θ (0:ℤ)) y.val * (F*y.val)
  have hy: TestFamily K true y.val:=y.property
  have Hx:TestFamily K true A:=(reflect_ok K j 0 hy).mul (hF.mul hy)
  have he:E x.t ((U (w:ℤ)) A)= E x.t A:=SWay Y H V x.t j (2*(w:ℤ)) Hx
  have ht:=field_test Y H x.t j 0 false z
  rw [snatch_equal,stems Y H V,area0,slab_eq]; change E x.t A= E x.t ((θ (0:ℤ)) z.val * (f.val.val*((U (α:ℤ)) z.val)))
  rw [← he]; apply congrArg _; unfold A
  rw [relocate_mul,relocate_mul,h,mirror_relocate K j _ _ ht,relocate_sums K j _ _ (reflect_ok K j _ ht),add_neg_cancel,relocate_zero K j (reflect_ok K j _ ht),relocate_sums K j _ _ ht,←p, show (w:ℤ)+(w:ℤ)=(α:ℤ) by omega]

lemma actualE (C:Arena Y H G.history.circuit j 0 false){v:Cloud (Dome (tent Y H))} {n w:ℕ} (z:0<w) (u:v∈ shorter Γ n)(f:Entry Y H n j false (w+w))
    (p:f.val.val=relocate K j (w:ℤ) ((Eₛ n) v).val)(e:n≤b)(g:w≤b) :
    vistaTake Y H D (v*x.boundary Y H j)=
    let m:= wait Y H j x-K₀^(x.t-n)*w
    let r : Ark.Ht Y H G.history.circuit j 0 false C:=actor Y H x.t G.history.circuit j 0 false C (irradiant Y H j x m)
    inner ℂ r ((B C n (w+w) f (by omega)) r):=by
    simp only []; let Q:= Eₛ x.t; let a:= x.kernelPath Y H j
    have hp:n≤x.t:=e.trans x.arrival
    have he: v∈ shorter Γ x.t:=Altitude.climbs Γ hp u
    let c : Veranda Y H n j false (T n v):=⟨w,w+w,by omega,f,p⟩
    let d:= x.t-n
    let α:= K₀^d
    let b':=α*w; let A:= K₀^d*(w+w)
    let h₀:= addLevel Y H V n G.history j false c x.t hp
    have hx: ((Eₛ x.t) v).val=stream Y H G.refine n d (((Eₛ n) v).val):= by
       have Hx:n+d=x.t:=by unfold d; omega
       exact (show _ from Eq.trans (congrArg (fun t=> ((Eₛ t) v).val) Hx.symm) (finish_upwards Y H D G n u d))
    have hk:b' ≤ x.wait Y H j:= Nat.mul_le_mul (Nat.pow_le_pow_right Λ.R.L.property (show d≤ x.t from Nat.sub_le ..)) g
    have hk': h₀.rise=b' := by change (K₀:ℤ)^d*(w:ℤ)=((K₀^d*w:ℕ):ℤ); push_cast; rfl
    have h': h₀.fwd.val.val=(U (b':ℤ)) ((Q v).val):= h₀.yes.trans (by rw [hk']; unfold Q; rw [hx]; rfl)
    have hs:=sandwich Y H D G j x C h₀.pos h₀.fwd ((Q v).property) h' hk (show h₀.span=b'+b' from mul_add ..)
    have ht: Q (v*x.boundary Y H j)=(Q v)*a:= Decking.last (vistaDressing Y H D) (auxiliaryPad K) v x.t he _
    rw [vistaCall Y H x.t (v*x.boundary Y H j) D ((shorter Γ x.t).mul_mem he (short_pinhole x.t a)),refined_box Y H V n G.history G.clipped j false C (w+w) f (by omega) x.t hp]
    change E x.t (Q _).val=_
    rw [ht]
    let k:= (emit Y H j x).val; let V':=(Q v).val; let S':= (θ (0:ℤ)) k
    have hb: V'*(S'*k)=S'*(V'*k):=by rw [←mul_assoc,even_tests K ((Q v).property) (reflect_ok K j 0 (show TestFamily K true k from (x.kernelRoot Y H j).property)),mul_assoc]
    change E x.t (V'*(S'*k))=_; rw [hb]; exact hs
end Future
end precursor
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Future.picture
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Future.actualE
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.symmetric_box
