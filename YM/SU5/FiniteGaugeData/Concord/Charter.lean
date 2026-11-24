import YM.SU5.FiniteGaugeData.Concord.Journal
/-!
# Positive reflected hierarchy

Single algebra through all finite regions at all resolutions. Matrix of OS comparisons on FREE
choices of local elements at ANY observing levels including combinations/products, reflection
plane coordinated with scale and aligned. This really uses the compatibility & the pricing of
actual kernels, not extending products across levels as if a homomorphism. Restrict to physical
singlet systems `physical` as needed. Derive positivity here on bigger algebra.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Concord
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
  Topology ComplexOrder Classical TensorProduct
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent
  Next.Free Bloch Drapes Spire Lifted Skye Precision Tree Push.SectorMeasure Next.SectorChange Fock Heat
open Afterglow Afterglow.Common Afterglow.Sound Afterglow.Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale Style
variable {Λ:Preparation}{l:ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)
variable {i k:ℕ→ℕ}{s:ℕ}
variable {F:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{P:Playhouse Λ l}
local notation "K"=> tent Y H
local notation "U"=> swept Λ l
variable (W:Traced Y H i k F E P) (a:Axis)(z:ℤ)
local notation "R'"=> fun k:ℕ=> courseAdvance Y H k W
local notation "ℓ"=>reserve Λ l

-- phase at common physical coordinate aligned to s=0 (can extend by starting higher for higher tests)
def steady (Λ:Preparation)(z:ℤ)(s:ℕ):= planeAt (gaugeShift Λ.block z) Λ.R.L s
local notation "Z"=> steady Λ z
lemma steady_step (s:ℕ): steady Λ z (s+1)=Λ.R.L.val*steady Λ z s:=(step_plane ..).symm
lemma steady_aligned (s:ℕ) : steady Λ z s=gaugeShift Λ.block ((Λ.R.L.val:ℤ)^s*z):=by unfold gaugeShift steady planeAt; unfold gaugeShift; ring

local notation "Lf"=> junior (tent Y H)
local notation "turnS"=> fun (s:ℕ)=> turn (tent Y H) a (steady Λ z s)
def acrossAll (K':Calibration)(a:Axis)(z:ℕ→ℤ) := Style.inversion (fun s=>turn K' a (z s)) -- rename

local notation "arrival"=> acrossAll (tent Y H) a Z

def BookRule (K':Calibration)(a:Axis)(z:ℕ→ℤ)(r:ℕ):ℕ→ Subalgebra ℂ (junior K') := fun n=> wing K' a (z n) r
local notation "Lounge"=> BookRule (tent Y H) a Z ℓ

lemma arrives (x: Hallspace K)(p:x∈ building K): (acrossAll (tent Y H) a Z x)∈ building K := by
  refine inv_room _ ?_ (show x∈pressed _ from p)
  rintro f ⟨v,n,e⟩; refine ⟨Submonoid.mem_top _, n, fun i p=>?_⟩
  unfold Style.rotating; rw [e i p]; exact turn_one ..
lemma aloft (x: Hallspace K)(p:x∈ physical K): (acrossAll (tent Y H) a Z x)∈ physical K := by
  refine inv_room _ ?_ (show x∈pressed _ from p); rintro f ⟨v,n,e⟩; refine ⟨fun i=>?_, n, fun i p=>?_⟩
  · exact turn_gauge («K»:=K) a (Z i) (v i)
  unfold Style.rotating; rw [e i p]; exact turn_one ..
lemma timely (x: Hallspace K)(p:x∈ Style.atLeast s): acrossAll (tent Y H) a Z x ∈ Style.atLeast s:= by
  refine inv_room _ ?_ (show x∈pressed _ from p); rintro f ⟨v,w⟩; refine ⟨Submonoid.mem_top _, fun i p=>?_⟩; unfold Style.rotating; rw [w i p]; exact turn_one ..

-- call generic estimator box record. Through T by confluence.
include W
local notation "Θ" i:max=> turn (tent Y H) a (steady Λ z i)
local notation "Applause" i:max=> prefixTube (fun _=> ↥(junior K)) (fun _=> LinearMap.id) (fun i=> courseAdvance Y H i W) i
private lemma halo_song (f:ℕ→junior K)(t:∀ i,f i∈wing K a (Z i) ℓ) (n:ℕ) : (prefixTube (fun _=> ↥(junior (tent Y H))) (fun _=> LinearMap.id) (fun i=>courseAdvance Y H i W) n).soc f∈ (BookRule (tent Y H) a Z (reserve Λ l)) n:=by
  induction n with
  | zero=>exact t 0
  | succ n ih=>
    rw [vystep]; refine Subalgebra.mul_mem _ ?_ (show f (n+1) ∈ Lounge (n+1) from t _)
    change _∈wing (tent Y H) a (Z _) ℓ; rw [steady_step]; exact starboard_turn Y H n W a _ ih
lemma applause_adv {f:Hallspace K}(p:f∈ limited (BookRule (tent Y H) a Z (reserve Λ l)) s): issue Y H W s f∈ wing K a (steady Λ z s) (reserve Λ l):=by
  refine display (P:=fun x=> issue Y H W s x ∈wing _ a (Z s) ℓ) (fun f p=>?_) ?_ ?_ ?_ (show f∈pressed _ from p)
  · rw [solo_issue Y H W f p.2]; exact halo_song Y H W a z f p.1 s
  · rw [map_zero]; exact (Lounge s).zero_mem
  · intro x y _ _ p q; rw [map_add]; exact (Lounge s).add_mem p q
  intro c x _ p; rw [map_smul]; exact (Lounge s).smul_mem p c

private lemma consumes (f g:ℕ→junior K)(t:∀ i,f i∈wing K a (Z i) ℓ)(u:∀ i,g i∈wing K a (Z i) ℓ)(n:ℕ): (prefixTube (fun _=> ↥(junior K)) (fun _=> LinearMap.id) R' n).soc (Style.rotating (fun s=> turn K a (steady Λ z s)) f * g)= (Θ n) ((Applause n).soc f) * ((Applause n).soc g):=by
  induction n with
  | zero=>rfl
  | succ n ih=>
    let v(i):=Θ i
    rw [vystep,vystep,vystep,ih]; simp only [Pi.mul_apply, LinearMap.id_coe, id_eq]
    rw [steady_step, wing_fence Y H n W a _ (halo_song Y H W a z f t n) (halo_song Y H W a z g u n), turn_mul]; unfold Style.rotating; simp_rw [steady_step]; ac_rfl

lemma composite {x y:Hallspace (tent Y H)}(p:x∈limited (BookRule (tent Y H) a Z (reserve Λ l)) s)(q:y∈limited (BookRule (tent Y H) a Z (reserve Λ l)) s):
    issue Y H W s (acrossAll (tent Y H) a (steady Λ z) x * y)=(turn (tent Y H) a (steady Λ z s)) (issue Y H W s x)*issue Y H W s y:=by
  let A(x y: Hallspace K):= issue Y H W s ((arrival) x * y) = (Θ s) (issue Y H W s x)*issue Y H W s y
  refine display (P:=fun x=> issue Y H W s ((arrival) x * y) = (Θ s) (issue Y H W s x)*issue Y H W s y) ?_ ?_ ?_ ?_ (show x∈ pressed _ from p)
  · intro f h
    refine display (P:=fun y=> A (PiTensorProduct.tprod ℂ f) y) (fun g u=>?_) ?_ ?_ ?_ (show y∈ pressed _ from q)
    · unfold A acrossAll; rw [Style.inv_at,PiTensorProduct.tprod_mul_tprod,solo_issue Y H W _ h.2,solo_issue Y H W _ u.2,solo_issue Y H W _ (fits_times (f:=Style.rotating turnS f) ?_ u.2)]
      · exact consumes Y H W a z f g h.1 u.1 s
      intro i t; unfold Style.rotating; dsimp only; rw [(show Style.fits s f from h.2) i t,turn_one] -- tune tc
    · unfold A; rw [mul_zero,map_zero,mul_zero]
    · intro x y _ _ p q; unfold A at p q ⊢; rw [mul_add,map_add,p,q,map_add,mul_add]
    intro c y _ p; unfold A at p ⊢; rw [Algebra.mul_smul_comm,map_smul,p,map_smul,Algebra.mul_smul_comm]
  · rw [map_zero,zero_mul,map_zero,map_zero,zero_mul]
  · intro f g _ _ p q; rw [map_add,add_mul,map_add,p,q,map_add,map_add,add_mul]
  intro c f _ p; rw [map_smulₛₗ (f:=arrival),Algebra.smul_mul_assoc,map_smul,p,map_smul,map_smulₛₗ (f:=Θ s),Algebra.smul_mul_assoc]

omit W

def midway : building (tent Y H)→ₗ⋆[ℂ]building (tent Y H):=  {
  toFun f:= ⟨(arrival) f.val, arrives Y H a z f.val f.property⟩
  map_add' := fun x y=> Subtype.ext (map_add arrival x.val y.val)
  map_smul' := fun c f=> Subtype.ext (map_smulₛₗ arrival c f.val) }

def haloRule := throughout (BookRule (tent Y H) a Z (reserve Λ l))
-- separate types for reader convenience, include gauge invariance outside later
local notation "Lore"=> (haloRule Y H a z)

def input : haloRule Y H a z→ₗ[ℂ] building (tent Y H) := (Subalgebra.inclusion (seen (BookRule (tent Y H) a Z (reserve Λ l)))).toLinearMap

def outGrid (x:haloRule Y H a z) : building (tent Y H) := midway Y H a z (input Y H a z x)

include W
lemma whole_positive (f : haloRule Y H a z) : 0 ≤ portfolio Y H W (outGrid Y H a z f * input Y H a z f) := by
  obtain ⟨s,he⟩:= Style.by_stages _ _ (show f.val∈ pressed _ from f.property)
  let x:= f.val; let F:= issue Y H W s x; let ζ:=steady Λ z s; let V:=outGrid Y H a z f; let R:=input Y H a z f
  have hx:x∈ Style.atLeast s:= limited_top _ (R:=BookRule (tent Y H) a Z (reserve Λ l)) he
  have hL:F∈ wing K a ζ ℓ:= applause_adv Y H W a z he
  have hv: V.val= arrival x:=rfl; have hr:R.val=x:=rfl
  change 0 ≤ portfolio Y H W (V*R); rw [portfolio_hall Y H W ((Style.atLeast s).mul_mem (show V.val ∈ Style.atLeast s from hv.symm ▸ timely Y H a z x hx) hx)] -- implicit x mismatch
  rw [Subalgebra.coe_mul,hv,hr,composite Y H W a z he he, ←intake_eq Y H s W.own]
  change 0≤ intake Y H s W.own (turn K a (steady Λ z s) F*F); unfold ζ at hL; rw [steady_aligned] at *
  exact diagonals Y H s a _ W.own F hL -- order checks
end YM.CF.Buffered.Concord
#print axioms YM.CF.Buffered.Concord.whole_positive
