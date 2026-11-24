import YM.SU5.FiniteGaugeData.Tower.Float
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
/-! Hilbert solder: plant consistency and common densely spanning increasing system. -/
open Fock Heat
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}(Q:Resolution (E:=E) Y H D)
variable (j:Axis)(z:ℤ)(strict:Bool)
local notation "m" u:max=> meshface (Λ:=Λ) z u
variable (C:Arena Y H Q j z strict)
local notation "F" s:max=> Tower.Field Y H s j z strict
local notation "κ" s:max=>actor Y H s Q j z strict C
local notation "A"=> Ark.Ht Y H Q j z strict C
include Q
lemma raiseGate(s t:ℕ)(p:s≤ t)(x:F s):stream Y H D s (t-s) x.val∈purpose (tent Y H) (meshface (Λ:=Λ) z t) j strict:=by
 have hx:= (purpose_ok ..).mp x.property
 have Hx: stream Y H D s (t-s) x.val ∈ wing K j (meshface (Λ:=Λ) z t):= newer Y H Q j z p (freeze Y H s j z strict x) -- Q inclusion?
 refine (purpose_ok ..).mpr ⟨Hx,fun a=>?_⟩
 obtain ⟨S,h⟩:= (exam j _ K hx.1).1.paid; have hu:↑x ∈ observ K S true:= (obs_in ..).2 ⟨h,hx.2 a⟩
 exact ((obs_in ..).1 (chroma Y H Q s (t-s) hu)).2
noncomputable def Raise (s t:ℕ)(p:s≤ t)(x:F s): (F t):=⟨stream Y H D s (t-s) x.val,raiseGate Y H Q j z strict s t p x⟩
include V C
lemma join_actor(s t:ℕ)(p:s≤ t)(x:F s): (κ t) (Raise Y H Q j z strict s t p x)=(κ s) x:=by
 apply all_voices Y H Q j z strict C; intro k i
 let u:=max k t; have h:k≤u:=le_max_left ..; have h₁:t≤u:=le_max_right ..
 rw [contracts Y H V Q j z strict C k t u h h₁,contracts Y H V Q j z strict C k s u h (p.trans h₁)]; suffices h': stream Y H D t (u-t) (Raise Y H Q j z strict s t p x).val=stream Y H D s (u-s) x.val by rw [h']
 exact congrArg Subtype.val (linking_diagram Y H Q j z p h₁ (freeze Y H s j z strict x))

-- One vacuum in this resolution construction. Concern vacuum selection
-- later -- this is still the one given by E itself, not assuming translation
-- uniqueness or factor.
noncomputable def unity (s:ℕ):F s:=⟨1,(purpose ..).one_mem⟩
noncomputable def floorV:A:= (κ 0) (unity Y H j z strict 0) -- #check
lemma vacua(s:ℕ): floorV Y H Q j z strict C=(κ s) (unity Y H j z strict s):=by
 have h: unity Y H j z strict s= Raise Y H Q j z strict 0 s (Nat.zero_le _) (unity Y H j z strict 0):=by apply Subtype.ext; exact (woven_one Y H Q 0 (s-0)).symm
 rw [h,join_actor Y H V]; rfl
lemma vane: ‖floorV Y H Q j z strict C‖=1:=by
 let x:=unity Y H j z strict 0; let v:= (κ 0) x
 have ht: inner ℂ v v=E 0 (mirror K j (meshface (Λ:=Λ) z 0) (1:Family K) *1) := contracts Y H V Q j z strict C 0 0 0 (by omega) (by omega) x x
 rw [mirror_unit, mul_one,E_unit Y H V,inner_self_eq_norm_sq_to_K] at ht
 have h₂:‖v‖^2=(1:ℝ):=by apply Complex.ofReal_injective; exact (Complex.ofReal_pow ..).trans ht
 change ‖v‖=_; nlinarith [norm_nonneg v]

open Set
-- linear span over all levels is dense and in fact every linear combination
-- is attained at one level, without separate RKHS approximants.
def itinerary := ⋃ i:ℕ, Set.range (arrows Y H V Q j z strict C i)
lemma echelon : Monotone (fun i:ℕ=> LinearMap.range (arrows Y H V Q j z strict C i)):=by
 rintro i k p _ ⟨x,rfl⟩; exact ⟨Raise Y H Q j z strict i k p x, join_actor Y H V Q j z strict C i k p x⟩
lemma sounds: Dense (itinerary Y H V Q j z strict C):=by
 let M(i):= LinearMap.range (arrows Y H V Q j z strict C i)
 let v:=C
 have h:= echelon Y H V Q j z strict C
 rw [itinerary,show (⋃ i:ℕ, Set.range (arrows Y H V Q j z strict C i))= ↑(⨆ i,M i) from Eq.symm (Submodule.coe_iSup_of_directed M h.directed_le)]
 apply ((show _root_.YM.Kernel.Gram _ from v).dense).mono
 exact Submodule.span_le.mpr fun i r=>by
    obtain ⟨x,rfl⟩:=r
    exact (le_iSup M x.1) (show (κ x.1) x.2 ∈ M x.1 from ⟨x.2,rfl⟩)

-- literal Born inner products from stipulated fixed-level arguments; when
-- needed `Float.sees` on the full cross form, so no replacements even for
-- mixed scales
lemma analyzes {S₁ S₂:Finset Cover}{Z T:A} {u v h:ℕ}(a:u≤ h)(b:v≤ h){x:F u}{y:F v}(z₁:Z=(κ u) x)(z₂:T=(κ v) y)
 (P : InTest (tent Y H) true S₁ false x.val)(R:InTest (tent Y H) true S₂ false y.val){A₀ B₀:ℕ→ℕ}(D':Coherent (i:=i) (k:=k) Y H (E:=E) D A₀ B₀):
   Tendsto (fun r=>sharp Y H h (i (A₀ r)) (k (B₀ r)) (stageGram Y H (i:=i) (k:=k) (a:=A₀) (b:=B₀) j z u v S₁ S₂ r h x.val y.val)) atTop (𝓝 (inner ℂ Z T)):=by
 rw [z₁,z₂]; exact (show inner ℂ ((κ u) x) ((κ v) y)=kennel Y H D'.circuit j z (survey Y H j z strict (⟨u,x⟩ : Choir Y H j z strict)) (survey Y H j z strict (⟨v,y⟩:Choir Y H j z strict)) from (show _root_.YM.Kernel.Gram _ from C).measure _ _ ) ▸ sees Y H V D' j z u v S₁ S₂ (x:=freeze Y H u j z strict x) (y:= freeze Y H v j z strict y) P R h a b
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.analyzes
#print axioms YM.CF.Buffered.Afterglow.Tower.sounds
