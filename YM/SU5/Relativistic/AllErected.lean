import YM.SU5.Relativistic.ElectedChord
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat PhaseChoice SlabMark Vacancy Tapestry Tapestry.Altitude Tapestry.Exhibition Tower.Selected
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {a b:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{L:Rack Λ l}{B:Clay Λ l}
    (D : Exhibition Y H a b I E L B)
local notation "V"=>D.univ_
variable (G:SatinVerification.GroundExtension (i:=a) (k:=b) (E:=E) Y H)
variable (u:ℕ→ℕ) {T:ℕ→Bool→Family (tent Y H)→Family (tent Y H)}(t:GradesAll (i:=a) (a:=G.rows) (k:=b) (b:=G.columns) Y H u T)
variable (d j:Axis) (c:∀ j:Axis,Arena Y H G.history.circuit j 0 false)
variable (x:displayAlgebra Y H D.univ_ G.history G.clipped d false (c d)→⋆ₐ[ℂ] ℂ)
local notation "χ" i:max=> displacement Y H D.univ_ G.history G.clipped d false (c d) x i (c i)
local notation "ψ"=>evaluate Y H D.univ_ G d c (SameCharacter.resident Y H D.univ_ G d false (c d) x)
local notation "D₀"=> Dome (tent Y H)
local notation "Ξ"=> Cloud (Dome (tent Y H))
local notation "φ" n:max => response Y H V n G.history G.clipped j false (c j) (χ j)
local notation "P" s:max F:max=>stream Y H (fun s=>T s true) s F
local notation "Q"=> G.history
variable {S:Finset Cover} {f:Family (tent Y H)} (h:InTest (tent Y H) true S true f) (s:ℕ)
local notation "μ"=> mirror K j (0:ℤ)

local notation "Z" z:max=>Heat.gaugeShift Λ.block z
include t h
lemma allRates (w:ℤ)(r:Tower.region j (Z w) (K).ℓ S): 0 ≤ ψ s (Complex.I • (mirror K j (Z w) f*f)):=by
 let r:Tower.region j (Z w) (K).ℓ S:=r
 let t' :=-(Λ.block.val :ℤ)*w; let a' := 2*t'; have he:a'=(a':ℤ):=rfl
 have hP: Heat.gaugeShift Λ.block w+2*a'=0:= by unfold Heat.gaugeShift a' t'; ring
 let U:= chime K j a' f; let R:= address j a' S
 have hx: Tower.region j 0 ((tent Y H).ℓ) R:=by
    intro i p; obtain ⟨k,u,rfl⟩:= mem_image.mp p
    have ht:= r _ u; rw [moves,if_pos rfl]; omega
 let F:= Complex.I • (mirror K j (Z w) f*f)
 have hv: InTest K true (reflectedBox j (Z w) S ∪ S) false F:= InTest.smul _ (((axial K j _ h).mono subset_union_left).mul (h.mono subset_union_right))
 have Ht: chime K j a' F= Complex.I • (mirror K j 0 U*U):=by
    unfold F; rw [chime_scale,chime_product,faceSlide K j _ _ h,hP]
 rw [←elect_sold Y H V G j s d c (SameCharacter.resident Y H V G d false (c d) x) t' (aux_test hv)] -- maybe doesn't match
 change 0≤ ψ s (chime K j a' F); rw [Ht]
 exact residentPrice Y H D G u t d j c x (flow_port K j a' h) s hx
omit h
-- actual positive theorem as costs matrix all parity channels, using common relation on even and 0 for odd. Also supply proof shift any d. For each b fixed-charge half marks (F odd not ∈Marks; ψ-defined on their pair*). neutral subdomain later. 
private def colSpace (J:Calibration)(d:Axis) (z:ℤ)(b:Bool): Submodule ℂ (Family J) where
 carrier:= {f|∃ S:Finset Cover, InTest J true S b f∧ Tower.region d z J.ℓ S}
 add_mem' :=by
    rintro f g ⟨S,h,p⟩ ⟨T,v,q⟩; exact ⟨S∪T,(h.mono subset_union_left).add (v.mono subset_union_right),fun i t=>(Finset.mem_union.mp t).elim (p i) (q i)⟩
 zero_mem':=⟨∅,InTest.zero,by simp [Tower.region]⟩
 smul_mem':=by intro x f h; obtain ⟨S,h,v⟩:=h; exact ⟨S,InTest.smul _ h,v⟩

section prior
variable {b':Bool}
variable (w:ℤ)

local notation "θ" => mirror K j (Heat.gaugeShift Λ.block w)
-- admonish one session. Note L using complex multiplication via I. h entry args no exact OccObs
local notation "Ξ₁"=> colSpace (tent Y H) j (Heat.gaugeShift Λ.block w) b'
omit t
private lemma everyBill (f g:Ξ₁):TestFamily K true (mirror K j (Heat.gaugeShift Λ.block w) f.val*g.val):=by
 obtain ⟨S,p,h⟩:= f.property; obtain ⟨T,q,t⟩:=g.property
 have he : false=b'.xor b':=by cases b'<;>rfl
 apply aux_test (S:=reflectedBox j (Heat.gaugeShift Λ.block w) S∪T); rw [he]
 exact ((axial K j _ p).mono subset_union_left).mul (q.mono subset_union_right)
-- We cannot insert f.val itself with markE, but pairs have the full prescription
noncomputable def capKernel : (Ξ₁)→ₗ⋆[ℂ] (Ξ₁)→ₗ[ℂ] ℂ where
 toFun f:={
   toFun:=fun g=> ψ s (Reflect.chord b' • (mirror K j (Heat.gaugeShift Λ.block w) f.val*g.val))
   map_add':=fun g h=>by
      let f' := everyBill Y H j w f
      rw [AddSubmonoid.coe_add,mul_add,smul_add]
      have hz:TestFamily K true _ :=(f' g).scale (Reflect.chord b')
      let a : Dome K:=⟨_,hz⟩; let b : Dome K:=⟨_,(f' h).scale (Reflect.chord b')⟩; exact (audition Y H V G d c (SameCharacter.resident Y H V G d false (c d) x) s).map_add a b
   map_smul':=fun a g=>by
      rw [Submodule.coe_smul,Algebra.mul_smul_comm,smul_comm (Reflect.chord b')]; exact (audition Y H V G d c (SameCharacter.resident Y H V G d false (c d) x) s).map_smul a (⟨_,(everyBill Y H j w f g).scale (Reflect.chord b')⟩:Dome K) }
 map_add' f g:= LinearMap.ext fun k=>by
    change ψ s (Reflect.chord b' • (θ (f+g).val * k.val)) = ψ s _ + ψ s _; rw [AddSubmonoid.coe_add,mirror_plus,add_mul,smul_add]
    exact (audition Y H V G d c (SameCharacter.resident Y H V G d false (c d) x) s).map_add (⟨_,(everyBill Y H j w f k).scale (Reflect.chord b')⟩:Dome K) ⟨_,(everyBill Y H j w g k).scale (Reflect.chord b')⟩
 map_smul' a f:=LinearMap.ext fun k=>by
    change ψ s (Reflect.chord b' • (θ (a • f:Ξ₁).val * k.val)) = star a * ψ s _; rw [Submodule.coe_smul,mirror_scale,Algebra.smul_mul_assoc, smul_comm (Reflect.chord b')]; exact (audition Y H V G d c (SameCharacter.resident Y H V G d false (c d) x) s).map_smul (star a) (⟨_,(everyBill Y H j w f k).scale (Reflect.chord b')⟩:Dome K)
include t
lemma cap_tilt (f:Ξ₁):0 ≤ capKernel Y H D G d j c x s w f f := by
 obtain ⟨S,h,p⟩:=f.property
 cases b'
 · change 0≤ ψ s ((1:ℂ) • _); rw [one_smul]; exact elect_plane Y H V G j d c _ h p s
 exact allRates Y H D G u t d j c x h s w p
lemma erected {I:Type*}[Fintype I](p:I→Family (tent Y H))(h:∀ i,∃ S:Finset Cover,InTest (tent Y H) true S b' (p i) ∧ Tower.region j (Heat.gaugeShift Λ.block w) (K).ℓ S): Matrix.PosSemidef (Matrix.of fun i i' => ψ s (Reflect.chord b' • (mirror K j (Heat.gaugeShift Λ.block w) (p i) * p i'))):= halfSpaceKernel (capKernel Y H D G d j c x s w) (cap_tilt Y H D G u t d j c x s w) fun i=> ⟨p i,h i⟩
end prior
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
