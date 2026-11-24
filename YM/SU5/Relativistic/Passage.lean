import YM.SU5.Relativistic.FrontSign
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
variable (s:ℕ)
local notation "α" => walkV Y H j
local notation "F₀"=> Cabin (tent Y H) j
local notation "κ" u:max=>mirror K j u
local notation "Λ₀"=> Λ.R.L.val
local notation "B₁" s:max=> creed Y H D G d j c x s

open HostLegal MeshClock
local notation "R₁"=> timeMesh Λ
local notation "U"=>flier Y H D G u t d j c x
local notation "W₀" s:max=> Tower.Field Y H s j 0 false
local notation "Ωe"=> doorstep Y H V Q G.clipped j false (c j) (χ j)
local notation "Φ" s:max=> arriving Y H V s Q G.clipped j false (c j) (χ j)
local notation "Υ" s:max=> (U).entry s
local notation "E₁"=> indoor Y H V Q G.clipped j false (c j) (χ j)
local notation "E₂"=> (U).booth
local notation "Δ₀"=> relocate (tent Y H)
local notation "B₀"=> ruler Λ.block
structure Slice (Z:Calibration)(j:Axis) (w:ℕ) where
 f:Family Z
 h : ∃ S:Finset Cover, InTest Z true S true f ∧ Between Z j 0 (ruler Z.B*(w:ℤ)) S
lemma Slice.single {Z:Calibration}{j:Axis}{w:ℕ}{S T:Slice Z j w}(h:S.f=T.f): S=T:=by rcases S with ⟨s,t⟩; rcases T with ⟨s',t'⟩; cases h; rfl

variable {w:ℕ}
variable (F : Slice (tent Y H) j w)
noncomputable def uphill {k:ℕ}(b:s≤k): Slice (tent Y H) j (Λ₀^(k-s)*w) where
 f:=stream Y H (fun s=>T s true) s (k-s) F.f
 h:=by
    obtain ⟨S,h,h'⟩:= F.h; refine ⟨_,t.allSupport Y H V G.history u s (k-s) h,?_⟩
    push_cast; rw [mul_left_comm]; exact expands_shape Y H h' _
local notation "X" p:max=> uphill Y H D G u t j s F p
lemma ridge_peak {k r:ℕ}(b:s≤k)(g:k≤ r):
    (uphill Y H D G u t j k (X b) g).f=(X (b.trans g)).f:=by
 change stream Y H (fun s=>T s true) k (r-k) ((P s (k-s)) F.f)=(P s (r-s)) F.f
 conv_lhs=>arg 4; rw [←Nat.add_sub_of_le b]
 rw [←joined,show k-s+(r-k)=r-s by omega]
lemma eve_test (x:W₀ s) :∃ S:Finset Cover,InTest K true S false x.val∧ Tower.region j 0 (K).ℓ S:=by
 obtain ⟨A₀,e,v⟩:= (show ∃ M:Finset Cover,InTest K true M false x.val∧Tower.region j (meshface (Λ:=Λ) 0 s) (K).ℓ M from ((purpose_ok ..).mp x.property).1)
 exact ⟨A₀,e,by rwa [area0] at v⟩
lemma uphill_inside (F:Slice (tent Y H) j w)(x:W₀ s): ∃ S:Finset Cover, InTest K true S true (F.f*Δ₀ j w x.val) ∧ Tower.region j 0 (K).ℓ S:=by
 obtain ⟨S,h,p⟩:= F.h; let Xx:= tick Y H s j 0 false (2*w) x; obtain ⟨T₀,v,q⟩:= eve_test Y H j s Xx
 refine ⟨S∪T₀,(h.mono subset_union_left).mul ((show InTest K true T₀ false _ from (timed_apply .. : Xx.val=_ ) ▸ v).mono subset_union_right),fun i t=> (mem_union.mp t).elim (fun v=>(p i v).1) (q i)⟩
noncomputable def sprout : (Tower.Field Y H s j 0 false) →ₗ[ℂ] Cabin (tent Y H) j where
 toFun x:= ⟨F.f * Δ₀ j (w:ℤ) x.val, uphill_inside Y H j s F x⟩
 map_add' x y:=Subtype.ext (by change F.f* Δ₀ j (w:ℤ) (x.val+y.val)=_; unfold relocate; rw [chime_plus,mul_add]; rfl)
 map_smul' a x:=Subtype.ext (by change F.f* Δ₀ j (w:ℤ) (a • x.val)=_; unfold relocate; rw [chime_scale,Algebra.mul_smul_comm]; rfl)
variable {k r:ℕ}(e:s≤k)(b₂:k≤r)
local notation "N" k:max p:max=> sprout Y H j k (X p)
include D G t
lemma grade_ho {f:Family (tent Y H)}{v:Bool}{S:Finset Cover}(p:InTest K true S v f)(m:ℕ)(z:ℤ): stream Y H (fun s=>T s v) s m (Δ₀ j z f)=Δ₀ j ((Λ₀:ℤ)^m*z) (stream Y H (fun s=>T s v) s m f):=by
 unfold relocate chime; rw [t.allTurning Y H V Q _ s m (axial K j 0 p),t.allTurning Y H V Q _ s m p]; unfold planeAt gaugeT Heat.gaugeShift; rw [mul_zero]; congr 1; ring!
lemma preparesV {S:Finset Cover}(p: Tower.region j 0 (K).ℓ S): Tower.region j (B₀*w) (K).ℓ (plow K j w S):=by
 intro i z; obtain ⟨i,z',rfl⟩:=plow_stays K j _ _ z; rw [moves,if_pos rfl]; specialize p _ z'; change _ ≤ i j+B₀*w; linarith
include e b₂
lemma first_glass (x':W₀ k): (U).cl k r ((N k e) x')= (N r (le_trans e b₂)) (Raise Y H G.history.circuit j 0 false k r b₂ x'):=by
 let F':=X e; obtain ⟨S,h,v⟩:= F'.h; let u':=Λ₀^(k-s)*w
 obtain ⟨L,h₀,p⟩:= eve_test Y H j k x'; let h1:= froll j h₀ (u':ℤ)
 let W:=plow K j u' L
 have hz:=cover_between K Λ l rfl j (S:=S) (fun i w=>(v i w).2) (M:=W) (preparesV Y H D G u t j p)
 apply Subtype.ext
 let y:=X (e.trans b₂)
 change (P k (r-k)) (F'.f* Δ₀ j (u':ℤ) x'.val)= y.f * Δ₀ j ((Λ₀^(r-s)*w:ℕ):ℤ) (stream Y H G.refine _ _ _)
 have hp:=t.allCrossing Y H V Q u k (r-k) h h1 hz
 rw [show ∀ f,(P k (r-k)) f=stream Y H (fun s=>T s (Bool.xor true false)) k (r-k) f from fun _=>rfl,hp,grade_ho Y H D G u t j k h₀,t.originally Y H V Q u k (r-k) (x:=x'.val) (aux_test h₀)] -- tune originally
 rw [show (P k (r-k)) F'.f=y.f from ridge_peak Y H D G u t j s F e b₂]
 congr 2; unfold u'; push_cast; rw [←mul_assoc ((Λ₀:ℤ)^(r-k)),←pow_add,show r-k+(k-s)=r-s by omega]
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.first_glass
