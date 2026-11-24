import YM.SU5.Relativistic.Fnat
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
variable {w:ℕ}(F : Slice (tent Y H) j w)
local notation "F₁"=> Slice (tent Y H) j
local notation "Bc₀" s:max F:max b:max=> blossoms Y H D G u t d j c x s F b
noncomputable def back: Slice (tent Y H) j w where
 f:=Δ₀ j w (mirror K j 0 F.f)
 h:=by
    obtain ⟨S,h,p⟩:= F.h
    have hp:Between K j (- (B₀*w)) 0 (reflectedBox j 0 S):=slab_flip Y H j p
    have hv:=hp.relocate K j w; change Between K j (B₀*w+_) (B₀*w+_) _ at hv; exact ⟨plow K j w _,froll j (axial K j 0 h) w,by change Between K j 0 (B₀*w) (plow K j w (reflectedBox j 0 S)); simpa only [add_neg_cancel,add_zero] using hv⟩
lemma back_twice : back Y H j (back Y H j F)=F:=by
 apply Slice.single; change Δ₀ j _ (mirror K j 0 (Δ₀ j _ (mirror K j 0 _)))=F.f
 obtain ⟨S,h,v⟩:=F.h; rw [backsV j (axial K j 0 h), reversal K j 0 h, edge_roll j _ _ h, add_neg_cancel,edge_void j h]
include t
lemma back_grade {k:ℕ}(p:s≤k): uphill Y H D G u t j s (back Y H j F) p= back Y H j (uphill Y H D G u t j s F p):=by
 apply Slice.single; let e:=k-s
 change (P s e) (Δ₀ j w (mirror K j 0 _))=Δ₀ j _ (mirror K j 0 ((P s e) F.f))
 obtain ⟨S,h,v⟩:=F.h; rw [grade_ho Y H D G u t j s (axial K j 0 h),t.allTurning Y H V Q _ s e h,planeAt,mul_zero]; push_cast; rfl
-- action
noncomputable def reed (z:Cabin (tent Y H) j): Tower.Field Y H s j 0 false:=by
 refine ⟨F.f * Δ₀ j w z.val,(purpose_ok ..).mpr ⟨?_,nofun⟩⟩; obtain ⟨S,h,k⟩:=F.h; let G:=walkV Y H j w z; obtain ⟨U',hp,p⟩:= hutSpec j K G
 refine ⟨S∪U',(h.mono subset_union_left).mul (hp.mono subset_union_right),?_⟩; rw [area0]; exact fun i v=>(mem_union.mp v).elim (fun h=>(k i h).1) (p i)
-- reed includes t? include auto includes t in lemmas, definitions with namespace includes? W uphill
noncomputable def otters (b:0<w) : (flier Y H D G u t d j c x).booth→L[ℂ] E₁:= (-Complex.I) • (Bc₀ s (back Y H j F) b).adjoint
local notation "Bo" s:max F:max b:max=> otters Y H D G u t d j c x s F b
-- relation finite
lemma Allies(X:W₀ s)(v: F₀): inner ℂ ((Υ s) (sprout Y H j s (back Y H j F) X)) ((Υ s) v)= Complex.I * inner ℂ ((Φ s) X) ((Φ s) (reed Y H j s F v)) :=by
 rw [Tier.arrived]; let B₀':=sprout Y H j s (back Y H j F) X
 rw [show inner ℂ ((Φ s) X) ((Φ s) (reed Y H j s F v))=ψ s (mirror K j 0 X.val*(F.f*Δ₀ j w v.val)) from (earns Y H V s Q G.clipped j false (c j) (χ j) X (reed Y H j s F v)).trans (selected_here Y H D G d j c x s _)]
 change ψ s (Complex.I • (mirror K j 0 B₀'.val*v.val))=_
 let v':=mirror K j 0 B₀'.val*v.val; let a:=Complex.I
 have hz: ψ s (a • v')= a * ψ s v':= (audition Y H V G _ c _ s).map_smul a (show Dome K from ⟨_,levied j K B₀' v⟩)
 rw [hz, ←show ψ s (Δ₀ j w v')= ψ s v' from elect_slide Y H V G j d c _ (levied j K B₀' v) (2*(w:ℤ)) s]
 have hB:B₀'.val=(back Y H j F).f* Δ₀ j w X.val:=rfl
 let h:=(eve_test Y H j s X).choose_spec.1
 have hp: (back Y H j (back Y H j F)).f=F.f:= congrArg Slice.f (back_twice ..)
 unfold v'; rw [hB,mirror_times,relocate_mul,relocate_mul,show Δ₀ j w (mirror K j 0 (back Y H j F).f) = F.f from hp, backsV j h,edge_roll j _ _ (axial K j 0 h),add_neg_cancel,edge_void j (axial K j 0 h)]
 have hw: F.f* mirror K j 0 X.val= mirror K j 0 X.val*F.f:=by simpa only [Sector.grainB,Bool.and_false,Bool.false_eq_true,ite_false,one_smul] using signMark K F.h.choose_spec.1 (axial K j 0 h)
 rw [hw,mul_assoc]
-- up-arrow stability
lemma sprout_exact (b:0<w) (v:W₀ s): (Bc₀ s F b) ((Φ s) v)=(Υ s) (sprout Y H j s F v):=by
 rw [blossoms_later Y H D G u t d j c x s F b (le_refl _)]
 apply congrArg; apply Subtype.ext; change (P s (s-s)) F.f *Δ₀ j (Λ₀^(s-s)*w:ℕ) v.val=F.f*Δ₀ j _ v.val; rw [Nat.sub_self,pow_zero,one_mul]; rfl
lemma petals (b:0<w){k:ℕ}(p:s≤k): Bc₀ s F b= Bc₀ k (uphill Y H D G u t j s F p) (Nat.mul_pos (pow_pos Λ.R.L.property _) b):=by
 let e:=Nat.mul_pos (pow_pos Λ.R.L.property (k-s)) b
 let W:=uphill Y H D G u t j s F p
 let A:=Bc₀ s F b; let B:=Bc₀ k W e
 refine DFunLike.coe_injective ((folks_dense Y H D G d j c x k).equalizer A.continuous B.continuous ?_)
 funext i; let r:=i.fst.val; let z:=i.2; let v:k ≤ r:=i.fst.property; change (Bc₀ s F b) ((Φ r) z) = (Bc₀ k W e) ((Φ r) z)
 rw [blossoms_later Y H D G u t d j c x s F b (p.trans v),blossoms_later Y H D G u t d j c x k W e v]; apply congrArg; apply Subtype.ext
 let A':= uphill Y H D G u t j s F (p.trans v); let B':= uphill Y H D G u t j k W v
 change A'.f*_ = B'.f*_
 have he:B'.f=A'.f:=ridge_peak Y H D G u t j s F p v
 change A'.f* Δ₀ j ((Λ₀^(r-s)*w:ℕ):ℤ) z.val=B'.f* Δ₀ j ((Λ₀^(r-k)*(Λ₀^(k-s)*w):ℕ):ℤ) z.val; rw [he,←mul_assoc,←pow_add,show r-k+(k-s)=r-s by omega]
lemma reeds_climb {k:ℕ}(p:s≤k)(z:Cabin K j): (reed Y H j k (uphill Y H D G u t j s F p) ((U).cl s k z))=Raise Y H G.history.circuit j 0 false s k p (reed Y H j s F z):=by
 apply Subtype.ext; change ((P s (k-s)) F.f)*Δ₀ j _ ((P s (k-s)) z.val)= stream Y H G.refine s (k-s) (F.f* Δ₀ j w z.val)
 obtain ⟨S,h,u'⟩:=F.h; obtain ⟨W,v,e⟩:=hutSpec j K z; have ht:=froll j v (w:ℤ)
 have hz:TestFamily K true (F.f* Δ₀ j w z.val):=aux_test ((h.mono (subset_union_left (s₂:=plow K j w W))).mul (ht.mono subset_union_right))
 have he:= t.allCrossing Y H V Q u s (k-s) h ht (cover_between K Λ l rfl j (S:=S) (fun i v=>(u' i v).2) (preparesV Y H D G u t j e))
 rw [←t.originally Y H V Q u s (k-s) hz, ←Bool.xor_self true, he, grade_ho Y H D G u t j s v]; push_cast; rfl
lemma back_petals (b:0<w){k:ℕ}(p:s≤k): (Bo s F b)= (Bo k (uphill Y H D G u t j s F p) (Nat.mul_pos (pow_pos Λ.R.L.property _) b)):=by
 unfold otters; rw [petals Y H D G u t d j c x s (back Y H j F) b p,back_grade]
lemma reeds_on (b:0<w) (z:Cabin K j) : (Bo s F b) ((Υ s) z)=(Φ s) (reed Y H j s F z):=by
 apply (folks_dense Y H D G d j c x s).eq_of_inner_right ℂ; intro i
 let k:=i.fst.val; let p:s≤ k:=i.fst.property; let v:=i.2; change inner ℂ ((Φ k) v) _= _
 rw [back_petals Y H D G u t d j c x s F b p,← Tier.increase _ p,show (Φ s) (reed Y H j s F z)= (Φ k) (Raise Y H G.history.circuit j 0 false s k p _) from (flourishes Y H V _ Q G.clipped j false (c j) (χ j) k p _).symm,←reeds_climb Y H D G u t d j c x s F p]
 unfold otters; rw [ContinuousLinearMap.smul_apply,inner_smul_right,ContinuousLinearMap.adjoint_inner_right,sprout_exact, Allies]; change (-Complex.I * (Complex.I * _))=_; rw [←mul_assoc,neg_mul,Complex.I_mul_I,neg_neg,one_mul]; rfl
lemma reeds_later (b:0<w){k:ℕ}(p:s≤k)(z:Cabin K j) : (Bo s F b) ((Υ k) z)=(Φ k) (reed Y H j k (uphill Y H D G u t j s F p) z):=by rw [back_petals Y H D G u t d j c x s F b p,reeds_on]
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.reeds_later
