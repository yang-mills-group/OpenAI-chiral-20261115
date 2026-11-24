import YM.SU5.Relativistic.Passage
import YM.SU5.Relativistic.PairForm
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
lemma slab_flip {S:Finset Cover}(h:Between (tent Y H) j 0 (B₀*w) S): Between K j (-(B₀*w)) 0 (reflectedBox j 0 S):=by
 intro i z; obtain ⟨x,y,rfl⟩:= mem_image.mp z; rw [fling_move,if_pos rfl]; specialize h x y; omega
lemma slab_group{S:Finset Cover}(h:Between K j 0 (B₀*w) S): Between K j (-(B₀*w)) (B₀*w) (reflectedBox j 0 S∪S):=by
 have he:0 ≤ B₀*(w:ℤ):=mul_nonneg (ruler_gene _).le (by positivity)
 intro i u; rcases mem_union.mp u with v|v; · have t:=slab_flip Y H j h i v; omega
 specialize h i v; omega
-- positive receipt build θ f shift w
noncomputable def wreath: Entry Y H s j false (w+w):=by
 let P₀:= Complex.I • (mirror K j 0 F.f * F.f); let R:= relocate K j (w:ℤ) P₀
 have hp:∃ S:Finset Cover, InTest K true S false R ∧ Between K j 0 (B₀*((w+w:ℕ):ℤ)) S:=by
    obtain ⟨S,h,a⟩:= F.h
    let Ta:=reflectedBox j 0 S; let W:=Ta∪S; have ht:InTest K true W false (mirror K j 0 F.f*F.f):=((axial K j 0 h).mono subset_union_left).mul (h.mono subset_union_right)
    refine ⟨plow K j w W,froll j (InTest.smul _ ht) w,?_⟩
    have hy:= (slab_group Y H j a).relocate K j w; change Between K j (B₀*w+_) (B₀*w+_) _ at hy; simpa only [Nat.cast_add,mul_add,add_neg_cancel] using hy
 let Z:W₀ s:= ⟨R,(purpose_ok ..).mpr ?_⟩ -- tune construct
 exact ⟨Z,hp⟩
 obtain ⟨S,h,v⟩:=hp; exact ⟨⟨S,h,fun i p=> by rw [area0]; exact (v i p).1⟩, nofun⟩
lemma wreath_val : (wreath Y H j s F).val.val=Δ₀ j w (Complex.I • (mirror K j 0 F.f * F.f)):=rfl
variable {k:ℕ}(p:s≤k)(bb:0<w)
local notation "F₁"=> uphill Y H D G u t j s F p
local notation "F₂"=> wreath Y H j s F
local notation "Bc"=> procession Y H V Q G.clipped j false (c j) (χ j)
local notation "By"=> Bc (entrance Y H V s Q G.clipped j false (c j) (F₂) (by omega))
local notation "Sy"=> sprout Y H j k (F₁)
include t p
lemma wreath_later: (furnished Y H s Q j false _ (F₂) k p).val.val= (wreath Y H j k (F₁)).val.val:=by
 let e:=k-s; let v:=Complex.I; let M:=mirror K j 0 F.f; let P':=M*F.f
 change stream Y H G.refine s e (F₂).val.val= _; rw [wreath_val,wreath_val]
 obtain ⟨S,h,g⟩:=F.h; have Xb:=slab_flip Y H j g
 have hM:=axial K j 0 h; have hp:InTest K true (reflectedBox j 0 S∪S) false P':=(hM.mono subset_union_left).mul (h.mono subset_union_right)
 have hv:=InTest.smul v hp; have ht:= froll j hv w
 rw [←t.originally Y H V Q u s e (x:=relocate K j w (v • P')) (aux_test ht)] -- R mismatch need `change`
 change stream Y H (fun s=>T s false) s e (Δ₀ j w (v • P'))=_
 rw [grade_ho Y H D G u t j s hv e,t.ampAll Y H V Q u s e hp]
 have he:= t.allCrossing Y H V Q u s e hM h (cover_between K Λ l rfl j (S:=reflectedBox j 0 S) (fun i u=>(Xb i u).2) (fun i w=>(g i w).1))
 change stream Y H (fun s=>T s false) s e P'= (P s e) M * (P s e) F.f at he
 rw [he, show M=_ from (rfl : M=mirror K j 0 F.f),t.allTurning Y H V Q u s e h,planeAt,mul_zero]; push_cast; rfl
include bb
lemma plait (x':W₀ k): inner ℂ ((Υ k) (Sy x')) ((Υ k) (Sy x'))= inner ℂ ((Φ k) x') (By ((Φ k) x')):=by
 rw [Tier.arrived]; let m:=Λ₀^(k-s); let f:=F₁; let J:= wreath Y H j k f; let W:=furnished Y H s Q j false _ (F₂) k p
 let h:= Sy x'
 have h0:(By) ((Φ k) x')= (Φ k) (slabT Y H k j false _ W x'):= slot_high Y H V s Q G.clipped j false (c j) (χ j) _ _ k p x'
 rw [h0]; change ψ k (Complex.I • (mirror K j 0 h.val*h.val))= inner ℂ (bud _ _ _ _ _ _ _ _ _ _ x') (bud _ _ _ _ _ _ _ _ _ _ _); rw [earns,selected_here Y H D G d j c x k]; change _= ψ k (mirror K j 0 x'.val * (slabT Y H k j false _ W x').val)
 rw [slab_eq]; unfold W; rw [wreath_later Y H D G u t j,wreath_val]
 let w':=m*w; have hψ:=elect_slide Y H V G j d c (SameCharacter.resident Y H V G d false (c d) x) ((levied j K h h).scale Complex.I) (2*(w':ℤ)) k
 rw [← show ψ k (Δ₀ j w' (Complex.I • (mirror K j 0 h.val*h.val)))= ψ k (Complex.I • _) from hψ] -- tactic
 have hscale {f}: Δ₀ j w' (Complex.I • f)= Complex.I • Δ₀ j w' f:=chime_scale ..
 have hmf:f.f* Δ₀ j w' x'.val=h.val:=rfl
 have hp:= eve_test Y H j k x'; let hX:=hp.choose_spec.1
 have H':(mirror K j 0 f.f)*(mirror K j 0 (Δ₀ j w' x'.val))=mirror K j 0 (Δ₀ j w' x'.val)*mirror K j 0 f.f := by simpa only [Sector.grainB,Bool.and_false,Bool.false_eq_true,ite_false,one_smul] using signMark K (axial K j 0 f.h.choose_spec.1) (axial K j 0 (froll j hX _))
 have hFlip: Δ₀ j w' (mirror K j 0 (Δ₀ j w' x'.val))=mirror K j 0 x'.val:=by
    rw [backsV j hX,edge_roll j _ _ (axial K j 0 hX),add_neg_cancel,edge_void j (axial K j 0 hX)]
 change ψ k (Δ₀ j w' (Complex.I • (mirror K j 0 h.val*h.val)))=ψ k (mirror K j 0 x'.val * (Δ₀ j w' (Complex.I • (mirror K j 0 f.f*f.f))*Δ₀ j (m*(w+w):ℕ) x'.val))
 rw [←hmf,mirror_times,H',hscale, hscale,relocate_mul,relocate_mul,relocate_mul,relocate_mul,hFlip,edge_roll j _ _ hX,show m*(w+w)= w'+w' from mul_add ..,Nat.cast_add,Algebra.smul_mul_assoc,Algebra.mul_smul_comm]; simp only [mul_assoc] -- tune
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.plait
