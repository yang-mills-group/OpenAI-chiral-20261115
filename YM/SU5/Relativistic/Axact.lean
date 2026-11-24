import YM.SU5.Relativistic.Illume
import YM.SU5.Selected.Landing
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
open Germ SelectionAnalysis CF.Pannier.Chancel.ScreeV
local notation "P₁"=> roadCrew Y H D G u t d j c x
local notation "Ξ₁"=> trueSun Y H D G u t d j c x
local notation "Up₁"=> upCycle Y H D G u t d j c x
local notation "Ξ₀"=> mainsea Y H V Q G.clipped j false (c j) (χ j)
local notation "Φ₀"=> peninsula Y H V Q G.clipped j false (c j) (χ j)
local notation "Γ"=> marks (timeMesh Λ)
local notation "Φ₁"=> convoy Y H D G u t d j c x
local notation "δ"=> daylight (timeMesh Λ)
local notation "ArS"=> (P₁).aviator (look j)
local notation "Ωb"=> vocation Y H V Q G.clipped j false (c j) (χ j)
local notation "vt" s:max=> land Y H V s Q G.clipped j false (c j) (χ j)
local notation "Haya" b:max=> Faze Y H D G (T:=T) d j c x s b
local notation "π"=> (ArS).orthogonalProjectionOnto
variable {S T':Finset Cover}{v:Bool}{F H':Family (tent Y H)}{r:ℕ}{z:ℤ}
lemma plane_pay (p:Till K r j z S T'): Tower.region j 0 (tent Y H).ℓ (reflectedBox j 0 (plow (tent Y H) j (-z) S)) ∧ Tower.region j 0 (tent Y H).ℓ (plow (tent Y H) j (-z) T'):=by
 constructor
 · intro i x; obtain ⟨k,v,rfl⟩:= mem_image.mp x; obtain ⟨y,h,hx⟩:= plow_stays K j _ _ v
   rw [fling_move,if_pos rfl,hx,moves,if_pos rfl,mul_neg]; have hp:=p.stay y h; omega
 intro i x; obtain ⟨k,v,hx⟩:= plow_stays K j _ _ x; rw [hx,moves,if_pos rfl,mul_neg]; have ht:=p.start k v; omega
structure Audited (F H':Family (tent Y H))(z:ℤ)(A B': Cabin (tent Y H) j) : Prop where
 offers : A.val=mirror K j 0 (Δ₀ j (-z) F)
 admits : B'.val=Δ₀ j (-z) H'
 gains : Faze Y H D G (T:=T) d j c x s true F H' (Ξ₁) (Complex.I • (Υ s) A) ((Υ s) B')
 continuous_rate : InnerRoad (Λ:=Λ) j (Ξ₁) (Complex.I • (Υ s) A) ((Υ s) B')
-- produce exact
include t
lemma drum_act (h:InTest K true S true F)(g:InTest K true T' true H')(e:Till K r j z S T')(w:∀k:Trans j,Soft Y H D G (T:=T) d k.val c x s true F H') : ∃ A B', Audited Y H D G u t d j c x s F H' z A B':=by
 let X:= Δ₀ j (-z) F; let Z:= Δ₀ j (-z) H'
 obtain ⟨q,p⟩:=plane_pay Y H j e
 let A:Cabin K j:= ⟨mirror K j 0 X,_, axial K j 0 (froll j h (-z)),q⟩
 let B':Cabin K j:= ⟨Z,_,froll j g (-z),p⟩
 have hv:Faze Y H D G (T:=T) d j c x s true F H' (Ξ₁) (Complex.I • (Υ s) A) ((Υ s) B'):= early_faze Y H D G u t d j c x s h g (A:=-z) (reversal K j 0 (froll j h (-z))) rfl
 exact ⟨A,B',rfl,rfl,hv,full_r Y H D G u t d j c x s h g hv w⟩
omit t in
lemma dia_zero : diameter (a:=j) (0:Axis→ℝ)=0:=by change OS.Semigroup.SEP j (0:E4)=0; exact map_zero _
lemma drum_gain {A B':Cabin K j} (p:Audited Y H D G u t d j c x s F H' z A B')(q:InTest K true T' true H'):
    inner ℂ ((ArS).orthogonalProjectionOnto (Complex.I • (Υ s) A)) (π ((Υ s) B'))= ψ s (F*H'):=by
 rw [← lastFaze Y H D G d j c x s p.gains q,Indoor_peak (X:=(Ξ₁)) j p.continuous_rate]
 rw [glass_window (Ξ₁) δ (Up₁) rfl (togetherP Y H D G u t d j c x),dia_zero j]
 change _= inner ℂ (show (P₁).Realm (look j) from _) ((Φ₁).E _ ((Φ₁).U 0 (π ((Υ s) B')))); rw [show Real.toNNReal ((0:Axis→ℝ) j)=0 by simp,(Φ₁).uZero,(Φ₁).eZero]; rfl
-- for even want also Ω call Φ conjugate across first, scan receipt.
structure Curated (F H':Family (tent Y H))(z:ℤ)(A B':Tower.Field Y H s j 0 false):Prop where
 offers : A.val=mirror K j 0 (Δ₀ j (-z) F)
 admits : B'.val=Δ₀ j (-z) H'
 gains : Faze Y H D G (T:=T) d j c x s false F H' (Ξ₀) ((Φ s) A) ((Φ s) B')
 press : InnerRoad (Λ:=Λ) j (Ξ₀) ((Φ s) A) ((Φ s) B')
lemma maven_act (h:InTest K true S false F)(g:InTest K true T' false H')(e:Till K r j z S T')(w:∀k:Trans j,Soft Y H D G (T:=T) d k.val c x s false F H') : ∃ A B', Curated Y H D G (T:=T) d j c x s F H' z A B':=by
 obtain ⟨q,p⟩:=plane_pay Y H j e
 let A:W₀ s:= ⟨mirror K j 0 (Δ₀ j (-z) F),(purpose_ok ..).mpr ⟨⟨_,axial K j 0 (froll j h (-z)),by rw [area0]; exact q⟩,nofun⟩⟩
 let B':W₀ s:= ⟨Δ₀ j (-z) H',(purpose_ok ..).mpr ⟨⟨_,froll j g (-z),by rw [area0]; exact p⟩,nofun⟩⟩
 have hv: Faze Y H D G (T:=T) d j c x s false F H' (Ξ₀) ((Φ s) A) ((Φ s) B'):=meadowry Y H D G u t d j c x s h g (A:=-z) (reversal K j 0 (froll j h (-z))) rfl
 exact ⟨A,B',rfl,rfl,hv,full_r Y H D G u t d j c x s h g hv w⟩
lemma maven_gain {A B':W₀ s}(p:Curated Y H D G (T:=T) d j c x s F H' z A B')(h:InTest K true S false F)(g:InTest K true T' false H'): inner ℂ ((vt s) A) ((vt s) B')= ψ s (F*H') ∧ inner ℂ ((vt s) A) Ωb= ψ s F ∧ inner ℂ Ωb ((vt s) B')= ψ s H':=by
 constructor
 · rw [←lastFaze Y H D G d j c x s p.gains g, Indoor_peak (X:=(Ξ₀)) j p.press]; change _= scene Y H V s Q G.clipped j false (c j) (χ j) A B' 0
   rw [peninsula_window,dia_zero j,show Real.toNNReal ((0:Axis→ℝ) j)=0 by simp,(Φ₀).eZero,(Φ₀).uZero]; rfl
 have hv(n:W₀ s): inner ℂ Ωb ((vt s) n)= ψ s n.val:= (land_call Y H V s Q G.clipped j false (c j) (χ j) n).trans (selected_here Y H D G d j c x s _)
 refine ⟨?_, (hv B').trans ((congrArg (ψ s) p.admits).trans (elect_slide Y H V G j d c _ (aux_test g) (2*(-z)) s))⟩
 rw [←inner_conj_symm,land_call,show (starRingEnd ℂ) _= _ from (all_mirror Y H V s Q G.clipped j false (c j) (χ j) (futureMark Y H s j false A) j).symm]; rw [selected_here Y H D G d j c x s]; change ψ s (mirror K j 0 A.val)=_; rw [p.offers,reversal K j 0 (froll j h (-z))]; exact elect_slide Y H V G j d c _ (aux_test h) (2*(-z)) s
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.drum_gain
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.maven_gain
