import YM.SU5.Relativistic.AllErected
import YM.SU5.Relativistic.FirGreen
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
variable (n:ℕ)
include D G t
-- pays complete upwards linear
lemma cabinLift : ∀ f:F₀, (P s n) f.val∈ Cabin K j:=by
 intro f; obtain ⟨S,h,r⟩:=hutSpec j K f
 have hx:Tower.region j (Heat.gaugeShift Λ.block 0) (K).ℓ S:=by simpa [gaugeShift] using r
 have hg:= future_climb Y H j 0 hx n
 refine ⟨_,t.allSupport Y H V Q _ s n h,fun i u=>?_⟩; specialize hg i u; unfold Heat.gaugeShift at hg; push_cast at hg; simp at hg; exact le_trans (by omega) hg
noncomputable def cargoV : Cabin (tent Y H) j →ₗ[ℂ] (Cabin (tent Y H) j) where
 toFun:=fun f=> ⟨_,cabinLift Y H D G u t j s n f⟩
 map_add' f g:=by
    apply Subtype.ext; obtain ⟨U,v,w⟩:= hutSpec j K f; obtain ⟨W,h,p⟩:=hutSpec j K g; exact t.allAdding Y H V Q _ s n (v.mono (subset_union_left (s₂:=W))) (h.mono subset_union_right)
 map_smul' a f:= by apply Subtype.ext; exact t.ampAll Y H V Q _ s n (hutSpec j K f).choose_spec.1 a
local notation "Λ₀"=> Λ.R.L.val
local notation "M" n:max=> cargoV Y H D G u t j s n
lemma starts (f:F₀): (M 0) f=f:= Subtype.ext rfl -- n accidentally
lemma powers (f:F₀)(k:ℕ): (M n) (α k f)=α (Λ.R.L.val^n*k) ((M n) f):=by
 apply Subtype.ext; obtain ⟨S,h,r⟩:=hutSpec j K f
 let a:= Heat.gaugeShift Λ.block (2*(k:ℤ)); let X:= mirror K j 0 f.val
 change (P s n) (mirror K j a (mirror K j 0 f.val))=chime K j (Heat.gaugeShift Λ.block (2*(↑(Λ.R.L.val^n*k:ℕ):ℤ))) ((P s n) f.val) -- 2* int not nat cast? def
 unfold chime
 rw [t.allTurning Y H V Q _ s n (axial K j 0 h),t.allTurning Y H V Q _ s n h,planeAt,planeAt,mul_zero]; unfold a Heat.gaugeShift; push_cast; congr 1; ring
omit D G t
-- measure on the exact panels. chord convention
noncomputable def creed : F₀→ₗ⋆[ℂ] F₀→ₗ[ℂ] ℂ := chilly K j (audition Y H V G d c (SameCharacter.resident Y H V G d false (c d) x) s)
include D G t
local notation "B₁" s:max=> creed Y H D G d j c x s
lemma chorded (f g:F₀): (B₁ s) f g=ψ s (Complex.I • (mirror K j 0 f.val*g.val)):= rfl
lemma fervour (f:F₀):0≤ (B₁ s) f f:=by obtain ⟨S,h,r⟩:=hutSpec j K f; exact residentPrice Y H D G u t d j c x h s r
lemma block_step(f g:F₀): stream Y H G.refine s n (Complex.I • (mirror K j 0 f.val*g.val)) = Complex.I • (mirror K j 0 ((M n) f).val * ((M n) g).val):=by
 obtain ⟨S,h,r⟩:=hutSpec j K f; obtain ⟨R,v,p⟩:=hutSpec j K g
 let z:=mirror K j 0 f.val; let V':=g.val
 have he:=t.allCrossing Y H V Q u s n (axial K j 0 h) v (mirror_detached Λ l r p)
 have ht:= ((axial K j 0 h).mono (subset_union_left (s₂:=R))).mul (v.mono subset_union_right)
 rw [Bool.xor_self] at ht
 rw [←t.originally Y H V Q u s n (aux_test (.smul _ ht)),t.ampAll Y H V Q u s n ht]
 change stream _ _ (fun s=>T s false) s n (mirror _ _ _ _ * V')=_ at he; unfold V' at he
 rw [he,t.allTurning Y H V Q u s n h,planeAt,mul_zero]; rfl
lemma assurance(f g:F₀): (B₁ (s+n)) ((M n) f) ((M n) g)= (B₁ s) f g:=by
 rw [chorded Y H D G u t,chorded Y H D G u t,←block_step Y H D G u t]
 exact elect_refine _ _ _ _ _ _ _ ((levied j K f g).scale Complex.I) s n

end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.unB_contract
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.assurance
