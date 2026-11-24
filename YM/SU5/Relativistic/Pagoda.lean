import YM.SU5.Relativistic.Spats
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
variable {S₁:Finset Cover}{v₁:Bool} (q:Bool)(m:ℕ)(p:ℤ)(z:Cover)
-- singular marks lifted to registration cut m, then define trajectory. If m not born yet meaningless. q holds whether moving. no statement before anchor. n≥m only.
def plated (v:Bool)(F:Family (tent Y H)): ℕ→ℤ→ Family (tent Y H):= winTurn Y H (T:=T) j m q v (if q then Vacancy.chart (tent Y H) z (stream Y H (fun s=>T s v) s (m-s) F) else stream Y H (fun s=> T s v) s (m-s) F)
local notation "⦃" v:max "," b:max "," F:max "⦄"=> plated Y H (T:=T) j s b m z v F
local notation "Ms" n:max z:max=> notch (timeMesh Λ) n z
include t
lemma winFlight {F:Family (tent Y H)} (h:InTest K true S₁ v₁ F)(w:Slab (timeMesh Λ))(p':hulls (Λ:=Λ) (l:=l) j s S₁ w): ∀ᶠ m:ℕ in atTop,∀ z:Cover,z j =0→ (match v₁ with
    | true=> ∃ X Z, TimedOdd Y H D G u t d j c x m (plated Y H (T:=T) j s q m z true F) (shifted q w.lower.val) (shifted q w.upper.val) X Z
    | false=> ∃ X, TimedEve Y H D G d j c x m (plated Y H (T:=T) j s q m z false F) (shifted q w.lower.val) (shifted q w.upper.val) X) := by
 filter_upwards [fleetHull Y H j s p'] with m hΓ z g
 obtain ⟨h₀,r,d₀,g0,hB,hX,Vt⟩:=hΓ
 cases v₁
 · have ht:= t.allSupport Y H V Q u s (m-s) h
   cases q
   · exact dawn_frame Y H D G u t d j c x m _ false ht g0 Vt hB hX
   exact dawn_frame Y H D G u t d j c x m _ true (tour_test z ordinate ht) g0 (passable Y H j Vt z g) hB hX
 have ht:=t.allSupport Y H V Q u s (m-s) h; cases q
 · exact win_frame Y H D G u t d j c x m _ false ht g0 Vt hB hX
 exact win_frame Y H D G u t d j c x m _ true (tour_test z ordinate ht) g0 (passable Y H j Vt z g) hB hX
variable {F:Family (tent Y H)}
local notation "Ctr"=> Vacancy.chart (tent Y H)
local notation "Π" v:max n:max F:max=> stream Y H (fun s=> T s v) s (n-s) F
variable (V':InTest (tent Y H) true S₁ v₁ F)
include D
lemma toured_grade {n:ℕ}(a: List Axis)(v:Cover){W:Finset Cover}{g:Bool}{f':Family K}(h: InTest K true W g f') :
    stream Y H (fun s=>T s g) s (n-s) (cad K a v f')= cad K a (fun i=>castor R₁ s n (v i)) (stream Y H (fun s=>T s g) s (n-s) f'):=by
 induction a with| nil=>rfl| cons i l ih=>rw [cad_step,cad_step,grade_ho Y H D G u t i s (tour_test v l h),ih]; rfl
include V'
lemma tied {n:ℕ}(k:s≤ m)(p:m≤n): stream Y H (fun s=>T s v₁) m (n-m) (Π v₁ m F)=Π v₁ n F:=by
 conv_lhs=>arg 4; rw [←Nat.add_sub_of_le k]
 rw [←joined,show m-s+(n-m)=n-s by omega]
lemma never_paid {n:ℕ}(p':s≤ m)(l:m≤n)(p:ℤ):
    ∃ S:Finset Cover, InTest K true S v₁ ((plated Y H (T:=T) j s q m z v₁ F) n p):=by
 let T':= t.allSupport Y H V Q u s (m-s) V'; cases q
 · exact ⟨_,froll j (t.allSupport Y H V Q u m (n-m) T') 0⟩
 exact ⟨_,froll j (t.allSupport Y H V Q u m (n-m) (tour_test z ordinate T')) p⟩
lemma plate_zero {n:ℕ}(h:s ≤ m)(k:m≤n)(p:ℤ):
    plated Y H (T:=T) j s false m z v₁ F n p=Π v₁ n F :=by
 change Δ₀ j 0 (stream Y H (fun s=>T s v₁) m (n-m) (Π v₁ m F))=_
 rw [tied Y H D G u t s m V' h k,edge_void j (t.allSupport Y H V Q u s _ V')]
lemma plate_more {n:ℕ}(h:s ≤ m)(k:m≤n)(p:ℤ):
    plated Y H (T:=T) j s true m z v₁ F n p= Δ₀ j p (Ctr (fun i=> castor R₁ m n (z i)) (Π v₁ n F)):=by
 change Δ₀ j p (stream Y H (fun s=>T s v₁) m (n-m) (cad K ordinate z (Π v₁ m F)))=_
 rw [toured_grade Y H D G u t m _ _ (t.allSupport Y H V Q u s _ V'),tied Y H D G u t s m V' h k]; rfl
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.winFlight
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.plate_more
