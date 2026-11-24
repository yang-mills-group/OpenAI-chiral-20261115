import YM.SU5.Relativistic.Dort
import YM.SU5.Relativistic.Trucks
import YM.SU5.Relativistic.Quintile
import YM.SU5.Relativistic.StreetSign
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
local notation "Λ₀"=> Λ.R.L.val
local notation "M" n:max=> cargoV Y H D G u t j s n
local notation "B₁" s:max=> creed Y H D G d j c x s

open HostLegal MeshClock
local notation "R₁"=> timeMesh Λ
local notation "U"=>flier Y H D G u t d j c x
variable (k:Axis)(σ:k≠j)
-- parity-ind in pose computations
variable {Z:Calibration}{S:Finset Cover}{v b₀:Bool}{F:Family Z}
open Signs
local notation "μ"=> mirror K j 0
local notation "P₁"=>perroll Y H D G u t d j c x s ⟨k,σ⟩
local notation "Π"=>upCycle Y H D G u t d j c x
local notation "ξ"=> (U).entry s

open CF.Pannier.Chancel.ScreeV
include D G t
lemma even_persists {z:ℤ}{S W:Finset Cover}{F G':Family (tent Y H)}{r:ℕ}(p:0<r)(t':Till (tent Y H) r j z S W)
    (v:InTest (tent Y H) false S false F)(a: InTest (tent Y H) false W false G') (f:Neutral (tent Y H) F)(g:Neutral (tent Y H) G')(e:ψ s (F*G') ≠ ψ s F*ψ s G') : FundX Y H D G d j c x s (T:=T) S W F G' false z r:=by -- pattern fix
 refine ⟨t',v,a,⟨f,g⟩,fun i v e h=>regionGap Y H j s z r t' _ _ e h,fun n=> ⟨t.neutrally Y H V Q _ s n v.widen f,t.neutrally Y H V Q _ s n a.widen g,⟨_,(has_footprint Λ l s S).persists n,t.allSupport Y H V Q _ s n v.widen⟩,⟨_,(has_footprint Λ l s W).persists n,t.allSupport Y H V Q _ s n a.widen⟩⟩, ‖ψ s (F*G')-ψ s F*ψ s G'‖, (norm_pos_iff.mpr (sub_ne_zero.mpr e)), fun n=>Pays5.requires_wedge Y H D G _ t d j c x s n v a z p t' _ (le_refl _)⟩

omit D G t
section geometry
variable (C:Calibration)(l':Axis)(αx β:ℤ)(η:ℕ)
lemma slideHon {S:Finset Cover}{v w:Bool}{F:Family C}(h:InTest C v S w F)(e:Neutral C F):Neutral C (mirror C l' αx F):= fun m=>covariant_reflected (h.support m) (e m) _ _
lemma slideMove {S:Finset Cover}{v w:Bool}{F:Family C}(h:InTest C v S w F)(e:Neutral C F):Neutral C (relocate C l' αx F):= slideHon C l' _ (axial C l' 0 h) (slideHon C l' _ h e)
lemma slideMul {F F':Family C}(p:Neutral C F)(q:Neutral C F'):Neutral C (F*F'):=by intro m x i; dsimp only [Pi.mul_apply]; rw [p m x i,q m x i,map_mul]
variable {r:ℕ}{z:ℤ}{A B': Finset Cover}(u':Till C r j z A B')
include σ u'
lemma walksGap : Till C r j z (plow C k αx A) (plow C k αx B'):=by
 constructor
 · intro i v; obtain ⟨t,h,rfl⟩:=plow_stays C k αx _ v; rw [moves,if_neg σ.symm]; exact u'.stay t h
 intro i v; obtain ⟨t,h,rfl⟩:=plow_stays C k αx _ v; rw [moves,if_neg σ.symm]; exact u'.start t h
lemma turnedGap : Till C r j z (reflectedBox k αx A) (reflectedBox k αx B'):=by
 constructor
 · intro i v; obtain ⟨t,h,rfl⟩:=Finset.mem_image.mp v; rw [fling_move,if_neg σ]; exact u'.stay t h
 intro i v; obtain ⟨t,h,rfl⟩:=Finset.mem_image.mp v; rw [fling_move,if_neg σ]; exact u'.start t h
omit σ
lemma bothGap {A₁ Gbx :Finset Cover}(v:Till C r j z A₁ Gbx) : Till C r j z (A∪A₁) (B'∪Gbx):= ⟨fun x h=> (mem_union.mp h).elim (u'.stay _) (v.stay _),fun x h=> (mem_union.mp h).elim (u'.start _) (v.start _)⟩
end geometry
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
