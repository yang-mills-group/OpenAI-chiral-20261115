import YM.SU5.Relativistic.FrontSign
import YM.SU5.Relativistic.BoothProj
import YM.SU5.Relativistic.CompassBill
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

variable {S V':Finset Cover}{f g:Family (tent Y H)}(p:InTest (tent Y H) true S true f)(q:InTest (tent Y H) true V' true g)
local notation "Δ₀" => relocate (tent Y H)
local notation "Kv" J:max k:max F:max T:max=>stringUp Y H D G d J c x s k F T
include D G p q
lemma oppositions (i r:ℤ) : (Kv j k f g) i r= -(Kv j k g f) (-i) (-r):=by
 let F':=Δ₀ k r g; let X':= Δ₀ j i F'; have hx:=froll j (froll k q r) i
 let VV:=Complex.I • (f*X'); have hv:TestFamily K true (Complex.I • (f*X')):=by
    apply TestFamily.scale; exact aux_test ((p.mono (subset_union_left (s₂:=plow K j i (plow K k r V')))).mul (hx.mono subset_union_right))
 unfold stringUp; rw [← elect_slide Y H D.univ_ G j d c (SameCharacter.resident Y H D.univ_ G d false (c d) x) hv (2* -i) s]
 have ht:= aux_test (flow_port K j (Heat.gaugeShift Λ.block (2* -i)) hv.paid.choose_spec)
 rw [← elect_slide Y H D.univ_ G k d c (SameCharacter.resident Y H D.univ_ G d false (c d) x) ht (2* -r) s]
 have he: Δ₀ k (-r) (Δ₀ j (-i) VV)= - (Complex.I • (g * (Δ₀ j (-i) (Δ₀ k (-r) f)))):=by
    have hz(j:Axis)(k:ℤ)(F:Family K)(a:ℂ):Δ₀ j k (a • F)=a • Δ₀ j k F:= chime_scale _ _ _ a
    unfold VV X' F'
    rw [hz,hz,relocate_mul,relocate_mul,edge_roll j _ _ (froll k q r), neg_add_cancel,edge_void j (froll k q r),edge_roll k _ _ q,neg_add_cancel,edge_void k q,unions K k j p,signMark K (froll j (froll k p (-r)) (-i)) q]; simp [Sector.grainB]
 change ψ s (Δ₀ k (-r) (Δ₀ j (-i) VV))=_
 rw [he]; let F:Dome K:= ⟨_, (show TestFamily K true (g * Δ₀ j (-i) (Δ₀ k (-r) f)) from aux_test ((q.mono (subset_union_left (s₂:=plow K j _ (plow K k _ _)))).mul ((froll j (froll k p (-r)) (-i)).mono subset_union_right))).scale Complex.I⟩; exact (audition Y H D.univ_ G d c _ s).map_neg F
lemma tilt_axis(i r:ℤ): (Kv j k f g) i r=(Kv k j f g) r i:=by unfold stringUp; rw [unions K j k q]
include t σ
lemma northeast (A B) (z:Stock (Kv j k f g) (P₁) A B): Tendsto (fun t:ℕ×ℕ=> (Kv j k f g) t.1 t.2) atTop (𝓝 (inner ℂ A ((P₁).calm B))) :=by
 let σ' : j≠ k:= Ne.symm σ
 obtain ⟨A',B',uQ⟩:= stocks Y H D G u t d k c x s j σ' p q
 refine Signs.quadrant (P₁) (perroll Y H D G u t d k c x s ⟨j,σ'⟩) A B A' B' z ?_
 intro ε e; apply (uQ ε e).mono
 intro i t' r; dsimp only; rw [tilt_axis Y H D G d j c x s k p q]; exact t' r
 
lemma southwest (A B) (z:Stock (Kv j k f g) (P₁) A B): Tendsto (fun t:ℕ×ℕ=> (Kv j k f g) (- (t.1:ℤ)) (- (t.2:ℤ))) atTop (𝓝 (inner ℂ A ((P₁).calm B))) :=by
 let σ' : j≠ k:= Ne.symm σ; let R':= perroll Y H D G u t d k c x s ⟨j,σ'⟩
 obtain ⟨A',B',uP⟩:= stocks Y H D G u t d k c x s j σ' q p -- g, f
 let K' := Kv j k f g
 have hp: Stock (fun m n=> K' n (-m)) (revW R') A' (-B') := by
    intro ε e; apply (uP ε e).mono
    intro i t' r
    unfold revW; dsimp only; unfold K'; rw [oppositions Y H D G d j c x s k p q,tilt_axis Y H D G d j c x s k q p,neg_neg,map_neg,inner_neg_right,dist_neg_neg]; exact t' _
 obtain ⟨A'',B'',uX⟩:= stocks Y H D G u t d j c x s k σ q p
 have hh: Stock (fun i j'=> K' (-i) (-j')) (P₁) A'' (-B''):=by
    intro ε e; apply (uX ε e).mono; intro i t' r
    dsimp only; unfold K'; rw [oppositions Y H D G d j c x s k p q, neg_neg,neg_neg,map_neg,inner_neg_right,dist_neg_neg]; exact t' r
 exact Signs.neg_quadrant (P₁) A B z (revW R') _ _ hp _ _ hh
omit q
lemma vanishing_ff: Tendsto (fun n:ℕ×ℕ=> (Kv j k f f) n.1 n.2) atTop (𝓝 0):=by
 obtain ⟨A,B,z⟩:= stocks Y H D G u t d j c x s k σ p p
 have hx:= northeast Y H D G u t d j c x s k σ p p _ _ z
 have hp:= southwest Y H D G u t d j c x s k σ p p _ _ z
 let Qx:= inner ℂ A ((P₁).calm B)
 have he:Tendsto (fun n:ℕ×ℕ=> (Kv j k f f) n.1 n.2) atTop (𝓝 (-Qx)):=hp.neg.congr fun n=> (oppositions Y H D G d j c x s k p p _ _).symm
 have h:Qx=-Qx:=tendsto_nhds_unique hx he
 exact (show Qx=0 from (by exact Signs.eqneg _ h)) ▸ hx
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.vanishing_ff
