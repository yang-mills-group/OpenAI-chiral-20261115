import YM.SU5.Relativistic.FirstFrost
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
noncomputable def flier : Tier (Cabin (tent Y H) j) where
 F:=fun s=>creed Y H D G d j c x s
 cl:=fun s k=>cargoV Y H D G u t j s (k-s)
 fares r:= fervour Y H D G u t d j c x r
 up s k p x' y:= by
    have hp:= assurance Y H D G u t d j c x s (k-s) x' y
    rw [show s+(k-s)=k by omega] at hp; exact hp
 same s x':=by rw [Nat.sub_self]; rfl
 further s i k p q x':=by
    apply Subtype.ext; change stream Y H (fun s=>T s true) i (k-i) (stream Y H (fun s=>T s true) s (i-s) x'.val)=stream Y H (fun s=>T s true) s (k-s) x'.val
    conv_lhs=>arg 4; rw [←Nat.add_sub_of_le p]
    rw [←joined,show i-s+(k-i)=k-s by omega]
 -- for same defeq perhaps
local notation "R₁"=> timeMesh Λ
local notation "U"=>flier Y H D G u t d j c x
include D G t
lemma tilt_ok (k:ℕ)(f g:F₀): (B₁ s) (α k f) g=(B₁ s) f (α k g):=by
 rw [chorded Y H D G u t,chorded Y H D G u t,← beams]
 exact (elect_slide Y H V G j d c _ ((levied j K (α k f) g).scale Complex.I) _ s).symm
lemma fares_rate (k:ℕ)(f:F₀):0≤ (B₁ s) f (α k f):=by
 obtain ⟨S,h,r⟩:= hutSpec j K f
 let v:=Heat.gaugeShift Λ.block (2*(k:ℤ)); let F':= chime K j v f.val
 have hp: 0≤ v:= by unfold v Heat.gaugeShift; positivity
 have hz: Tower.region j (Heat.gaugeShift Λ.block (2*(k:ℤ))) (K).ℓ (address j v S):=by
   intro i t; obtain ⟨u,t',rfl⟩:=mem_image.mp t; change v+_ ≤ _; simp only [Pi.add_apply,Pi.smul_apply]; simp; specialize r u t'; omega
 have Ht: mirror K j v F'= mirror K j 0 f.val:= slides1 j h v
 rw [chorded Y H D G u t]; change 0 ≤ ψ s (Complex.I • (mirror K j 0 f.val*F')); rw [← Ht]; exact allRates Y H D G u t d j c x (flow_port K j _ h) s (2*(k:ℤ)) hz
include t
lemma deposit (f:F₀):∃ r:ℕ,s≤r ∧∃ y:F₀, α 2 y=(M (r-s)) f:=by
 obtain ⟨S,h,r⟩:=hutSpec j K f; let k:=32*Λ.block.val; let F':= (M k) f; let m:=gaugeShift Λ.block 4
 have ht:InTest K true (volumeAround Λ l k S) true F'.val:=t.allSupport Y H V Q u s k h
 have hS:Tower.region j (Heat.gaugeShift Λ.block 0) (K).ℓ S:=by simpa [gaugeShift] using r
 have hg:= future_climb Y H j 0 hS k
 have hp: Tower.region j 0 (K).ℓ (address j (-m) (volumeAround Λ l k S)):=by
    intro i w; obtain ⟨i,w',rfl⟩:= mem_image.mp w; specialize hg i w'; unfold Heat.gaugeShift at hg; simp at hg
    rw [moves,if_pos rfl]; unfold k at hg; unfold m Heat.gaugeShift; omega
 let y:F₀:= ⟨chime K j (-m) F'.val, address j (-m) _, flow_port K j (-m) ht,hp⟩
 -- missing angle brackets for subtype proof
 refine ⟨s+k,by omega,y,Subtype.ext ?_⟩; rw [show s+k-s=k by omega]
 change chime K j (Heat.gaugeShift Λ.block (2*↑(2:ℕ))) (chime K j (-m) F'.val) = F'.val; rw [hoops K j _ ht,show gaugeShift Λ.block (2*↑(2:ℕ))=m from (by unfold m; norm_num),add_neg_cancel]; exact reversal K j 0 ht
noncomputable def hiker:Ride (flier Y H D G u t d j c x) (timeMesh Λ) where
 flow:=walkV Y H j
 source:= steps_orig Y H j
 compose:=steps_add Y H j
 ascent s n k ht x':= powers Y H D G u t j s (n-s) x' k
 symmetry:=tilt_ok Y H D G u t d j c x
 proper:=fares_rate Y H D G u t d j c x
 paid s n f:=halls Y H D G u t d j c x s f n
 possible:= deposit Y H D G u t j
-- embed physical semantics and spectra later
noncomputable def upCycle : OS.Semigroup (flier Y H D G u t d j c x).cabin.H j:= (hiker Y H D G u t d j c x).mapGrid.monoAxis j
lemma visits (i:ℕ)(k:ℕ)(p:s≤k)(f:F₀): (upCycle Y H D G u t d j c x).E (whenly (timeMesh Λ) s i) ((U).entry k f)=(U).entry k (α (Λ₀^(k-s)*i) f) := by
 let X:=hiker Y H D G u t d j c x; change X.mapGrid.track _ _=_; rw [X.reaches]; exact X.rides _ _ _ p _
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.visits
