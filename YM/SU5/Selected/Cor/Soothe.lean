import YM.SU5.Selected.Cor.Guild
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Selection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
open RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
open scoped InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock
open Vacancy

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b)
  (Qc : Clipped Y H (i ∘ a) (k ∘ b))
  (j : Axis) (C : Arena Y H Q.circuit j 0 false)
local notation "R" => Aurora Y H V Q j false C
local notation "A" => Ark.Ht Y H Q.circuit j 0 false C
local notation "W" => floorV Y H Q.circuit j 0 false C
local notation "F₊" n:max => Tower.Field Y H n j 0 false
local notation "φ" n:max => actor Y H n Q.circuit j 0 false C
local notation "Ω" => seat0 Y H V Q j false C
attribute [local instance] opCStarAlgebra
open CF.Pannier.Chancel Tapestry Papal
open CF.Pannier.Chancel.Lantern CF.Pannier.Chancel.Lantern.Bulb CF.Pannier.Chancel.Lantern.Bulb.Mezz
-- use C : Arena false only (assembly neutral). 
local notation "Ch"=> CapCharacter Y H V Q Qc j false C
local notation "Test"=> Vacancy.observable (tent Y H) false
local notation "readχ"=> phaseRead Y H V Q Qc j C
local notation "F₀" i:max=> cap Y H V i Q Qc j false C
local notation "N" i:max=> liftCap Y H V Q Qc j false C i
namespace Fern
open Commission Sermon
-- general j/time seam. orientation. Works before strongly continuous limit hypotheses. Mark coordinates are K units. Physical ticks are given in TimeKeeper Fermi level0 vs gauge campus ratio exactly two. 
variable (z : ℤ) (s:ℕ) {f g:Family (tent Y H)}{S T:Finset Cover} {a0 k0:ℝ}
local notation "U" u:max=>relocate K j u
--local notation "f" f:max=> f -- remove
local notation "θ"=> Tower.mirror K j 0
local notation "x₀" => (ruler (K).B*z)
local notation "R₀" => ruler (K).B
local notation "κ₁"=> (whenly (timeMesh Λ) s 1)
namespace Guild
-- develop generic accounting to translate to true gap and temporal steps in Actor stage3 of selected same law. sign α.
local notation "L"=> f
variable (p : ∀ x∈ S,x j+(tent Y H).ℓ ≤ ruler (tent Y H).B*z)
    (v : ∀ x∈ T, ruler (tent Y H).B*z+ruler (tent Y H).B+(tent Y H).ℓ ≤ x j)
    (A' : Alight Y H V Q Qc j C s a0 k0 f g S T)
local notation "ιM"=> plow K j
local notation "τ"=> tick Y H s j 0 false
lemma timeCoherence (Λ:Preparation)(s:ℕ): 2*((whenly (timeMesh Λ) s 1:ℝ≥0):ℝ)= markZ Λ s (ruler Λ.block):= by
 unfold whenly MeshClock.mill markZ precisionAt timeMesh ruler; push_cast; ring_nf
include p
private lemma beginning : Tower.region j (meshface (Λ:=Λ) 0 s) (K).ℓ (reflectedBox j 0 (ιM (-z) S)):=by
 rw [area0]; intro x h; obtain ⟨x,k,rfl⟩:=mem_image.mp h; rw [reflected_coord]; obtain ⟨x,t,rfl⟩:= plow_stays K j (-z) S k; rw [moves,if_pos rfl]; specialize p x t; linarith
omit p
include v
private lemma gracious : Tower.region j (meshface (Λ:=Λ) 0 s) (K).ℓ (ιM (-z-1) T):=by
 rw [area0]; intro x h; obtain ⟨x,q,rfl⟩:= plow_stays K j (-z-1) T h; rw [moves,if_pos rfl]; specialize v x q; linarith
omit v
lemma hour (x:F₊ s): ((τ 2) x).val= (U 1) x.val:= rfl -- coe natCast, maybe fails

-- inner for ANY α. Using zero caps already proved. Mark scope gauge true for both. Charge roles over aperture when moved preserve? don't claim.
variable {χ : CapCharacter Y H V Q Qc j false C} (X : Birthplace Y H V Q Qc j false C χ)
include V Q Qc C
lemma move_cap (x:Test) : (N s) (moved Y H j false z x)=(N s) x := whole_shift Y H V Q Qc j false C s (2*z) x
local notation "Tη" u:max => (journey Y H V Q Qc j false C X).track u
local notation "ς" => markedActor Y H V Q Qc j false C X s
local notation "μ"=> vacuum Y H V Q Qc j false C X
include A' X p v
-- χ(t) expectation path. Also all members p. sector. 
lemma retinue : ∃ x y:F₊ s,
       x.val= (θ) ((U (-z)) f) ∧
       y.val= (U (-z-1)) g ∧
       InTest K false (reflectedBox j 0 (plow K j (-z) S)) false x.val ∧
       InTest K false (plow K j (-z-1) T) false y.val ∧
       Neutral K x.val ∧ Neutral K y.val ∧
       inner ℂ μ (ς x)=0∧ inner ℂ μ (ς y)=0 ∧
       inner ℂ (ς x) ((Tη (κ₁)) (ς y))=(readχ χ) s (f*g) :=by
 let F:=(U (-z)) f; let G:=(U (-z-1)) g -- remove
 have he:= A'.inspires; have ht:= A'.blazes; let i:=gentle Y H he.1.widen; let w:=gentle Y H ht.1.widen; let a:=moved Y H j false (-z) i; let d:= dual Y H j false a; let b:=moved Y H j false (-z-1) w
 have hF:InTest K false (plow K j (-z) S) false F:= flow_port K j _ he.1; have hc:= axial (K) j 0 hF; have hg:InTest K false (ιM (-z-1) T) false G:= flow_port K j _ ht.1
 let x:= asField Y H j false s d hc.widen (beginning Y H j z s p); let y:= asField Y H j false s b hg.widen (gracious Y H j z s v)
 have hp:CovCover (K) x.val:= covariant_flips (K) j 0 hF.widen (chime_cov (K) j _ he.1.widen he.2.1); have hq:CovCover K y.val:= chime_cov K j _ ht.1.widen ht.2.1
 have f₁:(N s) a=0:=(move_cap Y H V Q Qc j C (-z) s i).trans (Cloak.forbidden Y H V Q Qc j C s i he.2.2)
 have f₂:(N s) b=0:=(move_cap Y H V Q Qc j C (-z-1) s w).trans (Cloak.forbidden Y H V Q Qc j C s w ht.2.2)
 have hl:(N s) d=0:=by unfold d; rw [read_mirror,f₁,star_zero]
 refine ⟨x,y,rfl,rfl,hc,hg,hp,hq,(actual_expect Y H V Q Qc j false C X s x).trans ?_,(actual_expect Y H V Q Qc j false C X s y).trans ?_,?_⟩
 · change χ ((N s) d)=_; rw [hl, map_zero]
 · change χ ((N s) b)=_; rw [f₂,map_zero]
 let Y₁:=(Tη κ₁); let u:= composed false i w
 have hk: (readχ χ) s (f*g)=χ ((N s) u):= phase_read Y H V Q Qc j C s χ u; have hi: bornTest Y H j false s x ((τ 2) y) = moved Y H j false (-z) u:= by
    apply Subtype.ext; change θ (θ F)* ((τ 2) y).val = (U (-z)) (f*g)
    have ht':(U 1) G=(U (-z)) g := (relocate_sums K j 1 (-z-1) (Tower.aux_test ht.1.widen)).trans (by rw [show 1+(-z-1)=-z by ring])
    exact (congrArg₂ (· * ·) (reversal K j 0 hF) ((show ((τ 2) y).val= (U 1) G from hour Y H j s y).trans ht')).trans ((relocate_mul K j (-z)).symm)
 have heq:(κ₁)=(whenly (timeMesh Λ) s 2/2):= by rw [show (2:ℕ)=1+1 from rfl,when_add,add_div,add_halves]; -- maybe NNReal add_halves
 let T':= (tempo_now Y H V Q Qc j false C X s 2 y); have htY:Y₁ (ς y)= ς ((τ 2) y) := (congrArg (fun z: X.H→L[ℂ] X.H=> z (ς y)) ((congrArg (journey Y H V Q Qc j false C X).track heq).trans (time_carry Y H V Q Qc j false C X s 2).symm)).trans T'
 change inner ℂ (ς x) (Y₁ (ς y))=_
 have htn: (N s) (bornTest Y H j false s x ((τ 2) y))=(N s) u:= (congrArg (N s) hi).trans (move_cap Y H V Q Qc j C (-z) s u)
 exact (congrArg (fun z:X.H=> inner ℂ (ς x) z) htY).trans ((affirmation Y H V Q Qc j false C X s x ((τ 2) y)).trans ((congrArg χ htn).trans hk.symm))
end Guild
end Fern
end YM.CF.Buffered.Afterglow.Tower.Selection
open YM.CF.Buffered.Afterglow.Tower.Selection.Fern.Guild
#print axioms retinue
