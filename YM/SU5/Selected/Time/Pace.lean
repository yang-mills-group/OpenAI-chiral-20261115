import YM.SU5.Selected.Cor.Soothe
import YM.SU5.Selected.Time.Diary
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
namespace Curtain
-- develop generic accounting to translate to true gap and temporal steps in Actor stage3 of selected same law. sign α.
local notation "L"=> f
variable (p : ∀ x∈ S,x j+(tent Y H).ℓ ≤ ruler (tent Y H).B*z)
    (v : ∀ x∈ T, ruler (tent Y H).B*z+ruler (tent Y H).B+(tent Y H).ℓ ≤ x j)
    (A' : Alight Y H V Q Qc j C s a0 k0 f g S T)
local notation "ιM"=> plow K j
local notation "τ"=> tick Y H s j 0 false
include p
private lemma beginning : Tower.region j (meshface (Λ:=Λ) 0 s) (K).ℓ (reflectedBox j 0 (ιM (-z) S)):=by
 rw [area0]; intro x h; obtain ⟨x,k,rfl⟩:=mem_image.mp h; rw [reflected_coord]; obtain ⟨x,t,rfl⟩:= plow_stays K j (-z) S k; rw [moves,if_pos rfl]; specialize p x t; linarith
omit p
include v
private lemma gracious : Tower.region j (meshface (Λ:=Λ) 0 s) (K).ℓ (ιM (-z-1) T):=by
 rw [area0]; intro x h; obtain ⟨x,q,rfl⟩:= plow_stays K j (-z-1) T h; rw [moves,if_pos rfl]; specialize v x q; linarith
omit v

open Guild
open Spectral Spectral.Alps
variable {χ : CapCharacter Y H V Q Qc j false C} (X : Birthplace Y H V Q Qc j false C χ)
include V Q Qc C
local notation "Tη" u:max => (journey Y H V Q Qc j false C X).track u
local notation "ς" => markedActor Y H V Q Qc j false C X s
local notation "μ"=> vacuum Y H V Q Qc j false C X
local notation "J"=> Diary.jetTime Y H V Q Qc j false C X
local notation "V₀" => journey Y H V Q Qc j false C X
local notation "u₀"=> phaseRead Y H V Q Qc j C χ s
local notation "W₀"=> whenly (timeMesh Λ) s -- h→
include X
lemma when_clock (x:F₊ s) (w:ℕ): (Tη (W₀ w)) (ς x) = ς ((τ (2*w)) x):= (congrArg (fun D':X.H.Op=> D' (ς x)) ((V₀).track_even s w)).trans (tempo_now Y H V Q Qc j false C X s (2*w) x) -- implicit notation V₀ captures s?
omit X
section account
variable (hX : InTest (tent Y H) false S false f)(hY : InTest (tent Y H) false T false g)
variable (ehX:Neutral (tent Y H) f)(ehY : Neutral (tent Y H) g)
variable (x y: Tower.Field Y H s j 0 false)
local notation "ϕ"=> θ ((U (-z)) f)
local notation "ψ"=> (U (-z-1)) g
include z hX hY p v ehX ehY
-- lantern entry points $x y$ (ensured). Strict slot energy computed via difference, no assuming centered at THAT split.
lemma wakes_x : ∃ x y:F₊ s, x.val=ϕ∧ y.val=ψ∧ InTest K false (reflectedBox j 0 (plow K j (-z) S)) false x.val ∧ InTest K false (plow K j (-z-1) T) false y.val∧Neutral K x.val∧Neutral K y.val:=by
 let F:=(U (-z)) f; let G:=(U (-z-1)) g
 let i:=gentle Y H hX.widen; let w:=gentle Y H hY.widen; let a:=moved Y H j false (-z) i; let d:= dual Y H j false a; let b:=moved Y H j false (-z-1) w
 have hF:InTest K false (plow K j (-z) S) false F:= flow_port K j _ hX; have hc:= axial (K) j 0 hF; have hg:InTest K false (ιM (-z-1) T) false G:= flow_port K j _ hY
 let x:= asField Y H j false s d hc.widen (beginning Y H j z s p); let y:= asField Y H j false s b hg.widen (gracious Y H j z s v)
 exact ⟨x,y,rfl,rfl,hc,hg,covariant_flips (K) j 0 hF.widen (chime_cov (K) j _ hX.widen ehX),chime_cov K j _ hY.widen ehY⟩
variable (e:x.val = Tower.mirror (tent Y H) j 0 (relocate (tent Y H) j (-z) f))(e': y.val= relocate (tent Y H) j (-z-1) g)
omit ehX ehY
local notation "u_1" f:max => cap Y H V s Q Qc j false C f
include X e e'
lemma temporal_eq (w:ℕ): inner ℂ (ς x) ((Tη (W₀ (1+w))) (ς y)) = u₀ (f*(U (w:ℤ)) g):=by
 let F:=(U (-z)) f; let G:=(U (-z-1)) g; let a:=(1+(w:ℤ))+(-z-1); have he:a=-z+w:=by unfold a; omega
 let i:= gentle Y H hX.widen; let P:= gentle Y H hY.widen; let t:= moved Y H j false (w:ℤ) P; let s':= composed false i t; let Y₁:=Tη (W₀ (1+w))
 have hk:u₀ (f*(U (w:ℤ)) g)=χ ((N s) s'):= phase_read Y H V Q Qc j C s χ s';
 have hp: toTest Y H j false s x=dual Y H j false (moved Y H j false (-z) i) := Subtype.ext e
 have hg: (U (-z)) ((U (w:ℤ)) g)=(U (1+w)) G:=by rw [relocate_sums K j _ _ (Tower.aux_test hY.widen)]; unfold G; rw [relocate_sums K j _ _ (Tower.aux_test hY.widen),show 1+(w:ℤ)+(-z-1)=_ from he]
 let y₁:= (τ (2*(1+w))) y; have hG:y₁.val=(U (1+(w:ℤ))) G:=by unfold y₁; rw [timed_apply,e', Nat.cast_add,Nat.cast_one] -- `timed_apply` explicit
 have hi: bornTest Y H j false s x y₁ = moved Y H j false (-z) s':=by
    apply Subtype.ext; change mirror _ _ _ x.val*y₁.val=(U (-z)) (f*(U (w:ℤ)) g); rw [e,Tower.reversal K j 0 (show InTest K false (ιM (-z) S) false F from flow_port K j _ hX),relocate_mul,hG,hg] -- maybe mirror z meshface=0 by rfl? room. Tune
 rw [when_clock]; let X':=move_cap Y H V Q Qc j C (-z) s s'; exact (affirmation Y H V Q Qc j false C X s _ _).trans ( (congrArg χ ((congrArg (N s) hi).trans X')).trans hk.symm) -- tune
local notation "c₀" f:max=> u₀ f
lemma mean_t : inner ℂ μ (ς y)= c₀ g ∧ inner ℂ (ς x) μ=c₀ f:= by
 let i:= gentle Y H hX.widen; let t:=gentle Y H hY.widen
 let u:=moved Y H j false (-z) i; let m:= marked Y H V Q Qc j false C χ
 constructor
 · have he : toTest Y H j false s y=moved Y H j false (-z-1) t:=Subtype.ext e'
   have hk :u₀ g= m s t:= phase_read Y H V Q Qc j C s χ t; exact (actual_expect Y H V Q Qc j false C X s y).trans ((congrArg (m s) he).trans ((congrArg χ (move_cap Y H V Q Qc j C (-z-1) s t)).trans hk.symm))
 have he : (N s) (toTest Y H j false s x) = star ((N s) i):=by
    rw [show toTest Y H j false s x= dual Y H j false u from Subtype.ext e, read_mirror,show (N s) u =_ from (show (N s) u=(N s) i from move_cap Y H V Q Qc j C (-z) s i)]
 have ht:= (actual_expect Y H V Q Qc j false C X s x).trans ( (congrArg χ he).trans (map_star χ _)) -- star output
 have hk: u₀ f=χ ((N s) i):= phase_read Y H V Q Qc j C s χ i; exact (inner_conj_symm ..).symm.trans ((congrArg star ht).trans ((star_star _).trans hk.symm)) -- tune
end account
end Curtain
end Fern
end YM.CF.Buffered.Afterglow.Tower.Selection
open YM.CF.Buffered.Afterglow.Tower.Selection.Fern.Curtain
#print axioms temporal_eq
#print axioms mean_t
#print axioms when_clock
#print axioms wakes_x
#check @mean_t
#check @temporal_eq
#check @wakes_x
