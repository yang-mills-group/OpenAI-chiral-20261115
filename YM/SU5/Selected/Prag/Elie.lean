import YM.SU5.Selected.Prag.Summit
import YM.SU5.Selected.Prag.Trove
import YM.SU5.Selected.Time.Pace
import YM.SU5.Selected.Prag.Pr
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 320000
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
  (C : ∀ j:Axis, Arena Y H Q.circuit j 0 false)
namespace Summer
open Germ
variable (j v:Axis)
local notation "θ" j:max=>mirror K j 0
local notation "T" v:max x:max=> relocate K v x
local notation "Y₀"=> timeMesh Λ
local notation "R" s:max r:max k:max=> Raise Y H Q.circuit k 0 false s r
local notation "Ξ" s:max r:max=> stream Y H D s (r-s)
local notation "W" j:max u:max=> Tower.Field Y H u j 0 false
local notation "M₀" s:max r:max=> castor Y₀ s r
local notation "B₀"=> (Λ.R.L.val:ℤ)
variable (s:ℕ)
variable (χ:CapCharacter Y H V Q Qc 3 false (C 3)) -- primary. Can generalize to arbitrary meeting Leg.
variable (qv:v≠j)
local notation "Λ₀" v:max=> escort Y H V Q Qc 3 false (C 3) v (C v) χ
variable (F: Birthplace Y H V Q Qc j false (C j) (escort Y H V Q Qc 3 false (C 3) j (C j) χ))
variable (P: Birthplace Y H V Q Qc v false (C v) (escort Y H V Q Qc 3 false (C 3) v (C v) χ))
local notation "V₀"=> Summer.Polaris Y H V Q Qc j false (C j) F
local notation "U₀" a:max=> (((V₀).crew a).play)
local notation "Π" a:max F:max=> Diary.jetTime Y H V Q Qc a false (C a) F
local notation "ρ" v:max F:max=> markedActor Y H V Q Qc v false (C v) F
---- Horizon & state of continuation restricted. Preserved labels (Altar). 
local notation "ζ"=> skyline Y H V Q Qc C j χ F
local notation "ξ"=> (Π j F)
open Spectral Spectral.Alps Germ.Alliance
local notation "Β"=> Actress.Label Y H j false
local notation "ν"=> Actress.Label.money Y H V Q Qc j false (C j) F
local notation "Φ"=> (V₀).Realm (look j)
local notation "w"=> vacuum Y H V Q Qc j false (C j) F
local notation "d"=> terse Y H V Q Qc C j χ F
noncomputable def worldShelf := Alliance.Arcadia (V₀) (daylight (timeMesh Λ)) (Π j F) (source_heat Y H V Q Qc j false (C j) F) (ν)
local notation "S"=> worldShelf Y H V Q Qc C j χ F
local notation "Ω"=> terse Y H V Q Qc C j χ F w
local notation "V₁"=> (daylight (timeMesh Λ))
local notation "μ"=> source_heat Y H V Q Qc j false (C j) F
local notation "λ₀"=> Alliance.Arden ζ
local notation "Γ"=> MeshClock.marks (timeMesh Λ)
include V Q Qc C F
lemma owns_vista : Follows V₀ w:= source_floor Y H V Q Qc j false (C j) F
lemma powder (i:Β):S (i,0)=Germ.Alliance.bead V₀ (ν i):= Alliance.home .. -- ambiguous
lemma plants(i:Β): S (i,0) Ω=d (ν i w):= by
 have hp:= follows_mem V₀ _ (owns_vista Y H V Q Qc C j χ F); exact (congrArg (fun l:(Φ).Op=>l Ω) (powder Y H V Q Qc C j χ F i)).trans (beadU _ _ _ hp)
lemma powders (i:Β): S (Actress.Label.rev Y H j false i,0)= star (S (i,0)):=by
 let p:=(powder Y H V Q Qc C j χ F); let i':= i.rev Y H j false; let T':=V₀; exact (p i').trans ((congrArg (bead T') (Actress.Label.rest Y H V Q Qc j false (C j) F i)).trans ((Alliance.bead_star T' _).trans (congrArg star (p i).symm)))
-- localization for mesh p. later physical reservation. test scales by 2. labels for arbitrary shifts in Mark support.Cl.
omit V Q Qc C F in
private lemma giveG (M:Mesh)(z:marks M)(P:marks M→Prop)(h:∀ s i,P (notch M s i)):P z:=by obtain ⟨s,i,rfl⟩:= notch_exists M z; exact h ..
lemma travelC (i:Β)(v: Trans j)(z:Γ) : ∃ f': Β,S (i,aSpot v z)=S (f',0):=by
 refine giveG Y₀ z (fun z=> ∃ f': Β,S (i,aSpot v z)=S (f',0)) ?_; intro s k; let d₀:= notch Y₀ s k; obtain ⟨f',p⟩:= Actress.movesF Y H V Q Qc j false (C j) F i s v (2*k) (max s i.count) (le_max_left ..) (le_max_right ..); refine ⟨f',Alliance.balconyP V₀ V₁ ξ μ ν v d₀ i f' ?_⟩; change (U₀ v) d₀ *_=_* _; exact (source_z Y H V Q Qc j false (C j) F v s k).symm ▸ p -- maybe field not C
lemma utopia (v:LoneVac Y H V Q Qc j false (C j) F): Urbana ζ Ω S λ₀:=by
 let Pℓ:= V₀; let T':= μ; let Y':= Actress.podium Y H V Q Qc j false (C j) F; refine Alliance.stationCity Pℓ V₁ ξ T' (w) ν ?_ (vacuum_norm Y H V Q Qc j false (C j) F) Y' (owns_vista Y H V Q Qc C j χ F) fun x t p=>?_; · exact Actress.fix_ground Y H V Q Qc j false (C j) F -- maybe usage
 have hw:x∈ bottom Y H V Q Qc j false (C j) F:= (Diary.staves Y H V Q Qc j false (C j) F x).mpr ⟨p,fun s a i=> (source_z Y H V Q Qc j false (C j) F a s i) ▸ t a (notch Y₀ s i)⟩; exact Submodule.mem_span_singleton.mp (v ▸ hw)
lemma wHeat : Ω∈ (ζ).ground:= Alliance.follows_heat V₀ V₁ ξ μ (w) (owns_vista Y H V Q Qc C j χ F) (Actress.fix_ground Y H V Q Qc j false (C j) F)
lemma constellation (i:Β)(f: OS.Cross j): Vista ζ f (S (i,0))= S (i,f):=by
 have ht: Vista ζ f (S (i,0))= S (i,f+0):= risen V₀ V₁ ξ μ ν f (i,(0:OS.Cross j)); exact ht.trans (congrArg (fun t=> S (i,t)) (add_zero f)) -- tune
end Summer
end YM.CF.Buffered.Afterglow.Tower.Selection
open YM.CF.Buffered.Afterglow.Tower.Selection.Summer
#print axioms plants
#print axioms wHeat
#print axioms travelC
#print axioms powders
#print axioms utopia
#print axioms constellation
#check @utopia
