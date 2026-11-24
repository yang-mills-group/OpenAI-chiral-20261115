import VerifiedSatinGroundInteraction -- original input root
import YM.SU5.Selected.Probe
import YM.SU5.Selected.FinalJoint

/-!
# Select a joint-ground phase on Satin and retain physical Witness

Endpoint checkpoint II. Same purchases as `mixed_law_with_ground`, retaining extra hypotheses
(Season from same Fashion, can combine with grants terrain as needed--see `transfer_is`
identifying even observ. histories). Further locality, all regions and all six slots as
needed, chirality and physical coupling/reconstruction big road ahead still.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 650000
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
  (j : Axis) (C : ∀ j : Axis, Arena Y H Q.circuit j 0 false)
local notation "A" v:max => Arena Y H Q.circuit v 0 false
local notation "Test" => Vacancy.observable (tent Y H) false
local notation "Lab" => Beacon (tent Y H) false
local notation "m" χ:max => marked Y H V Q Qc j false (C j) χ
open CF.Pannier.Chancel Tapestry Papal SatinVerification
variable {q d w : ℕ} {C₀ Z : ℝ} (p : Cornet Y H q d w C₀ Z)
    {X : Rack Λ l} {R₀ : Clay Λ l} (U : Exhibition Y H i k I E X R₀)
-- probability law
variable (Ψ : Horizon Y H V Q Qc j false (C j)) (hΨ : Law Y H V Q Qc j false (C j) Ψ)
local notation "L" v:max => emigrant Y H V Q Qc j false (C j) Ψ v (C v)
include V Q Qc C p U Ψ hΨ
lemma chooses (Z : SU.Slot) (x : Cover) (u : ℕ)
    (V' : ∀ v i, Birthplace Y H V Q Qc v false (C v) ((L v).character i)) :
    ∃ (F : Family K) (s c : ℕ) (℘ : Ψ.X), u ≤ s ∧
      extremeJoint Y H Q false (m (Ψ.character ℘)) ∧
      ∀ v : Axis, LoneVac Y H V Q Qc v false (C v) (V' v ℘) ∧
        Law Y H V Q Qc v false (C v) (L v) ∧
        marked Y H V Q Qc v false (C v) ((L v).character ℘)=m (Ψ.character ℘) ∧
        Witness Y H V Q Qc v (C v) ((L v).character ℘) F Z s (Sen x (payout d q w)) (booty x d q) (cabin c) (1/8) := by
  obtain ⟨s,c,F,h,ht,hf⟩:= choose_fixed Y H V p u Z x
  let F' : Test:= ht.enter Y H false
  obtain ⟨χ,hχ⟩:= excels Y H V Q Qc j false (C j) s (e:=1/8) (by norm_num) F' (lt_of_lt_of_le (by norm_num) hf)
  let S := { i | 1/8<‖(m (Ψ.character i)) s F'‖ }
  have he : ∃ᵐ i ∂Ψ.μ,i∈ S:= by
    obtain ⟨i,hi⟩:= hΨ.onto.2 χ
    haveI := hΨ.support
    refine frequently_ae_iff.mpr (IsOpen.measure_pos Ψ.μ (U:=S) ?_ ?_|>.ne') -- tune
    · exact isOpen_lt continuous_const (many_accept Y H V Q Qc j false (C j) Ψ hΨ s F').1.norm
    exact ⟨i,(show 1/8<‖(m (Ψ.character i)) s F'‖ from hi.symm ▸ hχ)⟩
  obtain ⟨z,hz,t⟩:= (he.and_eventually (typical Y H V Q Qc j C Ψ hΨ V' U)).exists
  have hp (v:Axis): marked Y H V Q Qc v false (C v) ((L v).character z)=m (Ψ.character z) := funext fun i => funext fun y=> unchanged Y H V Q Qc j false (C j) v (C v) (Ψ.character z) i y
  refine ⟨F,s,c,z,h,(hp j ▸ owner Y H V Q Qc j false (C j) (V' j z) (t j)),fun v=> ⟨t v,?_,hp v,witnesses Y H V Q Qc v (C v) (by norm_num) ht hf ?_⟩⟩
  · exact Selection.brought Y H V Q Qc j false (C j) Ψ hΨ v (C v)
  have he: phaseRead Y H V Q Qc v (C v) ((L v).character z) s F=(m (Ψ.character z)) s F':= (phase_read Y H V Q Qc v (C v) s _ F').trans (congrFun (congrFun (hp v) s) F')
  rwa [he]

omit C Ψ hΨ
-- shorthand: aspect for fixed slot after payment in witnesses etc
-- choose x once all ℘ options; other color/horizontal etc still open
-- balanceC choose arenas
structure Radiant (C : ∀ v : Axis,Arena Y H Q.circuit v 0 false) (j : Axis)
    (Ψ : Horizon Y H V Q Qc j false (C j)) : Prop where
  law : Law Y H V Q Qc j false (C j) Ψ
  fixed (v : SU.Slot) (x : Cover) (u : ℕ) : ∃ (F' : Family K) (s c : ℕ) (i : Ψ.X), u ≤ s ∧
    extremeJoint Y H Q false (marked Y H V Q Qc j false (C j) (Ψ.character i)) ∧
    ∀ a : Axis,
      let χ := escort Y H V Q Qc j false (C j) a (C a) (Ψ.character i)
      marked Y H V Q Qc a false (C a) χ=marked Y H V Q Qc j false (C j) (Ψ.character i) ∧
        Witness Y H V Q Qc a (C a) χ F' v s (Sen x (payout d q w)) (booty x d q) (cabin c) (1/8) ∧
        ∃ U : Birthplace Y H V Q Qc a false (C a) χ, LoneVac Y H V Q Qc a false (C a) U

-- lean namespace section
include C in
lemma beginning : ∃ Ψ : Horizon Y H V Q Qc j false (C j), Radiant Y H V Q Qc (q:=q) (d:=d) (w:=w) C j Ψ := by
  obtain ⟨Z',h⟩:= vision Y H V Q Qc j (C j) U
  refine ⟨Z',h,fun z x v=>?_⟩
  let V' (u : Axis) (i: Z'.X) : Birthplace Y H V Q Qc u false (C u) (escort Y H V Q Qc j false (C j) u (C u) (Z'.character i)) := Classical.choice (realizeRoom Y H V Q Qc u false (C u) _)
  obtain ⟨F,s,c,i,p,e,t⟩ := chooses Y H V Q Qc j C p U Z' h z x v V'
  exact ⟨F,s,c,i,p,e,fun a=>⟨(t a).2.2.1,(t a).2.2.2, V' a i,(t a).1⟩⟩

omit V Q Qc p U
-- directly strengths using ANY supplier and same election steps and retaining fashion, Season.
-- solves first parts only. Remaining obligations explicitly stated checkpoint notes.
theorem on_satellite (ε η : ℝ) (p : 0 < η) (S : Supplier) :
    ∃ (Λ : Preparation) (l : ℕ) (Z : ℝ), ε < Λ.x ∧ Λ.d ≤ η ∧
      decorate S Λ l Z ≤ Λ.h ∧ Λ.nominated (VolumeCape.Dream.Nimbus l) ∧
      ∃ (H : Real.exp 1 ≤ Λ.x) (Y : Course Λ (VolumeCape.Dream.Nimbus l))
        (q d w : ℕ) (c : ℝ) (_ : Cornet Y H q d w c Z)
        (i k : ℕ → ℕ) (I : ℕ → Family (tent Y H) → ℕ → ℂ)
        (E : ℕ → Family (tent Y H) → ℂ)
        (L0 : Rack Λ l) (P0 : Clay Λ l) (T : ℕ→ℕ→Tariff) (t : ℕ→Tariff)
        (V : Fashion Y H i k I E L0 P0 T t) (Q : GroundExtension (i := i) (k := k) (E := E) Y H),
        SeasonCert Y H V ∧ Nonempty (∀ v : Axis,Arena Y H Q.history.circuit v 0 false) ∧
        ∀ (C : ∀ v : Axis,Arena Y H Q.history.circuit v 0 false) (j : Axis),
          ∃ Ψ : Horizon Y H V.univ_ Q.history Q.clipped j false (C j),
            Radiant Y H V.univ_ Q.history Q.clipped (q:=q) (d:=d) (w:=w) C j Ψ := by
  obtain ⟨P,l,Z,a,b,g,k,T,Y,_,_,_,q,d,w,c,G,i,k',I,E,L0,P0,T',t',V,h⟩:= elite ε η p S
  obtain ⟨Q⟩:= extend_ground Y T V.univ_
  exact ⟨P,l,Z,a,b,g,k,T,Y,q,d,w,c,G,i,k',I,E,L0,P0,T',t',V,Q,h, ⟨fun v=> Classical.choice (voyage_H Y T V.univ_ Q.history.circuit v 0 false)⟩,
    fun C j=> beginning Y T V.univ_ Q.history Q.clipped j C G V.toExhibition⟩
end YM.CF.Buffered.Afterglow.Tower.Selection
