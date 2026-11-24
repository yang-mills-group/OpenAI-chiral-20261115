import YM.SU5.Selected.Prag.Book
import YM.SU5.Macro.Edge

/-!
# Extrapolate! Prove an actual spatial-analytic strip (for this correlation and geometry)

At fixed positive orientation and margins; this does NOT take the Atlas between
arbitrary rotated regions and does not assume or assert Lorentz spectrum.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 440000
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
namespace Relief
open _root_.YM.SatinMacro

variable (χ:CapCharacter Y H V Q Qc 3 false (C 3))
variable (F: Birthplace Y H V Q Qc j false (C j) (escort Y H V Q Qc 3 false (C 3) j (C j) χ))
open Alliance
local notation "Y₀" => timeMesh Λ
local notation "G" => marks Y₀
local notation "P" => Summer.Polaris Y H V Q Qc j false (C j) F
local notation "Λ₀" j:max => escort Y H V Q Qc 3 false (C 3) j
local notation "ξ" j:max t:max => (Diary.jetTime Y H V Q Qc j false (C j) t)
local notation "S" => skyline Y H V Q Qc C j χ F
local notation "α" => terse Y H V Q Qc C j χ F
local notation "ρ" v:max T:max s:max x:max => markedActor Y H V Q Qc v false (C v) T s x
open _root_.YM.Spectral.Alps
variable (s:ℕ)(x y:Tower.Field Y H s j 0 false)
include V Q Qc F C

/-- Each selected actor defining a Width vacuum vector already carries a
real positive amount of heat. Does not depend on analytic cores for all
operators or rotation covariance. -/
lemma padding : HasPadding (skyline Y H V Q Qc C j χ F)
    (terse Y H V Q Qc C j χ F (ρ j F s x)) := by
  obtain ⟨q,y,p⟩ := predecessor Y H s Q.circuit j 0 false x
  let t:= s+q
  have h:= Fern.Curtain.when_clock Y H V Q Qc j (C j) t F y 1
  have he : ρ j F s x=(ξ j F).E (whenly Y₀ t 1) (ρ j F t y) := by
    -- align actors (2*1 notation defeq)
    have hp := congrArg (markedActor Y H V Q Qc j false (C j) F t) p
    exact ((h.trans hp).trans (Selection.path Y H V Q Qc j false (C j) F s t (by unfold t; omega) x)).symm
  refine ⟨_, when_pos Y₀ t 1 zero_lt_one, α (ρ j F t y), ?_⟩
  exact (congrArg (terse Y H V Q Qc C j χ F) he).trans ((P).prism_early (daylight Y₀)
    (ξ j F) (source_heat Y H V Q Qc j false (C j) F) _ _)

omit V Q Qc F C
variable (v : Trans j) -- shadows earlier arbitrary
/-- Unit spatial direction (the very basis used in E4). -/
def aim : OS.Cross j := ⟨basis v.val,(show basis v.val j=0 by rw [basis_eq,if_neg v.property.symm])⟩
lemma aim_length : ‖(aim j v).val‖=1 := basis_norm v.val

variable {d:ℝ} (X Y':F.H.space) (h:∀ v:Trans j,Poem Y H V Q Qc C j χ F v.val d X Y')
local notation "κ" e:max Δ:max => SatinMacro.kernel (S) (α X) (α Y') e Δ
include V Q Qc F C X Y' h

omit V Q Qc F C X Y' h in
private lemma focus {Γ:AddSubgroup ℝ} (u : Γ) :
    pours j (fun i:Trans j=> ((if i=v then u else 0 : Γ):ℝ)) = (u:ℝ) • aim j v := by
  apply Subtype.ext; ext1 i
  change (if p:i≠j then (↑(if (⟨i,p⟩:Trans j) = v then u else 0 : Γ):ℝ) else 0)= (u:ℝ)* basis v.val i
  rw [basis_eq]; by_cases p : i≠j
  · rw [dif_pos p]; by_cases e : i = v.val
    · rw [if_pos e,if_pos (show (⟨i,p⟩:Trans j)=v from Subtype.ext e),mul_one]
    rw [if_neg e,if_neg (show (⟨i,p⟩:Trans j)≠v from fun h=>e (congrArg Subtype.val h)),mul_zero]; rfl
  rw [dif_neg p,if_neg (show i≠v.val from fun h=> p (h ▸ v.property)),mul_zero]

private lemma real_focus (p:0<d) (u : G) (e:-d < (u:ℝ)) (Δ : ℝ≥0) :
    κ ((u:ℝ) • aim j v) Δ = inner ℂ X (((P).crew v).play u ((ξ j F).E Δ Y')) := by
  let a(i:Trans j):G:= if i=v then u else 0
  have q : (P).raw (look j) a = ((P).crew v).play u:= by
     rw [(P).pointR (v:=v) u a _ (look_one j) (fun _ _=> rfl),if_pos (look_all j v)]
  have z(i:Trans j) : -d < (a i:ℝ) := by
     by_cases x:i=v; · rw [show a i=u from if_pos x]; exact e
     rw [show a i=0 from if_neg x]; exact neg_neg_of_pos p
  let KP (p: OS.Cross j):= κ p Δ
  have he : KP (pours j fun i=>(a i:ℝ))= inner ℂ X (((P).raw (look j) a) ((ξ j F).E Δ Y')):= limes Y H V Q Qc C j χ F d X Y' h a z Δ
  exact (congrArg KP (focus j v u)).symm.trans (he.trans (congrArg (fun p : F.H.Op => inner ℂ X (p ((ξ j F).E Δ Y'))) q))

/-- Extra statement for checking the same-transverse-axis prices: not just
knowing correl analytic but identify the single target on the other very axis
arena and SAME χ for real u, with that axis's true purchase. -/
theorem extrapolate (p:0 < d)
    (W : Birthplace Y H V Q Qc v.val false (C v.val) (escort Y H V Q Qc 3 false (C 3) v.val (C v.val) χ))
    (Δ : ℝ≥0) (q:Δ ∈ MeshClock.times (timeMesh Λ)) :
    ∃ (r:ℕ)(z:ℤ)(x y: Tower.Field Y H r v.val 0 false),
      d ≤ bell (timeMesh Λ) r z ∧ ∀ u:ℝ, -d < u →
       κ (u • aim j v) Δ = inner ℂ (ρ v.val W r x) ((ξ v.val W).E (Real.toNNReal (u+bell (timeMesh Λ) r z)) (ρ v.val W r y)) := by
  let t:=Y₀
  have hh:= Poem.heated Y H V Q Qc C j v.val χ F (y:=Y') (x:=X) (h v) Δ q v.property
  refine Exists.elim hh (fun r hr=> Exists.elim hr (fun k hk=> Exists.elim hk (fun m hm=> Exists.elim hm (fun x hx=> Exists.elim hx (fun y hy=> Exists.elim hy (fun A hA=> Exists.elim hA (fun B hB=>?_)))))))
  let p₀:=hB.1; let p₁:= hB.2.1; let p₂:= hB.2.2.1; have w := hB.2.2.2
  let g (u:ℝ):= inner ℂ (ρ v.val W r A) ((ξ v.val W).E ((u+bell t r m).toNNReal) (ρ v.val W r B))
  let f(u:ℝ):= κ (u • aim j v) Δ
  have hg : Continuous g:= continuous_const.inner (((ξ v.val W).continuousE _).comp
    (continuous_real_toNNReal.comp (continuous_add_const _)))
  have hf : Continuous f:= (kernel_cont_space (S) (α X) (α Y') Δ).comp (continuous_id.smul continuous_const)
  refine ⟨r,m,A,B,w,?_⟩
  have he : Set.EqOn f g (Set.Ioi (-d) ∩ (G : Set ℝ)) := by
    rintro u ⟨i,h'⟩; let E₀:G:= ⟨u,h'⟩
    have hp:-d<u:=i
    let U':= ((P).crew v).play E₀
    exact (real_focus Y H V Q Qc C j χ F v X Y' h p E₀ hp Δ).trans
      ((congrArg₂ (inner ℂ) p₁ (congrArg U' p₂)).trans
        (Refracts.BellCross Y H V Q Qc C j v.val r χ v.property F W p₀ E₀ (show 0 ≤ u+bell (timeMesh Λ) r m by linarith only [hp,w])))
  exact fun u hp=> he.closure hf hg ((daylight t).open_subset_closure_inter isOpen_Ioi (show u∈ Set.Ioi (-d) from hp))

lemma analyt_h (p:0<d)(Δ:ℝ≥0)(q:Δ∈MeshClock.times (timeMesh Λ)) :
    AnalyticOnNhd ℝ (fun (u:ℝ)=> κ (u • aim j v) Δ) (Set.Ioi (-d)) := by
  let W:= Classical.choice (realizeRoom Y H V Q Qc v.val false (C v.val) ((Λ₀ v.val) (C v.val) χ))
  obtain ⟨r,z,a,b,e,m⟩:= extrapolate Y H V Q Qc C j χ F v X Y' h p W Δ q
  intro u x
  let d':= bell (timeMesh Λ) r z
  let Z₀:= ξ v.val W; let P':= ρ v.val W r a; let J:= ρ v.val W r b
  refine (real_analytic_shift Z₀ P' J 0 d' u (lt_of_le_of_lt (neg_le_neg e) (show _<_ from x))).congr ?_
  filter_upwards [(isOpen_Ioi.mem_nhds x)] with i t
  let v':=(i+d').toNNReal
  have hz:= (DFunLike.congr_fun Z₀.uZero (Z₀.E v' J))
  exact (congrArg (inner ℂ P') hz).trans (m i t).symm
end Relief
end Summer
end YM.CF.Buffered.Afterglow.Tower.Selection
open YM.CF.Buffered.Afterglow.Tower.Selection.Summer.Relief
#print axioms padding
#print axioms analyt_h
