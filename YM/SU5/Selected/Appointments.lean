import VerifiedSatinGroundInteraction
import YM.SU5.Selected.Plateau
/-! # Appointment of relative-position grid in each direction.
Mark resolution charts for pair Entrance↔Entrance where the two words admit
buffered tower Field positivity presentations. Compute ALL positions of the mesh group
in the joint half-charts. Cross to other-axis positive direction. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 340000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Selected
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock Set Vacancy
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
local notation "L₀" => Λ.R.L.val
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E) (s : ℕ)
variable {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b) (Qt : Clipped Y H (i ∘ a) (k ∘ b))
variable (j : Axis) (strict : Bool) (C : Arena Y H Q.circuit j 0 strict)
open TopologicalSpace OS.Ground YM.SelectionAnalysis Vacancy
variable (f : (displayAlgebra Y H V Q Qt j strict C) →⋆ₐ[ℂ] ℂ)
local notation "A" => Ark.Ht Y H Q.circuit j 0 strict C
local notation "𝔄" => displayAlgebra Y H V Q Qt j strict C
local notation "𝔅" => driveAlgebra Y H V Q Qt j strict C
local notation "ℛ" => Aurora Y H V Q j strict C
local notation "𝔙" t:max => Tower.Field Y H t j 0 strict
local notation "Ω₀" => seat0 Y H V Q j strict C
local notation "ω₀" => floorV Y H Q.circuit j 0 strict C
local notation "E₀" t:max x:max p:max => entrance Y H V t Q Qt j strict C x p
local notation "ιₜ" t:max => actor Y H t Q.circuit j 0 strict C
local notation "Φ" => atCharacter Y H V Q Qt j strict C f
local notation "Λ₀" => traveller Y H V Q Qt j strict C
local notation "Ε" t:max => response Y H V t Q Qt j strict C f
local notation "Π" B:max => procession Y H V Q Qt j strict C f B
local notation "Υ" u:max => moveMark Y H u strict
local notation "Θ" => mirrorInMarks Y H j strict
local notation "Τ" => Marks (tent Y H) strict
local notation "Μ" => timeMesh Λ
local notation "ψ" t:max n:max => heatStamp Y H V t Q Qt j strict C n
local notation "Σ₁" u:max d:max => shiftStamp Y H V Q Qt j strict C u d
local notation "θt" s:max i:max=> MeshClock.whenly (timeMesh Λ) s i
local notation "Ρ" => indoor Y H V Q Qt j strict C f
local notation "Ω" => doorstep Y H V Q Qt j strict C f
local notation "Oa" => arrive Y H V Q Qt j strict C f
local notation "a₀" t:max x:max => bud Y H V t Q Qt j strict C f x
local notation "M₁" t:max => futureMark Y H t j strict
local notation "S"=> turnstile Y H V Q Qt j strict C f
local notation "R" => ride Y H V Q Qt j strict C f
local notation "P" k:max => (S).crew k
local notation "T" => look j
abbrev placement (Λ : Preparation) := Axis → marks (timeMesh Λ)
-- recall `gaugePosition` physical scale; Lean Test above uses **Φ** at every point; no broad-only morphological assumptions
abbrev uptown (j : Axis) (u : placement Λ) := 0 ≤ (u j:ℝ)
local notation "λ₀" u:max => fun k : Trans j => u k.val
local notation "γ" z:max => show ℝ≥0 from Real.toNNReal ((z : marks Μ):ℝ)
noncomputable def atEstate (u : placement Λ) : (indoor Y H V Q Qt j strict C f).Op :=
  ((R).E (γ (u j))).comp ((S).raw (look j) (λ₀ u))

noncomputable def relocateWorld (v : Cover) (p : Marks (tent Y H) strict) : Marks (tent Y H) strict :=
  ordinate.foldr (fun i q=> moveMark Y H i strict (v i) q) p
lemma world_val (v : Cover) (p : Marks (tent Y H) strict) : (relocateWorld Y H strict v p).val = Vacancy.chart (tent Y H) v p.val := by
  unfold relocateWorld Vacancy.chart; generalize ordinate=A'
  induction A' with
  | nil=>rfl
  | cons i l' ih=> rw [List.foldr_cons,cad_step]; exact congrArg (relocate K i (v i)) ih
lemma world_still (v : Cover) (p : Marks (tent Y H) strict) : (Ε s) (relocateWorld Y H strict v p)=(Ε s) p := by
  unfold relocateWorld; generalize ordinate=A'
  induction A' with
  | nil=>rfl
  | cons i l ih=> rw [List.foldr_cons,all_waiting,ih]
lemma world_seed (p : Marks (tent Y H) strict) : relocateWorld Y H strict 0 p=p := Subtype.ext ((world_val Y H strict 0 p).trans (cad_zero K _ (marksSpec strict p).1)) -- arg tune
lemma world_held (v w : Cover) (p : Marks (tent Y H) strict) : relocateWorld Y H strict v (relocateWorld Y H strict w p)=relocateWorld Y H strict (v+w) p := by
  apply Subtype.ext; rw [world_val,world_val,world_val]; exact cad_plus _ _ (marksSpec strict p).1 ..

local notation "V₁" k:max=> Vacancy.transport Y H s j strict (look j) k
lemma roving (t : List (Trans j)) (x : 𝔙 s) (y : Trans j→ℤ) :
    (S).raw t (fun k=> notch Μ s (y k)) (a₀ s x)=a₀ s (Vacancy.transport Y H s j strict t y x) := by
  induction t with
  | nil=>rfl
  | cons i t ih=>
    rw [Germ.Alliance.raw_step,ContinuousLinearMap.comp_apply,ih,turnstile_in]; rfl
lemma apt_rides (x : 𝔙 s) (p : Cover) (v : ℕ) (h : (v:ℤ)=p j) :
    atEstate Y H V Q Qt j strict C f (fun k=> notch Μ s (p k)) (a₀ s x)=
      a₀ s (tick Y H s j 0 strict (2*v) ((V₁ (fun k : Trans j=> p k.val)) x)) := by
  unfold atEstate; rw [ContinuousLinearMap.comp_apply, roving]
  have he : Real.toNNReal (bell Μ s (p j))= θt s v:=by rw [←h, natural_time]; exact Real.toNNReal_coe -- Real.toNNReal_coe
  rw [show Real.toNNReal (↑(notch Μ s (p j)) : ℝ)= _ from he,ride_ticks]
include V C in
lemma aptMoves (x : 𝔙 s) (p : Cover) (v : ℕ) (h : (v:ℤ)=p j) :
    ((M₁ s) (tick Y H s j 0 strict (2*v) ((V₁ (fun k : Trans j=> p k.val)) x))) = relocateWorld Y H strict p ((M₁ s) x) := by
  apply Subtype.ext; rw [world_val,future_val,future_val,timed_apply,transverseT Y H V s Q j strict C]
  rw [chart_piece _ j _ (field_test Y H s j 0 strict x),h,transverse_eq _ j (look j) p (fun i=> p i.val) (fun _=>rfl)] -- includes V C

def Visits (x y : Tower.Field Y H s j 0 strict) (u : placement Λ) : ℂ :=
    inner ℂ (a₀ s x) (atEstate Y H V Q Qt j strict C f u (a₀ s y))
local notation "Z" t:max=> Visits Y H V t Q Qt j strict C f
lemma estate_moves (x y : 𝔙 s) (u : placement Λ) (p : uptown j u) (v: Cover) (h : ∀ k:Axis, notch Μ s (v k)=u k) :
    (Z s) x y u=(Ε s) (Θ ((M₁ s) x)*relocateWorld Y H strict v ((M₁ s) y)):= by
  let n := (v j).toNat; have ht : 0≤ v j := (bell_le Μ s 0 (v j)).1 (by
    have hp : 0 ≤ (notch Μ s (v j):ℝ):=(h j).symm ▸ p; change 0 ≤ bell Μ s (v j) at hp; simpa [bell] using hp)
  unfold Visits; rw [← funext h,apt_rides Y H V s Q Qt j strict C f y v n (Int.toNat_of_nonneg ht),earns,aptMoves Y H V s Q j strict C y v n (Int.toNat_of_nonneg ht)] -- tune

def upGrade (F : Marks (tent Y H) strict) (t : ℕ) : Marks (tent Y H) strict := upward Y H Q strict F s (t-s)
lemma marches {F : Marks (tent Y H) strict} {t : ℕ}: upGrade Y H s Q strict ((Θ) F) t= Θ (upGrade Y H s Q strict F t) := by
  apply Subtype.ext; change stream Y H D _ _ (mirror K j 0 F.val)=mirror _ _ 0 _; rw [stream_flipped Y H Q.circuit s (t-s) j 0 (marksSpec strict F).1, mul_zero]; rfl
lemma necklace (u : placement Λ) : ∃ (t:ℕ), s ≤ t ∧ ∃ x : Cover,∀ k,notch Μ t (x k)=u k := by
  choose n x hx using (fun k=> notch_exists Μ (u k))
  let t:=s+Finset.univ.sup n
  refine ⟨t,by unfold t; omega,fun i=>castor Μ (n i) t (x i), fun i=>?_⟩
  rw [notch_up, hx]; exact le_trans (Finset.le_sup (f:=n) (Finset.mem_univ i)) (by unfold t; omega)
lemma visits_higher (x y : 𝔙 s) (u : placement Λ) (p : uptown j u) (t:ℕ) (h:s≤t) (v:Cover)(l:∀ k,notch Μ t (v k)=u k) :
    (Z s) x y u=(Ε t) ((upGrade Y H s Q strict (Θ ((M₁ s) x)) t)* relocateWorld Y H strict v (upGrade Y H s Q strict ((M₁ s) y) t)) := by
  rw [marches];
  let I := fun f : (𝔙 s)=> Raise Y H Q.circuit j 0 strict s t h f;
  have Hu(x:𝔙 s) : upGrade Y H s Q strict ((M₁ s) x) t=(M₁ t) (I x) := rfl
  rw [Hu x,Hu y]; rw [← estate_moves Y H V t Q Qt j strict C f (I x) (I y) u p v l]
  unfold Visits I; rw [flourishes,flourishes]

variable {j' : Axis} (C' : Arena Y H Q.circuit j' 0 strict) (f' : (displayAlgebra Y H V Q Qt j' strict C') →⋆ₐ[ℂ] ℂ)
variable (x y : Tower.Field Y H s j 0 strict) (x' y' : Tower.Field Y H s j' 0 strict)
/-- Require actual equality of **responses** (can use displacement buying in same Panel), allow
both directions. -/
def Duality : Prop :=
  (∀ (x : Marks (tent Y H) strict) (t : ℕ), response Y H V t Q Qt j strict C f x=response Y H V t Q Qt j' strict C' f' x) ∧
  mirror (tent Y H) j 0 x.val=mirror (tent Y H) j' 0 x'.val ∧
  y.val = y'.val
lemma Duality.turn (v : Duality Y H V s Q Qt j strict C f C' f' x y x' y') : Duality Y H V s Q Qt j' strict C' f' C f x' y' x y:= ⟨fun x t=> (v.1 x t).symm,v.2.1.symm,v.2.2.symm⟩
lemma Duality.compare (v : Duality Y H V s Q Qt j strict C f C' f' x y x' y') (u : placement Λ) (p:uptown j u)(l:uptown j' u): (Z s) x y u=Visits Y H V s Q Qt j' strict C' f' x' y' u:= by
 obtain ⟨t,ts,i,e⟩:= necklace s u
 rw [visits_higher Y H V s Q Qt j strict C f x y u p t ts i e,visits_higher Y H V s Q Qt j' strict C' f' x' y' u l t ts i e,(show mirrorInMarks Y H j strict ((M₁ s) x)= mirrorInMarks Y H j' strict (futureMark Y H s j' strict x') from Subtype.ext v.2.1),(show futureMark Y H s j strict y=futureMark Y H s j' strict y' from Subtype.ext v.2.2),v.1]
end YM.CF.Buffered.Afterglow.Tower.Selected
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.Duality.compare
