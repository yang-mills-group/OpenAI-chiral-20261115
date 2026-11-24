import YM.SU5.Selected.Landing
/-! # Exact estimation of narrowOrt products and of arbitrary Compass chart via smearing (iterated). -/
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
open Germ SelectionAnalysis Sunbelt
local notation "Ξ"=> mainsea Y H V Q Qt j strict C f
local notation "δ"=> daylight Μ
local notation "K₀"=> saunters Y H V Q Qt j strict C f
local notation "L"=> fort Y H V Q Qt j strict C f
local notation "P₀"=> (K₀).orthogonalProjectionOnto
local notation "π" => (S).stackS (look j)
local notation "W" m:max n:max => Rides.first Μ (S) (look j) m n
local notation "Z" m:max => Rides.camp Μ (S) (look j) m
local notation "ρ"=> procession Y H V Q Qt j strict C f
local notation "𝕋" p:max=> narrowOrt Y H V Q Qt j strict C f p
local notation "Ωc"=> vocation Y H V Q Qt j strict C f

noncomputable def meander (t:List (Trans j))(n l:ℕ): driveAlgebra Y H V Q Qt j strict C:= t.foldr (fun i p => (Average.center (fun a: Fin (L₀^l)=> Σ₁ i (notch Μ (n+l) a.val)))*p) 1
-- acts of actual slab-drive, all components of this average representative have exact same positive spatial displacement costs (balls, no passage of continuous shifts yet).
lemma meanders (t:List (Trans j)) (n l:ℕ): Π (meander Y H V Q Qt j strict C t n l)= Rides.first Μ (S) t n l:= by
 induction t with
 | nil=> rw [show meander _ _ _ _ _ _ _ _ ([]:List (Trans j)) _ _= _ from (show meander Y H V Q Qt j strict C [] n l= 1 from rfl), map_one]; rfl
 | cons i t ih=>
    rw [show meander Y H V Q Qt j strict C (i::t) n l=(Average.center (fun a: Fin (L₀^l)=> Σ₁ i (notch Μ (n+l) a.val)))*meander Y H V Q Qt j strict C t n l from rfl,map_mul,ih]; change ((Π (Average.center (fun a: Fin (L₀^l)=> Σ₁ i (notch Μ (n+l) a.val)))).comp _) = _; rw [Rides.first_step]; unfold Average.center; rw [map_smul,map_sum]; rfl
local notation "M₀" m:max n:max=> meander Y H V Q Qt j strict C (look j) m n
private lemma narrow_cost (x : 𝔅)(u : L) : ‖((𝕋 x) u)‖ ≤ ‖x‖*‖u‖:= by
 change ‖P₀ ((Π x) u.val)‖≤ _; refine (Submodule.norm_orthogonalProjectionOnto_apply_le _ _).trans ((ContinuousLinearMap.le_opNorm ..).trans ?_)
 exact mul_le_mul_of_nonneg_right (show ‖Π x‖ ≤ ‖x‖ from NonUnitalStarAlgHom.norm_apply_le _ _) (norm_nonneg _)
-- full product compression PH. define corresponding words and establish. In particular for x∈B=Entry.
noncomputable def labored (t:List (driveAlgebra Y H V Q Qt j strict C))(m n:ℕ) := (t.map fun x=> (M₀ m n)*x).prod -- insert before EVERY operator including first
noncomputable def went (t:List (driveAlgebra Y H V Q Qt j strict C))(m:ℕ) := (t.map fun x=> Z m * (Π x)).prod
noncomputable def paidRanks (t:List (driveAlgebra Y H V Q Qt j strict C)) := (t.map (fun x=> 𝕋 x)).prod
local notation "J" p:max m:max n:max=> labored Y H V Q Qt j strict C p m n
local notation "O" p:max m:max=> went Y H V Q Qt j strict C f p m
local notation "Ψ" p:max=> paidRanks Y H V Q Qt j strict C f p
lemma earned_ranks (p:List (driveAlgebra Y H V Q Qt j strict C))(x:L)(m:ℕ) : Tendsto (fun n=>(Π (J p m n)) (x.val:Ρ)) atTop (𝓝 ((O p m) (x.val:Ρ))) := by
 induction p with
 | nil=> change Tendsto (fun n=>(Π 1) _) _ (𝓝 _); rw [map_one]; exact tendsto_const_nhds
 | cons i t ih=>
    simp only [labored, went, List.map_cons,List.prod_cons, map_mul]; simp_rw [ContinuousLinearMap.mul_apply,meanders]
    apply Rides.motion (fun n=> W m n) _ (fun i _=>Rides.first_cost ..) (((Π i).continuous.tendsto _).comp ih); exact Rides.consec ..
lemma rank_ticket (p:List (driveAlgebra Y H V Q Qt j strict C))(x:L) : Tendsto (fun m=>(O p m) (x.val:Ρ)) atTop (𝓝 ((((Ψ p) x : K₀).val) : Ρ)) := by
 induction p with
 | nil=> exact tendsto_const_nhds
 | cons i t ih=>
    simp only [went, paidRanks, List.map_cons,List.prod_cons]; simp only [ContinuousLinearMap.mul_apply];
    let z:L:= (Ψ t) x; let y:Ρ:= (Π i) z.val
    change Tendsto _ _ (𝓝 ((P₀ y).val:Ρ)); rw [show (P₀ y).val=(S).stackS (look j) y from ?_]; swap; · rw [stack_projection]; rfl
    apply Rides.motion (fun i=> Z i) _ (fun i _=> Rides.camp_cost ..) (((Π i).continuous.tendsto (z.val:Ρ)).comp ih); exact Rides.onwards ..
-- equality of scalar regularized limit and actual SHELL glyph products determined in comp H
lemma ranks_contract (p:List (driveAlgebra Y H V Q Qt j strict C)) : ∃ g: ℕ→ℂ,(∀ s, Tendsto (fun t:ℕ=>atCharacter Y H V Q Qt j strict C f (J p s t)) atTop (𝓝 (g s))) ∧ Tendsto g atTop (𝓝 (inner ℂ Ωc ((Ψ p) Ωc))) := by
 refine ⟨fun s=>inner ℂ (Ωc).val ((O p s) (Ωc).val),fun s=>?_, ?_⟩
 · have he t: Φ (J p s t)=inner ℂ (Ωc).val ((Π (J p s t)) (Ωc).val) := by rw [vocate, ← arrive_vec,arrive_mean]
   simp_rw [he] -- wrong direction
   exact (tendsto_const_nhds (x:=(Ωc).val)).inner (earned_ranks Y H V Q Qt j strict C f p Ωc s)
 exact (tendsto_const_nhds (x:=(Ωc).val)).inner (rank_ticket Y H V Q Qt j strict C f p Ωc)

-- at a chart question even where no regularity claimed for raw, projects to curtain via purchasing the scene with such offsets on just the second point of a chart
-- to state as EXACT average of raw, note Average.points Fin(... ) ^ Trans. define iter law
lemma transferred (v : placement Λ) (x y:Tower.Field Y H s j 0 strict) :
    ∃ e:ℕ→ℂ, (∀ r, Tendsto (fun t=> inner ℂ (a₀ s x) (atEstate Y H V Q Qt j strict C f v ((Π (M₀ r t)) (a₀ s y)))) atTop (𝓝 (e r))) ∧ Tendsto e atTop (𝓝 (scene Y H V s Q Qt j strict C f x y (fun i=> (v i:ℝ)))) := by
 let L' := (innerSL ℂ (a₀ s x)).comp (atEstate Y H V Q Qt j strict C f v)
 refine ⟨fun i=> L' ((Z i) (a₀ s y)),fun i=>?_,?_⟩
 · simp_rw [meanders]; exact L'.continuous.continuousAt.tendsto.comp (Rides.consec Μ (S) (look j) (a₀ s y) i)
 rw [scene_on_mesh]; exact L'.continuous.continuousAt.tendsto.comp (Rides.onwards Μ (S) (look j) (a₀ s y))
end YM.CF.Buffered.Afterglow.Tower.Selected
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.transferred
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.ranks_contract
