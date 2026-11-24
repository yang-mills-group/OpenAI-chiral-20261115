import YM.CF.Chaff.Aff
import YM.CF.Vale.Sail
import YM.CF.Fief.Vex
import YM.CF.Hype.Ace
import YM.CF.Ione.Mesh
import YM.CF.Fief.Lucid
import YM.CF.Char.Gel
import YM.Next.STATIONARY.Joint.OnShell
import YM.CF.Rill.Pott
import YM.CF.Skye.Hark
import YM.CF.Prism.Pecu
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 450000
noncomputable section
namespace YM.CF.Chaff
open Function NormedSpace Filter Metric Finset Lattice MeasureTheory RG
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Kronecker
open Pressure
open Cube Lat Tenant Tulip Gully Spire Scroll Scree Jet Ave Skye Gas Pastry Dial Fock
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m B N: Side}{a e K H C:ℝ}{n:ℕ}
local notation "Λ" => CSide m B
local notation "ξ"=> Domain m B
local notation "G"=>SU.group
open Phase Branch
variable {D:Ave.Briar m B e→ Scree.Cipher (CSide m B)}{S:Stamp m B}
variable (p:0≤e)(h:Inscribed K e n S H D C)
local notation "Γ"=> tangD Λ
variable {s:ℝ}{R:Scree.Loom (CSide m B)}{P:BudgetPoint}{c:ℕ}(A:Roof (CSide m B) a s c R)(pH: P.threshold ≤ a)(v:s < e)(l:c≤P.B)
open MultiNext.SignedSource
variable (o:Seat (CSide m B))(y:o∈S) 
variable {r Y V x μ b θ C' ρ:ℝ}
open Gloss Maize Ione Salt Hive Vow
open Hom Vale Vale.Grace Kea Nova RP RP.Str Spark
open Wilson Precision Next.Free Gauge Paige Vault Brace
variable {L:Patch}{Z:Teller SU.group}{W:ChartRatio SU.group}{N0:Postal}(D':Grace Z L W){X:Grasp D'.U B e}{R':Scree.Loom (CSide m B)}{k:ℕ}{u:ℝ}
section point
variable (f:Scroll m B (Brace.northZ m B))(I:RegBudget (CSide m B))
abbrev LabelB(m B:Side): Sweep (CSide m B)→ Prop:=fun s=> s∈ Set.range (netB m B)
local notation "ᵀ"=> northZ m B
local notation "IR" I s x=> fulvia I s (Vale.launch D'.L x P (CSide m B))
-- uses explicit X
structure Lives_B (t v:ℝ)(P:BudgetPoint)(R:Loom (CSide m B))(X:Grasp D'.U B e)(s':ℝ):Prop where
 weight: IncX (LabelB m B) I P H v
 eyes:∀ (β:ℝ)(i:Orbit Λ),Rue.FleetS P.threshold i.1 →∀ T:FC (Single Λ), inner ℂ (mateK Λ) (acts T (denZ (fulvia I s' (Vale.launch D'.L β P (CSide m B))) X R i)) =∫ z, hoistF Z.top.clip P.threshold β f e 0 t 1 (northZ m B) (fun _=>Spark.crossL (helix _).symm T) (i.1,z)∂rains m -- note P notation old 
variable (pX:X.roundZ ≤ (CSide m B).val)(hy:Z.top.clip.direct≤1)
include A p v pH pX hy l
lemma livesB(t:ℝ)(W:Fire_ins f t X n K H x b)(T':Opera P n e x H Y K b r)(y0:4*P.B<(Domain m B).val): ∃ s:ℝ, ∃ I:RegBudget Λ,Lives_B (H:=Y) D' f I t r P R X s:=by
 obtain ⟨Ω,O,he⟩:= W.slate; obtain ⟨F,w,u,g,V,hM⟩:=O.seed; let T :=Pastry.pane (Ω (floorP m B p)); have hv:T=(↑T.re:ℂ):=by
    refine Complex.ext rfl ?_; change T.im=0; unfold T; rw [V,pane_f]; simp_rw [Complex.im_sum]; apply sum_eq_zero; intro i _; exact rama hM ..
 obtain ⟨C',r',U,θ,b',μ,h1,h2,h3,h4,h5,h6,h7,h8,h9,p1,p2,p3,p4,p5⟩:=T'.costs; let F':= MarkF p R F P; have hr:=hubCost p A pH v l u (fun i=>p4.symm ▸ g i) hM h1 h2 h3 h4 h5 h6 h7 h8 h9 p1 p2 y0 p3; have H':∀ z:Briar m B e,pingS P.threshold univ z.val→ exponentL P F' z.val= Ω z-hollow (↑T.re):=by intro z s; rw [←hv]; exact φs_A p A pH v l u h2 h1.κ s Ω V
 let s':=T.re; refine ⟨s',F',⟨p5.symm ▸ hr,?_⟩⟩; intro β i v1 Z'; rw [dusk_m D' β A pH v pX hy p F' s' _ H' i v1,map_smul,inner_smul_right]; unfold hoistF; dsimp only; rw [integral_const_mul]; let Y:=i.1
 by_cases h:Y∈ Calm G ξ P.threshold; swap; · rw [show primal Z.top.clip ξ β P.threshold i.1=0 from Set.indicator_of_notMem h _, Complex.ofReal_zero]; simp
 have hc:R i=Y:=Robes.solar i R A P pH h; have hg:Guard Y e:=hc ▸ ((A.paid _).shrink v.le); rw [claw p _ hg]; exact congrArg (fun t:ℂ=>_ * t) (he ⟨Y,hg⟩ Z').symm
end point
end YM.CF.Chaff
