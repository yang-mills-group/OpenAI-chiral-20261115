import YM.CF.Iva.Brio
import YM.CF.Pastry.Bliss
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Iva
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Lich Corne
open Lich.Muster
attribute [local instance] opCStarAlgebra
variable {E: Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]{x:E} {k:ℕ}
variable{n:Type*}[LinearOrder n][Fintype n]
local notation "Z₀"=> LeanV n
abbrev naked(d:ℝ):Raid n:= Pi.single ∅ d
abbrev ank(H:Finset n)(d:ℝ):Raid n:= Pi.single H d
open Rue Font
abbrev steel(k:ℕ)(D:ℝ):= (k+1:ℝ)*D
abbrev pinT(i j:n):Finset (LeanV n):={(true,i)}∪ {(false,j)}
abbrev thumb(k:ℕ)(H:Toll n):Raid (LeanV n):=∑ i:n,∑ j:n, ank (pinT i j) (steel k (H i j))
abbrev cull(k:ℕ)(V:Toll n)(d:ℝ):Raid (LeanV n):= naked (steel k d)+thumb k V
lemma peels{V:E→ℂ}{b:ℝ}(p:Allows k V x b):Rigid (n:=n) (Pastry.hollow ∘ V) k x (naked (steel k b)):= (Woody.chit ∅ (bare_p V b p)).germ (Eventually.of_forall fun x=>by simp [Pastry.hollow,poke,Poly.tag_void]) -- infer song
lemma elect(i j:n){v:E→ℂ}{b:ℝ}(p:Allows k v x b) : Woody k (fun t=>v t • (wire true i*wire false j)) x (ank (pinT i j) (steel k b)):=by
 let A:Finset (LeanV n):={(true,i)}; let B:Finset (LeanV n):={(false,j)}; let q:= Poly.sail A B; have hp:Disjoint A B:=disjoint_left.mpr fun x u t=>by simp only [A,B,mem_singleton] at *; subst x; simp at t -- use specific
 apply ((Woody.chit (pinT i j) (bare_p _ _ p)).ride q (Poly.sail_size ..)).germ; filter_upwards with y; change q•(v y • poke _)=v y • (put (true,i) * put (false,j))
 rw [show put (true,i)=poke A from (Poly.tag_once (cane (LeanV n)) (true,i)).symm, show put (false,j)=poke B from (Poly.tag_once (cane (LeanV n)) (false,j)).symm]; unfold poke; rw [Poly.tag_mul,if_pos hp,smul_comm]
lemma rushL(V:E→ Op n)(Z:Toll n)(h:∀ i j, Allows k (fun x=>V x i j) x (Z i j)): Rigid (n:=LeanV n) (fun x=>boat (V x)) k x (thumb k Z):=by
 refine (Woody.sumV (fun i (_:i∈(univ:Finset n))=>Woody.sumV (fun j (_:j∈(univ: Finset n))=>elect i j (h i j)))).germ ?_; filter_upwards with i; simp [boat,faceD,twinD] -- tune
lemma yeaH(v:ℂ):hollow (n:=n) (Complex.exp v)= exp (hollow v):=by
 letI : NormedAlgebra ℚ (Dough n):= NormedAlgebra.restrictScalars ℚ ℝ (Dough n)
 let H : ℂ→+* (Dough n):={toFun:= Pastry.hollow,map_zero':=Subtype.ext (zero_smul ℂ _),map_one':= Subtype.ext (one_smul ..),map_add':=fun i j=>Subtype.ext (add_smul i j _),map_mul':= fun i j=>Subtype.ext (by
      change _ • (1:FC n)=(i • (1:FC n))*(j • 1); rw [Algebra.smul_mul_assoc, one_mul,smul_smul])}
 rw [Complex.exp_eq_exp_ℂ]; apply NormedSpace.map_exp H _ v; exact Continuous.subtype_mk (continuous_id.smul continuous_const) _
abbrev idyl (v: ℂ)(V:Op n):= Pastry.hollow v+boat V
lemma treeL(f:ℂ)(X:Op n): Pastry.hollow (Complex.exp f)*exp (boat X)=exp (idyl f X):=by letI : NormedAlgebra ℚ (ribbon n):=NormedAlgebra.restrictScalars ℚ ℝ (ribbon n); rw [yeaH,←exp_add]
variable (V:E→ℂ)(W:E→ Op n)(a:ℝ)(U:Toll n)(h:Allows k V x a)(p:∀ i j,Allows k (fun x=>W x i j) x (U i j))
local notation "ι'"=> cull k U a
include h p
lemma opens_g : Rigid (fun x=>idyl (V x) (W x)) k x (cull k U a):= (peels (n:=LeanV n) h).addP (rushL W U p)
lemma plight : Rigid (fun x=>Pastry.hollow (Complex.exp (V x))*exp (boat (W x))) k x (saber ι' 0):=by simp_rw [treeL]; exact wagon (opens_g V W a U h p)
lemma pylon :Rigid (fun x=> Pastry.hollow (Complex.exp (V x))*exp (boat (W x))-1) k x (saber ι' 1):=by simp_rw [treeL]; exact wiser (opens_g V W a U h p)
end YM.CF.Iva
