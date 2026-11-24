import YM.CF.Iva.Loon
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
variable {N P B:Side}{G:Ratio (mid N B) (mid P B)}{S:StepData (Domain N B) (Domain P B)}{x β R e a b:ℝ} {n m l k:ℕ}
local notation "G₅"=> SU.group
variable{T:Tube G₅ S}(Z:Muster G S x e T)(M:Monk G₅ S){w t u C D:ℝ}
local notation "l_"=> Z.post
local notation "q_"=> Z.trot
local notation "Ba"=> radiusB x
local notation "Wa"=> (fun y=>M.atop y x)
open Lor
attribute [local instance] opCStarAlgebra
local notation "M'"=> (violet M)
attribute [local instance] opCStarAlgebra
local notation "d_"=> Single (mid N B)
open Lor Font
variable(i:Site (Domain N B))
abbrev verbP (Z:Muster G S x e T)(P: Rent0 G e)(i j:Single (mid N B)):= Corne.led G x Z.Fame P i j
def wreath (k:ℕ)(o:Site (More N))(U:ℝ): Toll (Single N):= fun i j=> if place_x i=o ∧ place_x j∈ halo k {o} then U else 0
variable {s v η b1:ℝ}{H₀:nomA N P B→Op (Single (mid N B))}
variable (h:S.ratio=ratio G)(e_:Ind G Z.Fame s v η n H₀)
local notation "th"=> ((radiusB x)+1)
section value
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{K:E→Rent0 G e}{u:E}
include h e_
lemma mask_p(i':Site (Domain N B))(t j:d_)(p:¬(place_x t=i'∧place_x j∈ halo th {i'}))(b: Rent0 G e): maskS Z b i' t j=0:=by
 by_contra! v; obtain ⟨l,u⟩:= joy_p Z b h e_ i' t j v; by_cases w:place_x t=i'; exact p ⟨w,u⟩; exact v (if_neg w)
lemma staff(a:ℝ)(p:∀ t j, place_x t=i→ Allows k (fun x=>verbP Z (K x) t j) u a): ∀ t j:d_,Allows k (fun x=> maskS Z (K x) i t j) u (wreath (N:=mid N B) th i a t j):=by
 intro t j; unfold wreath; split_ifs with z
 · unfold maskS; simp only [Matrix.of_apply,z.1,↓reduceIte]; exact p _ _ z.1
 rw [funext fun x=> mask_p Z h e_ _ t j z (K x)]; exact allows_const _ norm_zero.le
end value
variable(K: Monk G₅ S→Rent0 G e)
local notation "X₀"=> (Cay.rough M 0)
local notation "M_"=> (Cay.violet M)
local notation "W'"=> (fun y=>Cay.violet (Wa y))
variable{F F':ℝ}
include h e_
lemma perK (w:∀ t j,place_x t=i →Allows k (starsW (x:=x) M (fun P=>verbP Z (K P) t j)) 0 F)(y:∀ t j, place_x t=i → Allows k (fun u=>verbP Z (K (Cay.rough (Wa u) 0)) t j) 0 F') : ∀ t j,Allows k (fun x=>maskS Z (K (Wa x)) i t j) 0 (wreath (N:=mid N B) th i (F+F') t j):=by
 apply staff Z i h e_; intro t j g; exact ((w t j g).add (y t j g)).germ (Eventually.of_forall fun _=> sub_add_cancel ..)
lemma walK (p:∀ t j,place_x t=i→Allows k ((starsW (x:=x) M (fun P=>verbP Z (K P) t j))+(starsW (x:=x) M_ (fun P=>verbP Z (K P) t j))) 0 F)(y:∀ t j,place_x t=i→Allows k (fun u=>verbP Z (K (Cay.rough (Wa u) 0)) t j) 0 F'):∀ t j:d_,Allows k (fun x=> maskS Z (K (Wa x)) i t j+maskS Z (K (W' x)) i t j) 0 (wreath (N:=mid N B) th i (F+(F'+F')) t j):=by
 intro t j; unfold wreath; split_ifs with z
 · obtain ⟨g,u⟩:=z; let b:= y t j g; refine ((p t j g).add (b.add b)).germ ?_; filter_upwards with x'; dsimp only [starsW,Pi.add_apply]; unfold maskS; simp only [Matrix.of_apply,g,↓reduceIte]; rw [show Cay.rough ((M_).atop x' x) 0=Cay.rough (M.atop x' x) 0 from rfl]; unfold verbP; rw [show (M_).atop x' x=violet (M.atop x' x) from rfl]; abel
 simp_rw [mask_p Z h e_ i t j z,add_zero]; exact allows_const _ norm_zero.le
end YM.CF.Iva
