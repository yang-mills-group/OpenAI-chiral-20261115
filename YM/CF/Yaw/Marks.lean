import YM.CF.Yaw.Fancy
import YM.CF.Yaw.Year
import YM.CF.Plume.Ton
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Yaw
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Eire Jet Scroll Push.AbsoluteSums.Trees PetalP
section
variable {α β:Type*}
lemma rowsP [DecidableEq α][CommMonoid β](p:α→β)(L:List α)(t:L.Nodup):(L.map p).prod=∏ i∈L.toFinset,p i:=by induction L with | nil=>simp| cons i L ih=> rw [List.toFinset_cons,prod_insert (by simpa using (List.nodup_cons.mp t).1),←ih (List.nodup_cons.mp t).2]; rfl
lemma prodPi [Monoid β](L:List (α→β))(x:α): L.prod x=(L.map fun i=> i x).prod:=by induction L with | nil=>rfl| cons i L ih=> rw [List.prod_cons,Pi.mul_apply,ih]; rfl
end
variable {I N P B:Side}(S:StepData (Domain N B) (Domain P B)) (G:Ratio (mid N B) (mid P B)){r d k l D:ℕ}
open Rush Scroll Paige Vault Phase Acorn Spire
variable {ι:Type}[Fintype ι][DecidableEq ι](X:ι→ Palot.leaf (Site (Domain N B)))
local notation "m"=> mid P B
local notation "V'"=> Domain P B
local notation "H_"=> Eire.Ride S
local notation "S_"=> Eire.Folk S r ι
local notation "τ"=> Oboe (Single (mid P B))
local notation "χ"=> (LeanV (Single (mid P B)))
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
variable{S G}
variable (L:List (Kite S r))(U:List (Rust (mid P B)))(W:List ι)
-- tickets explicit order fixed for this τ.Code poll. no cost sum over order
abbrev sentR(i:Rust (mid P B)):Folk S r ι:=Sum.inr (.inl i)
abbrev sentV(i:ι): Folk S r ι:=Sum.inr (.inr i)
abbrev weave_g:= List.map (fun i=> Sum.inl (β:=Rust (mid P B)⊕ι) i) L ++ (U.map (sentR (S:=S) (ι:=ι)) ++ W.map sentV) -- implicit S witness turb
local notation "Z'"=> weave_g L U W
lemma left_i: (Z').toFinset.toLeft=L.toFinset:=by ext i; simp [weave_g,sentR,sentV]
lemma left_v: (Z').toFinset.toRight.toLeft=U.toFinset:=by ext i; simp [weave_g,sentR,sentV]
lemma right_v: (Z').toFinset.toRight.toRight=W.toFinset:=by ext i; simp [weave_g,sentR,sentV]
section pod
variable (u:L.Nodup)(p:U.Nodup)(g:W.Nodup)
include u p g
lemma noK : (Z').Nodup:=by
 let X:=L.map (fun i=> Sum.inl (β:=Rust (mid P B)⊕ι) i); let K:=U.map (sentR (S:=S) (ι:=ι) (r:=r)); let T:= W.map (sentV (S:=S) (r:=r)); refine List.pairwise_append.mpr ⟨List.Nodup.map Sum.inl_injective u, List.pairwise_append.mpr ⟨List.Nodup.map (show Injective (sentR (S:=S) (ι:=ι) (r:=r)) from Sum.inr_injective.comp Sum.inl_injective) p,List.Nodup.map (show Injective (sentV (S:=S) (ι:=ι) (r:=r)) from Sum.inr_injective.comp Sum.inr_injective) g,?_⟩,?_⟩
 · intro i x j h; obtain ⟨_,_,rfl⟩:=List.mem_map.mp x; obtain ⟨_,_,rfl⟩:=List.mem_map.mp h; unfold sentR sentV; simp
 intro i x j h; obtain ⟨_,_,rfl⟩:= List.mem_map.mp x; rcases List.mem_append.mp h with f|f<;>obtain ⟨_,_,rfl⟩:=List.mem_map.mp f<;>exact Sum.inl_ne_inr
end pod
open Eire.Dress
variable {e A Q:ℝ}(R:GramM (mid P B))(M:E→Monk SU.group S)(T: ∀ i:E, Dress G S e r D (M i) R k X)(x:ℝ)(l:ℕ)(ξ:Eire.Troupe S r ι)
local notation "ξ₀"=>(Z').toFinset
abbrev schoolK (i:S_)(e':E): Cipher (mid P B):= match i with
| .inr (.inl j) =>OpK S x R (trot S (M e') (penn S ξ)) (T e').cloth (T e').pipe (T e').chi (T e').wage l j
| _=>1
def row_g(i:Folk S r ι)(y:E):Cipher (mid N B):=match i with
| .inr (.inr j)=>(T y).coin (penn S ξ) j
| .inl j=> (T y).rare (penn S ξ) j.1
| _=>1
lemma spanProd {n:Type}[LinearOrder n][Fintype n](L:List (ribbon n)): (L.map (fun v=>v.val)).prod=L.prod.val:= (map_list_prod (Pastry.Dough _).val _).symm -- tune
lemma school_l (p:U.Nodup) (i:E):((Z').map fun j e'=>(schoolK X R M T x l ξ₀ j e').val).prod i=((T i).bodyL x l ξ₀).val:=by
 rw [prodPi,List.map_map]; let g(j:S_):=schoolK X R M T x l ξ₀ j i; rw [show (List.map _ _)= ((Z').map g).map (fun i=>i.val) from ?_,spanProd]; swap; · simp only [List.map_map]; rfl
 apply congrArg; unfold weave_g; simp only [List.map_append,List.map_map,List.prod_append]; let X'(j):= g (sentR j); rw [show (L.map (g ∘ Sum.inl)).prod=1 from ?_, show (W.map (g ∘ sentV)).prod=1 from ?_,one_mul,mul_one]; exact (rowsP X' U p).trans (by change _= (T i).bodyL x l ξ₀; unfold Eire.Dress.bodyL lure; rw [left_v])
 all_goals solve| simp [g,sentV,schoolK,Function.comp_def]| simp [g,schoolK,Function.comp_def] -- tune map_conv
lemma fields_b (p:L.Nodup)(q:pureK S L.toFinset)(r':W.Nodup)(i:E):((Z').map fun j e'=>(row_g X R M T ξ₀ j e').val).prod i=((T i).brew ξ₀).val:=by
 rw [prodPi,List.map_map]; let g(j:S_):= row_g X R M T ξ₀ j i; rw [show List.map _ _=((Z').map g).map (fun v=>v.val) from ?_,spanProd]; swap; · simp only [List.map_map]; rfl
 apply congrArg; unfold brew; dsimp only; rw [left_i, right_v, liftK,prod_image]; swap; · exact fun i a j v=>proud_p S _ q a v
 unfold weave_g; simp only [List.map_append,List.map_map,List.prod_append]; have ht:= rowsP (fun j=> g (Sum.inl j)) L p; rw [show (U.map (g ∘ sentR)).prod=1 from ?_,one_mul]; exact congrArg₂ (·*·) ht (rowsP (g∘sentV) W r'); simp [g,Function.comp_def,row_g,sentR]
end YM.CF.Yaw
