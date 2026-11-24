import YM.CF.Eire.Walk
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Eire
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
variable {N P B:Side}(S:StepData (Domain N B) (Domain P B)){r D:ℕ}
variable (L L':Ride S)
local notation "bay"=> Stilo.bay
open Rush Scroll Paige Vault Phase Acorn Spire
variable {A:Side}{j k:ℕ}{o:Odd A.val}{Y:Pricing j A o (Thread j)}{e:ℝ}{q:Grasp Y B e}{I:Aim (mid P B)}{M:Male}{α K K' t a d C H:ℝ}
variable (V: ∀ A:Support (Domain P B),Lend P B e A)(X:Tints P B e)
-- locality charge all Ids including ties/halo, anti axis irrelevant
lemma lit_i (i:Kite S r)(p: Vista q M I V k K t a d)(R:Pec.Pride (mid P B))(v:Dyes α e R k X C H)(x y:Castle P B e (danceL S i.1.val r))(A B':Ids (mid P B))(c:Set.EqOn A B' ((danceL S i.1.val r∪ i.2.1∪ i.2.2):Support (Domain P B)))(h:∀ x',Agrees ((i.2.1∪i.2.2):Support (Domain P B)) (x.val x') (y.val x')):
 Scion.stock e (danceL S i.1.val r) X V x A i.2= Scion.stock e (danceL S i.1.val r) X V y B' i.2:=by
 let W:= danceL S i.1.val r; have g:Grove (terr _) W:= dance_g S i.1; have hu(X:Support (Domain P B))(g:Grove (terr _) X):X.Nonempty:=by cases g <;> simp
 have hx:=hu _ g
 have he: Hive.chip (N:=mid P B) W A=Hive.chip (N:=mid P B) W B':=by -- identifier chip ambiguous
    have ht:Set.EqOn (priorP A) (priorP B') W:= fun i v=>congrArg Prod.fst (c (mem_union_left _ (mem_union_left _ v))) -- tune
    unfold Hive.chip; rw [mastL W _ _ ht,show A _= B' _ from c (mem_union_left _ (mem_union_left _ (mastP W hx (priorP B')).1))]
 change Scion.stock e W X V x A i.2=Scion.stock e W X V y B' i.2; unfold Scion.stock; refine congrArg₂ (· • ·) ?_ ?_
 · let s:=Hive.chip W A; unfold strokeC; dsimp only; unfold strideH; rw [←he]; let Z:= actS s i.2.1; have hz:=v.arch _ (grove_t _ s g); obtain ⟨C,v,-⟩:=hz; have ht:= (v Z).1; apply congrArg (cSignX _); apply ht.reads; exact ferryG Z A B' s _ _ (actG_l .. |>.symm ▸ c.mono (Finset.coe_subset.mpr (subset_union_right.trans subset_union_left))) (fun x=>by rw [actG_l]; exact agrees_mono (h x) (Finset.coe_subset.mpr subset_union_left))
 rw [hols,hols, ←he]; refine sum_congr rfl fun j _=>?_ ; let s:=Hive.chip W A; by_cases w:(sumW W V s A j).1∈ ({i.2.2}:Finset _); swap
 · rw [if_neg w,if_neg (show (sumW W V s B' j).1∉{i.2.2} from w)]
 rw [if_pos w,if_pos (show (sumW W V s B' j).1∈{i.2.2} from w)]
 exact phase_u W V _ A {j} B' g p x y (fun i v=>mem_singleton.mp v|>.symm ▸ (mem_singleton.mp w).le) (c.mono (Finset.coe_subset.mpr subset_union_right)) (fun i=> agrees_mono (h i) (Finset.coe_subset.mpr subset_union_right)) j (mem_singleton_self _) -- tune
variable(T T' U U': Pane (mid P B))(G:Ids (mid P B))
variable (D)
def printG (Z: Finset (Hos S r))(O: Hos S r) (b:Bool): Pane (mid P B):= if b then valve S T U (insert O Z) D else valve S T U Z D
def postM (Z:Finset (Hos S r))(i: Kite S r): FC (Single (mid P B)):= if p:(printG S D T U Z i.1)∈ MonoX P B e (danceL S i.1.val r) then Scion.stock e (danceL S i.1.val r) X V ⟨_,p⟩ G i.2 else 0
-- uniform arch recipe for all parent sets and field tags, dummy seals treated after requests
abbrev clipM (Z: Finset (Kite S r))(l:List (Hos S r)):= liftK S Z ∩ l.toFinset
abbrev legend (Z:Finset (Kite S r))(w:Hos S r):= Z.filter fun i=> i.1=w
def rankG (Z:Finset (Kite S r))(l : List (Hos S r))(i:Hos S r): FC (Single (mid P B)):= if i∈liftK S Z then ∑ j∈legend S Z i,postM S D V X T U G (clipM S Z l) j else 1
def paint (Z:Finset (Kite S r))(l:List (Hos S r)): FC (Single (mid P B)):= match l with
| [] => 1
| i::l => rankG S D V X T U G Z l i* paint Z l
lemma ink_p (Z:Finset (Kite S r))(v:∀ i∈Z,frameP S i ⊆ bay L)(p:Vista q M I V k K ((Fintype.card Play:ℝ)*t) a d)(g:∀ i∈ Z,ShiftD k K' K e (danceL S i.1.val r) G (Hive.chip (danceL S i.1.val r) G))(l:List (Hos S r))(i:Hos S r): Pitch bell (lipF (mintK S L)) 0 (rankG S D V X T U G Z l i):=by
 unfold rankG; split; swap; · exact zeroW _
 apply Pitch.sum; intro j t; let h:= (mem_filter.mp t).1; unfold postM; split; next a => exact rolled S L j p ⟨_,a⟩ G (g j h) (v j h)
 exact Pitch.null
lemma paint_p (Z:Finset (Kite S r))(v:∀ i∈ Z,frameP S i⊆ bay L)(p:Vista q M I V k K ((Fintype.card Play:ℝ)*t) a d)(g:∀ i∈ Z, ShiftD k K' K e (danceL S i.1.val r) G (Hive.chip (danceL S i.1.val r) G))(l:List (Hos S r)): Pitch bell (lipF (mintK S L)) 0 (paint S D V X T U G Z l):=by
 induction l with| nil=> exact zeroW _| cons i l ih=> exact (ink_p S D L V X T U G Z v p g l i).mu ih
end YM.CF.Eire
