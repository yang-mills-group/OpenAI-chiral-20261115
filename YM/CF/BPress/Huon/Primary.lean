import YM.CF.BPress.Huon.Array
/- $Near$ and Bias charges separated.B.Visible.Books.Point. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Huon
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Pf Primary Hazel Mount Stamps Skye Port Locale Cube Precision Next.SectorChange RG Sugar Honey
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
open Net Grid Driver Letter Letters Hazel Chrono Spin.Hole Actor House LocalH Sugar.Stage Wealth Weave Pressure Mount.Silhouette Awards Push.SectorMeasure Env Scree Vesper Shot Crew Honey Honey.Recipe Peel Peel.Spine Ledger Push.AbsoluteSums Mosaic Lilac Born Lilac.Stripe Peel.Along
variable {m s N:Side}{B:BandWidth}{A:Bands (More (mid m s)) B}{R:Hangar (More (mid m s))}
local notation "Λ"=> mid m s
local notation "η"=> More Λ
variable {H: Sugar.Crew A}{T:GramM (mid m s)}{X: Sugar.Stage (mid m s)}{Y:Driver (mid m s)}{k:ℕ} {c q d t v ε e d' C D ζ δ τ u b:ℝ}{p0 p1 p2 p3:Pledge}{h: Wish Y p0 p1 p2}{G: Brace.Duet m s}
namespace Pilot
variable (B0: Born A R X Y) (P: Edition Y)(F:Rented R H X Y.d e k c)(Q:Stamp A R X Y)(r:ℕ)
local notation "Ξ" => Visit A R H
-- denominator estimation.
def money(i:Tenor η) := if Tiny A X r i.2 then (P.op i (B0.H₁ 0)) else 0 -- retains only uncancelled budget
abbrev skew (x:Visit A R H)(i:Tenor η) := δRest A X.W.M scaffold (fun j=>arts P F Q x j) i
/-- bad assignment factor includes all Tiny original prefactor but divides $F1$ extracted at those terms -/
def ζLeft(x:Ξ)(i:Tenor η) := if Tiny A X r i.2 then arts P F Q x i-money B0 P r i else 0
def leftP (x:Ξ)(S:SlotT A R):= ∑ i∈badcore x (fun i:Tenor η=> plan A R i.1) S univ, ζLeft B0 P F Q r x i
-- clean excited. pieces.$ ∑ block → all short$. unmarked comparator.
def rightP (x:Ξ)(S:SlotT A R):=∑ i∈ Upper H x.val S, chast B0 P r i (chip x.val i)
lemma whole (x:Ξ) : ∑ i:Tenor η, skew P F Q x i =(∑ i,money B0 P r i) + ((∑ i,paysL P F Q r x i)+(∑ i,start0 B0 P F Q r x i))+ ∑ S∈ Camp x.val H,(leftP B0 P F Q r x S+rightP (H:=H) B0 P r x S):=by
 let v:= vicinity H x.val; let E:= Camp x.val H; let L:= Peel.Place H x.val; let Tx(i:Tenor η):=plan A R i.1; let w:= ζLeft B0 P F Q r x; let ptr(a:SlotT A R):= chipAt a Tx univ; let h(i:Tenor η):= rosy B0 P r i (chip x.val (Tx i)); have h₁: ∑ t∈ E, leftP B0 P F Q r x t=∑ i∈ptr v,w i:=by unfold leftP; rw [← sum_biUnion (separatesV x _ _)]; change (∑ i∈(Camp x.val H).biUnion (fun S=> badcore x Tx S univ), w i)=_; rw [partition]
 have h₂: ∑ t∈ E, rightP B0 P r x t=∑ i∈ptr (L \ v),h i:=by
    unfold rightP; rw [←sum_biUnion (upper_separates x.val), show E.biUnion (Upper H x.val)= L \ v from chargeG x.val,← portions (L \ v) Tx h univ]; apply sum_congr rfl; intro i u; unfold chast; exact sum_congr rfl fun i p=> congrArg _ (congrArg (chip x.val) (mem_filter.mp p).2.symm) -- tune orientation
 rw [sum_add_distrib]; change _ = _+_+((∑ t∈ E,leftP _ _ _ _ _ _ t)+∑ t∈ E,rightP (H:=H) B0 P r x t); rw [h₁,h₂]; unfold ptr chipAt; rw [sum_filter,sum_filter]; repeat rw [←sum_add_distrib]
 apply sum_congr rfl; intro t u; by_cases p:Tx t∈ v
 · by_cases e:Tiny A X r t.2
   · simp only [Finset.mem_sdiff, p, not_true_eq_false, and_false, ↓reduceIte, w,ζLeft, paysL,money,start0, e, show plan A R t.1∈ vicinity H _ from p, skew,δRest, if_pos (show currencyT A X.W.M (scaffold t) from e.1)]; abel -- tune
   next=> simp [Finset.mem_sdiff,e,p,Tx,w,ζLeft,money,start0,paysL,arts,h,skew] -- h unused
 have he:Tx t ∉ v:= p; simp only [Finset.mem_sdiff, p, not_false_eq_true,and_true, ite_false]; by_cases e:Tiny A X r t.2; swap; · simp only [h, rosy,money,start0,paysL, skew,δRest,arts, e, ite_false,add_zero, zero_add, ite_self]; -- tune
 unfold paysL start0; rw [if_pos e,if_pos e, if_neg p]; by_cases u:Tx t∈ L; · rw [if_pos u]; unfold h rosy; simp only [money,e,ite_true,skew,δRest,if_pos (show currencyT A X.W.M (scaffold t) from e.1),δop]; abel
 rw [if_neg u]; unfold money; simp only [e,ite_true,skew,δRest,if_pos (show currencyT A X.W.M (scaffold t) from e.1), show chip x.val (plan A R t.1)= 0 from not_not.mp (fun h=> u ((grade_t F x p).2 h))]; abel
end Pilot
end YM.CF.BPress.Huon
