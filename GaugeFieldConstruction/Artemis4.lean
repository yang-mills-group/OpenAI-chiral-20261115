import GaugeFieldConstruction.Bladex4
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry 
namespace Iona
variable {I θ E:Type}[Fintype I][LinearOrder I]{n:Side}
open Rio Grotto Isle Lattice.Corona
section
variable (σ:I→ Seat n) (F:XE I (InkD n) n)(K:KK I (Copy n) n)(T: PI I n→ℝ)(Y:KI I n→ℝ)
variable (μ:I→ℝ)(s:I→List I)(G:I→Hub n)
-- deterministic.Calendar tail after ascending Step order. L chronological build
abbrev RX (P:Rio I n):=F+pureX P
abbrev BX (P:Rio I n):=K+P.B
def turnY (P:Rio I n)(i:I):Rio I n:=P+(FrameT (RX F P) (BX K P)).insertΦ (G i) σ (s i) (μ i) i
def ProgramL (L:List I): Rio I n:=L.foldl (turnY σ F K μ s G) 0
local notation "ξL"=> ProgramL σ F K μ s G
private lemma St (i:I)(L:List I): (ξL (L++[i]))=turnY σ F K μ s G (ξL L) i:=by rw[ProgramL,List.foldl_append]; rfl
-- query pay recurrence.In theorem uses any selected prefix with incoming weighted Book. debt charge.
local notation "PIζ"=>rental
variable (C:BudgetPoint)(h ℓ Ω η a:ℝ)(b k:ℕ)(fV:BillX C σ h 1 T F)(tV:BillF C σ h 1 k Y K)
-- rite fixture; any step subset eligible
structure FlushL (L:List I): Prop where
    frame (i:I)(p:i∈L):σ i=(G i).val.1
    costB (i:I)(p:i∈L):5*(μ i*Summit b a (G i).val.2)≤ℓ
    p0(i)(p:i∈L):0≤μ i
include T Y fV tV
lemma WarpP (v:0≤h)(u:0<η)(p:0≤ Ω)(q:Cube_M b*Ω≤1)(L: List I)(f: FlushL σ μ G ℓ a b L): WarpL C σ 1 h k b a η ℓ Ω (rental b a η T Y) (L.map σ) (ProgramL σ F K μ s G L):=by
 induction L using List.reverseRecOn with
 | nil=>exact WarpL.empty
 | append_singleton L t ih=>
    let P:= ξL L; have hl:t∈L++[t]:= List.mem_append_right _ (by simp); have hw:=soci σ F K C h k T Y fV tV ℓ η Ω a b P (μ t) (s t) t (G t) (f.frame _ hl) (f.p0 _ hl) u p v q (f.costB t hl) -- tune
    rw [show IncomeP F K P=FrameT (RX F P) (BX K P) from (by unfold RX BX IncomeP pureX; rw[add_assoc])] at hw
    rw[List.map_append,St]; refine WarpL.step (ih ?_) hw; exact ⟨fun i p=>f.frame i (List.mem_append_left _ p),fun i p=>f.costB i (List.mem_append_left _ p),fun i p=>f.p0 i (List.mem_append_left _ p)⟩
include T Y fV tV
local notation "ηL"=> rental b a η T Y
structure Rider4 (X:Origin n)(L: List (Seat n))(Z Φ:ℝ):Prop where
   p0: 0<η
   p1: 0≤ ℓ
   sum:crewFlow b L Φ
   rise : Z+ ℓ*Φ+(advanceC ℓ η*Z+stolon b Ω η ℓ*Φ)≤ Ω
   proc:0≤Ω
   expa:advanceC ℓ η≤ 1
   cap :∀ i:Seat n,X L i≤ Z
   span:Scales b a η L
lemma Skalp (v:0≤h)(q:Cube_M b*Ω≤1)(Z Φ:ℝ)(L Kz:List I)(w: Rider4 ℓ Ω η a b (rental b a η T Y) ((L++Kz).map σ) Z Φ)(c:FlushL σ μ G ℓ a b L): let P:= ProgramL σ F K μ s G L; ∃ W:CashI I n, Weighted C σ 1 h k P W ∧∀ i:Seat n,Paw b a η W (Kz.map σ) i ≤ ℓ*Φ∧Rio.Band b a η W (Kz.map σ) i ≤ advanceC ℓ η*Z+stolon b Ω η ℓ*Φ:=by
 intro P; have wz: WarpL C σ 1 h k b a η ℓ Ω ηL (L.map σ) P:= WarpP σ F K T Y μ s G C h _ _ _ _ b k fV tV v w.p0 w.proc q L c
 rw [List.map_append] at w
 have Q: 0≤ ηL:=by
    intro i y; exact add_nonneg (pointX_gene _ _ fV.gist _ (fun _=>Temp_p ..|>.le) y) (pointX_gene _ _ tV.gist _ (fun _=>Temp_p ..|>.le) y)
 have Qs(S:List (Seat n))(i y:Seat n):(ηL S i) ≤ ηL (y::S) i:=by
    unfold rental; exact add_le_add (pointX_up cloudP _ fV.gist _ _ (fun x=>Temp_mono b _ η S x w.p0.le y) _) (pointX_up cloudK _ tV.gist _ _ (fun x=>Temp_mono b _ η S x w.p0.le y) _)
 have t:crewFlow b (L.map σ) Φ:=by
    intro i; let f:=fun j:Seat n=> windPulse b j i; have r:=w.sum i
    rw [List.map_append,List.sum_append] at r; refine le_trans (le_add_of_nonneg_right ?_) r
    apply List.sum_nonneg; intro i h; obtain ⟨a,b,rfl⟩:=List.mem_map.mp h; exact (Real.exp_pos _).le
 have he:=pressure C σ 1 h k b a η ℓ Ω (ηL) (Kz.map σ) (L.map σ) P Φ Z w.rise w.p1 w.p0 w.expa w.proc Q Qs wz w.cap w.span t
 obtain ⟨W,u,h⟩:=he; refine ⟨W,u,fun i=>?_⟩; have k:= advanceC ℓ η; have hv: 0≤advanceC ℓ η:=mul_nonneg (mul_nonneg w.p1 (by norm_num)) (inv_nonneg.mpr w.p0.le); refine ⟨(h i).1.trans (mul_le_mul_of_nonneg_left (t i) w.p1), (le_add_of_nonneg_right ?_).trans ((h i).2.trans (add_le_add (mul_le_mul_of_nonneg_left (w.cap i) hv) (mul_le_mul_of_nonneg_left (t i) (Sl_Pos b η ℓ Ω w.p1 w.p0 w.proc))))⟩; exact mul_nonneg hv (add_nonneg (show 0≤(ηL) _ _ from Q _ _) (u.estate (a:=a) (d:=b) w.p0.le _ i).1)
omit T Y fV tV
local notation "σk"=>turnY σ F K μ s G
lemma BankIt (L:List I)(k:I)(t:k∉L)(h:BlankM F K k): BlankM (RX F (ξL L)) (BX K (ξL L)) k:=by
 induction L using List.reverseRecOn with
 | nil=> rw[show RX F (ξL [])=F from (by change F+(0+0)=_; rw[add_zero,add_zero]), show BX K (ξL [])=K from (by change K+0=K; rw[add_zero])]; exact h
 | append_singleton L i ih=>
    have t':k ≠i:=fun z=>t (by simp[z]); let V:=ξL L; let Y₀:= FrameT (RX F V) (BX K V); let A:=insertΦ Y₀ (G i) σ (s i) (μ i) i; rw[St]; change BlankM (F+pureX (V+A)) (K+(V.B+A.B)) k
    rw [show F+pureX (V+A)=RX F V+pureX A from (by change F+(V.X+A.X+(V.Y+A.Y))=F+(V.X+V.Y)+ (A.X+A.Y); abel),←add_assoc]
    have v:=ih (fun p=> t (by simp[p])); have w:= coastline σ (RX F V) (BX K V) (G i) (s i) (μ i) i k v t'; constructor
    · intro r e x; exact e (show (RX F V) r+ pureX A r=0 from (by rw [show RX F V r=0 from Classical.byContradiction (fun u=>v.1 r u x),show pureX A r=0 from Classical.byContradiction (fun u=> w.1 r u x),add_zero]))
    intro r e x; exact e (show (BX K V) r+A.B r=0 from (by rw [show BX K V r=0 from Classical.byContradiction (fun u=>v.2 r u x),show A.B r=0 from Classical.byContradiction (fun u=>w.2 r u x), add_zero]))
lemma bandy_r(L:List I) (y:PI I n)(p:pureX (ξL L) y≠0):∃ i∈L,i∈ y.1 ∧ (G i).val.1=y.2.val.1∧(G i).val.2⊆ y.2.val.2:=by
 induction L using List.reverseRecOn with
 | nil=> exact False.elim (p (by change (0+0:InkD n)=_; rw [add_zero]))
 | append_singleton L i ih=>
    by_cases x:pureX (ξL L) y=0; swap
    · obtain ⟨i,h,u⟩:=ih x; exact ⟨i,List.mem_append_left _ h,u⟩
    rw[St] at p; let V:=ξL L; let A:=(FrameT (RX F V) (BX K V)).insertΦ (G i) σ (s i) (μ i) i; refine ⟨_,List.mem_append_right _ (List.mem_singleton_self _), (staffKY σ (RX F V) (BX K V) (G i) (s i) (μ i) i).1 y ?_⟩; intro b; apply p; change pureX (V+A) y=0; rw[show pureX (V+A)=pureX V+pureX A from (by change V.X+A.X + (V.Y+A.Y)=V.X+V.Y + (A.X+A.Y); abel),Pi.add_apply]; change pureX (ξL L) y + pureX A y=0; change pureX A y=0 at b; rw [x,b,add_zero]
lemma bandy_F(L:List I)(y:KI I n)(p:(ξL L).B y≠0):∃ i∈L,i∈ y.1:=by
 induction L using List.reverseRecOn with
 | nil=>exact False.elim (p rfl)
 | append_singleton L i ih=>
    by_cases v:(ξL L).B y=0; swap
    · obtain ⟨i,h,u⟩:= ih v; exact ⟨i,List.mem_append_left _ h,u⟩
    rw [St] at p; let V:=ξL L; let A:=(FrameT (RX F V) (BX K V)).insertΦ (G i) σ (s i) (μ i) i; refine ⟨_,List.mem_append_right _ (List.mem_singleton_self _), (staffKY σ (RX F V) (BX K V) (G i) (s i) (μ i) i).2 y ?_⟩; intro b; apply p; change (ξL L).B y+A.B y= _; change A.B y=0 at b; rw [v,b,add_zero] -- tune
end
end Iona
end YM.CF.Scree.Ing
end
