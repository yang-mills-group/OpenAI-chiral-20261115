import GaugeFieldConstruction.QuiffMQ
import GaugeFieldConstruction.PhonicsQ
import GaugeFieldConstruction.Barrera4
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
open Rio Grotto Isle Lattice.Corona
variable {I J:Type}[Fintype I][LinearOrder I][Fintype J][LinearOrder J]{n:Side}
variable (e:I↪J)(σ:I→Seat n)(σ':J→Seat n)
open Same4
local notation "Δ"=> PaintEV e
variable (F:XE I (InkD n) n)(K:KK I (Copy n) n) (F':XE J (InkD n) n)(K':KK J (Copy n) n)
variable (S:List I)
local notation "S'"=> List.map e S
variable (l m:ℕ)(a:l=m)(p:Hub n)
variable (X:Finset I)
abbrev SpiritRQ :Prop:= ∀ j:PI I n,j.1⊆ X→ F' (PaintEV e j)= F j
abbrev SpiritFQ:Prop:= ∀ j:KI I n,j.1⊆X→K' (PaintEV e j)=K j
local notation "ΡΙ"=> FrameT F K
local notation "ΡΘ"=> FrameT F' K'
variable (r:SpiritRQ e F F' S.toFinset)(b:SpiritFQ e K K' S.toFinset)
variable (s:Sect I)(s': Sect J)
structure MapLexQ : Prop where
    reads : s'.reg=s.reg.map (List.map e)
    powers: s'.pack=s.pack.map e
lemma poetQ : (poet S).length=(poet (S.map e)).length:=by match S with| []| [_]| [_,_]| _::_::_::_=> rfl
lemma songQ (j:Isle.Path S): MapLexQ e ((poet S).get j) ((poet (S.map e)).get (Fin.cast (poetQ e S) j)):=by
 match S with
 | []=> change Fin 1 at j; fin_cases j; exact ⟨rfl,rfl⟩
 | [i] => change Fin 2 at j; fin_cases j<;> exact ⟨rfl,rfl⟩
 | [i,k] => change Fin 5 at j; fin_cases j<;> exact ⟨rfl,rfl⟩
 | i::k::m::n=>exact j.elim0
variable (w:MapLexQ e s s')
include w
lemma ChpQ : s.reg.length=s'.reg.length:=by rw[w.reads,List.length_map]
local notation "ν_"=> (s.reg.length)
local notation "Υ_"=> (s'.reg.length)
lemma LeoQ(j:Fin ν_): boon s' (Fin.cast (ChpQ e s s' w) j)= List.map e (boon s j):=by
 unfold boon; let F:=s.reg; let T:=s'.reg; have h:T=F.map (List.map e):=w.reads
 -- dependent caption
 have g(T:List (List J))(F:List (List I))(h:T=F.map (List.map (⇑e)))(ι:F.length=T.length)(j:Fin F.length): T.get (Fin.cast ι j)= List.map e (F.get j):=by subst T; simp
 exact g T F h _ _
omit w
local notation "δV"=> PaintEV e
include r
lemma rFitQ (j:PI I n)(t:j.1⊆ S.toFinset)(L:List I)(D:Support (More n)): (FrameT F K).noteV S L j D=(FrameT F' K').noteV (S.map e) (L.map e) (PaintEV e j) D:=by
 unfold noteV; change (if _ then _ else _)= if _∧ Disjoint ((ΡΙ).UV j) D then F' (Δ j) else 0; rw [r j t,propext (know_Q e S _ ((ΡΘ).W (Δ j)) L (news_Cue e j.1))]
include w
lemma ΩSaleQ (A:Heart p (Dusk I n) s.reg.length)(D:Support (More n))(h:rosterF univ (fun i:Fin s.reg.length=>(FrameT F K).purseV S (A.val i))=[]) : let V:=iκQ e s.reg.length s'.reg.length p (ChpQ e s s' w) A; ∏ j:Fin s.reg.length, (FrameT F K).noteV S (boon s j) (A.val j) D=∏ j:Fin s'.reg.length,(FrameT F' K').noteV (S.map e) (boon s' j) (V.val j) D:=by
 intro V; apply Fintype.prod_equiv (finCongr (ChpQ e s s' w)); intro i; have hq:∀ j, (FrameT F K).noteV S j (A.val i) D=(FrameT F' K').noteV (S.map e) (j.map e) (Δ (A.val i)) D:=by intro j; exact rFitQ e F K F' K' S r _ (rangeRQ F K S _ p h i) _ D -- tune
 rw [show boon s' ((finCongr (ChpQ e s s' w)) i) = (boon s i).map e from LeoQ e s s' w i]; rw [show V.val ((finCongr (ChpQ e s s' w)) i)= Δ (A.val i) from rfl]; exact hq _
omit r
include b
lemma StepYQ (A:Finset (KI I n))(h:(FrameT F K).tressV S A=[]): (FrameT F K).oracle S s A=(FrameT F' K').oracle (S.map e) s' (A.image (PaintEV e)):=by
 unfold oracle; rw [w.powers,←propext (know_Q e S _ _ _ (rotaRQ e F K F' K' A))]; split; swap; · rfl
 rw [prod_image]; refine Finset.prod_congr rfl fun x t=> Eq.symm ?_; exact b x (rangeKQ F K S h x t); exact (ev_inj e _).injOn
#print axioms ΩSaleQ
#print axioms StepYQ
end Iona
end YM.CF.Scree.Ing
end
