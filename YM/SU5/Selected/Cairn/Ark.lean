import YM.SU5.Selected.Cairn.Belle
import YM.SU5.Selected.Cor.Pavilion
import YM.SU5.Selected.Twirl.Pearl
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Pannier.Chancel.Attic.Cairn
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest Airy Rail Lantern Lantern.Bulb Attic Cuve
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 20000
local notation "I"=>Complex.I
open Mint Mezz Rubric Stencil
open Commission
open Afterglow Tower Tower.SlabMark Tapestry
attribute [local instance] opCStarAlgebra
namespace Giant
variable (A:Giant) {N:Side}(Z:A.Notes→basisRule) {T:Type}[Fintype T][DecidableEq T](P:Society T)(b y:Bool)(i:A.Block)(C:ℝ)
local notation "S"=> park N (A.patio b)
local notation "F" k:max=> A.Hours (N:=N) Z P b y C i k
noncomputable def fleur (U: Pane N) := countOne (A.Hours Z P b y C i true U) (A.Hours Z P b y C i false U) b
noncomputable def tonne : Buffered.Mark N:= fun x=> A.fleur Z P b y i C x.1
abbrev pied (b' y:Bool):= if b' then A.anchorX y else A.anchorY
local notation "K"=> A.fleur Z P b y i C
local notation "ρ"=> A.tonne (N:=N) Z P b y i C
omit b i y
include b i y
lemma flavour (U:Pane N): (K) U= ∑ t:pulseNode, lyric t • tape b (rune t ((F true) U) ((F false) U)):= loreP b _ _ P.club_card -- need macro parentheses
variable {M:Tulip.Male}{γ δ:ℝ}(c:A.Pride Z C δ γ M N)(h:A.tokenS<N.val)
omit c h
private abbrev film₃ (t:pulseNode): Pane N → WRect (Single N) P.Club:= fun x => rune t ((F true) x) ((F false) x)
include c h
private lemma film₃_ok(t:pulseNode) : Viole A P b (film₃ (N:=N) A Z P b y i C t):= ((chronos A Z P b y C i true c h).scale _).adds (chronos A Z P b y C i false c h)
omit c h in
lemma mosaic : (ρ)= ∑ t:pulseNode, lyric t • (fun x:Fields N=> tape b (film₃ A Z P b y i C t x.1)):=by funext x; simp_rw [Finset.sum_apply]; exact flavour A Z P b y i C _
lemma tonne_guard : AtSupport false (park N (A.patio b)) (ρ):=by
 rw [A.mosaic]; generalize h': (Finset.univ:Finset pulseNode)=T₁; clear h'; induction T₁ using Finset.induction_on with
 | empty=> rw [sum_empty]; exact AtSupport.zeroM
 | insert t T h' H=> rw [sum_insert h']; exact ((film₃_ok A Z P b y i C c h _).serves.smulM _).addM H -- c param order etc
lemma tonne_c : Continuous ρ:=by
 rw [A.mosaic]; generalize h': (Finset.univ:Finset pulseNode)=T₁; clear h'; induction T₁ using Finset.induction_on with
 | empty=> rw [sum_empty]; exact continuous_const
 | insert d T h' H=> rw [sum_insert h']; exact ( ((tape_c b).comp ((film₃_ok A Z P b y i C c h _).cont.comp continuous_fst)).const_smul (lyric d)).add H
omit c h
lemma coat (g:Seat N→SU.E)(U: Pane N): fleur A Z P b y i C (gauge g U)= twist (quantU (tradew N g)) ((K) U):=by
 simp_rw [flavour,map_sum,twist_scalar]; apply sum_congr rfl; intro j _; apply congrArg (fun f:FC (Single N)=> lyric j • f); let Q:=gauge g U; let p:=P.arm (g ((wrap (More N)) (A.pied b y))); rw [tape_cov];
 let f:= F true; let v:= F false; let Y:= rune j (f Q) (v Q); change tape b Y= _; rw [show (tradew N g).val*rune j (f U) (v U)=Y*p.val from ?_,wave_det, P.arm_d,map_one,one_smul]; unfold Y rune f v Q; rw [Matrix.mul_add,Matrix.mul_smul,Matrix.add_mul,Matrix.smul_mul]; rw [show A.Hours Z P b y C i true (gauge g U)*p.val=_ from merit .., show A.Hours Z P b y C i false (gauge g U)*p.val=_ from merit ..]
lemma tonne_0 : Buffered.covariant (ρ):=fun g x=> coat A Z P b y i C g _
end Giant
end YM.CF.Pannier.Chancel.Attic.Cairn
open YM.CF.Pannier.Chancel.Attic.Cairn.Giant
#print axioms tonne_c
#print axioms tonne_guard
#print axioms tonne_0
#check @film₃_ok
