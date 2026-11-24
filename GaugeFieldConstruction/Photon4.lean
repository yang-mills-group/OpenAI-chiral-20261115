import GaugeFieldConstruction.Energia4
import GaugeFieldConstruction.GlintM
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
variable {I α β:Type}[Fintype I][LinearOrder I][Fintype α][Fintype β]
open Rio Grotto
namespace Isle
variable {n:Side}(B:Isle I α β n)(p:Hub n)(σ:I→Seat n)(C:BudgetPoint)(U:Orbit n)(S:List I)(v':Isle.Speak B σ)(pK:poke_F σ p.val.2 S.toFinset)(μ:ℝ)(k:I)
abbrev Path (S:List I):= Fin (poet S).length
private lemma poet_up: ∀ i:Path S,Night S ((poet S).get i):=fun i=> poet_b S _ (List.get_mem ..) -- tune
abbrev altuQ (j:Path S):= B.salt_Four p S ((poet S).get j) μ (poet_up S j) k
abbrev insertΦ : Rio I n:=payment σ (altuQ B p S μ k)
variable (X:Key I→RegBudget n)(r:Key I→ForceBudget n)
def sayQ (x:Key I):= exp (exponentL C (X x) U.1)*fueled C (r x) U
def addCosto (x:Key I):=X x+Canz σ _ (pureX (B.insertΦ p σ S μ k)) x
def BankoB(x:Key I):= r x+Canz σ _ (B.insertΦ p σ S μ k).B x
local notation "X0"=> sayQ C U X r
local notation "Xn"=> sayQ C U (addCosto B p σ S μ k X) (BankoB B p σ S μ k r)
variable (l:Rue.FleetS C.threshold U.1)(x':∀ x,exponentL C (X x) U.1=B.gaugeQ C U x)(b':∀ x,PourUp B.U (fun i=> B.κQ U i x)= fun i=>r x i U)
def giftζ(x:Key I):=exp (B.gaugeQ C U x)*(∑ i:Path S,(altuQ B p S μ k i).cashVector C x (fun j=> B.κQ U j x) U)
local notation "Kz"=> giftζ B p C U S μ k
include l x' b'
lemma preSay (x:Key I) : sayQ C U X r x=exp (B.gaugeQ C U x) * B.heapQ C U x:=by unfold sayQ; rw[x',hum_pay l,←b', Hum_split]; rfl
omit l x' b' in
private lemma ex_LV (p:BudgetPoint)(x:Pane n)(X Y:RegBudget n): exponentL p (X+Y) x=exponentL p X x+exponentL p Y x:=by
 unfold exponentL; rw [←sum_add_distrib]; apply sum_congr rfl; intro i _; unfold numbE; by_cases h:pingS p.threshold i.val.2 x <;> simp[Set.indicator,h]
lemma singulari : Kin σ (sayQ C U (addCosto B p σ S μ k X) (BankoB B p σ S μ k r)) (sayQ C U X r + giftζ B p C U S μ k) :=by
 let K:=altuQ B p S μ k
 have v(i):KidValid k (K i):=⟨fun j=> Or.inl (List.mem_cons_self ..),fun j x=> Or.inl (List.mem_cons_self ..)⟩
 have t: River (fun y=> exponentL C (X y) U.1):=by simp_rw[x']; exact B.gaugeQ_r C U
 have hp:=Insert_p σ K C U l (fun x i=> B.κQ U i x) (κQ_r _ _) k r X b' v t -- tune
 simp only [x'] at hp -- ex_LV include args dummy
 unfold sayQ giftζ addCosto BankoB; simp_rw [ex_LV,x']; exact hp
-- evaluate all new.Price.Payment.Masks incounted
include v' pK
variable (t: S.Nodup)
include t
lemma gift_s (w:S.length ≤ 2)(x:Key I)(q:x∈hill I)(p0:∀ i∈S,x i=0):giftζ B p C U S μ k x= (x k*(μ:ℂ)) • lance (sayQ C U X r) S x:=by
 let f:= B.gaugeQ C U; let g:= B.heapQ C U; rw [show sayQ C U X r=(exp∘ f)*g from funext (preSay B C U X r l x' b'), silver (B.gaugeQ_r ..) (B.heapQ_r ..) _ t w x q p0]
 unfold giftζ; let Q:=x k*(μ:ℂ)
 let Z:= poet S; let Hs(i:Sect I):= Sect.wit f g i x
 have he:(Z.map Hs).sum=∑ i:Fin Z.length,Hs (Z.get i):=by nth_rw 1 [← List.ofFn_get Z]; rw[List.map_ofFn,List.sum_ofFn]; rfl
 rw [show ((poet S).map _).sum=_ from he]; change _= Q • (exp (f x)*(∑ i:Fin Z.length,_))
 rw[← Algebra.mul_smul_comm,Finset.smul_sum]; apply congrArg (exp (f x)*·); apply Finset.sum_congr rfl; intro i _; exact B.card_turn p σ C U (poet_up _ _) v' pK μ k x q t p0 -- rw direction
omit t v' pK
lemma unchanged4 (T:List I)(g:k∉T)(q:ψS σ T) : tipI (sayQ C U (B.addCosto p σ S μ k X) (B.BankoB p σ S μ k r)) T=tipI (sayQ C U X r) T:=by
 let M:= B.insertΦ p σ S μ k; have hf:= B.singulari p σ C U S μ k X r l x' b'
 apply tip_nurse _ _ _ _ hf.1 g; funext x; let t:=dune k x; have he:=Kins σ (altuQ B p S μ k) k (fun i=> ⟨fun j=> Or.inl (List.mem_cons_self ..),fun x h=> Or.inl (List.mem_cons_self ..)⟩) t (update_self ..); change exp (exponentL _ (X t+Canz σ _ (pureX M) t) _)*fueled _ (r t+Canz σ _ M.B t) _=_
 rw [he.1,he.2,add_zero,add_zero]; rfl
include t v' pK
lemma height_p (w:S.length ≤2)(q:k ∉ S)(j :List I)(V:ψS σ (k::j))(hx:∀ i∈S,i∉j)(p': (sayQ C U X r)∘dune k=sayQ C U X r): tipI (sayQ C U (B.addCosto p σ S μ k X) (B.BankoB p σ S μ k r)) (k::j)=(μ:ℂ) • tipI (sayQ C U X r) (S++j):=by
 have he:River (sayQ C U X r):=by rw [funext (preSay B C U X r l x' b')]; exact (gaugeQ_r B C U|>.exp_V).mul_T (heapQ_r ..)
 exact onRich _ _ _ _ (B.singulari p σ C U S μ k X r l x' b') S k (μ:ℂ) he (B.gift_s p σ C U S v' pK μ k X r l x' b' t w) p' q j V hx
#print axioms height_p
end Isle
end Iona
end YM.CF.Scree.Ing
end
