import GaugeFieldConstruction.GravifierN
import GaugeFieldConstruction.Eddies
import GaugeFieldConstruction.Farouche
set_option autoImplicit false
set_option maxRecDepth 3000
noncomputable section
namespace YM.GaugeFieldConstruction.Invoice.curvΝ
open Phys Calibration Cauchy Row Wick Raster Gap Function MeasureTheory Set Filter Mirror Flux.One
open Floor Flavor
open Matter (Generation Sheet Slot)
open YM.Maxwell (Green normal normal_pos)
open scoped BigOperators Topology Classical
-- cubic chirality receipt on our concrete U1 directions. zero permit013. uses SAME channels.E
namespace LeftVU
local notation "A" => apex
local notation "K" => (32*(normal:ℂ))
local notation "L" => (4*(normal:ℂ))
open Wick.Yacht
lemma luminate (a b:Cauchy.Spin): stare (blend a b)=if a=b then K else 0:=by
 have h(i): stare (Gap.step i stone)=(if τ=i then -2*(normal:ℂ) else 0):=by rw [sheer,rank,map_smul,tick,lever,axis_s]; split_ifs <;> simp
 have t: stare (blend a b)= (-16*star (Hij τ a b))*(-2*(normal:ℂ)):=by
    rw [blend,map_sum,Finset.sum_eq_single τ]; rw [map_smul,h,if_pos rfl]; rfl
    intro i _ t; rw [map_smul,h,if_neg (Ne.symm t),smul_zero]; simp -- tune
    
 have hp: Hij τ a b=(if a=b then 1 else 0):=by fin_cases a <;> fin_cases b <;> first|rfl| simp
 rw[t,hp]; split_ifs <;> norm_num <;> ring
lemma powered (a b:Cauchy.Spin) : eye ((2:ℝ) • apex) (blend a b)=(if a=b then L else 0):=by
 have h: ((2:ℝ):ℂ)^3 * eye ((2:ℝ) • apex) (blend a b)=_:= Foulard (t:=2) (by norm_num) a b apex -- typo
 change _=stare _ at h
 rw [luminate] at h
 apply mul_left_cancel₀ (show ((2:ℝ):ℂ)^3≠0 by norm_num); rw [h]; split_ifs <;> push_cast <;> ring
abbrev A1Vue (i:Generation)(s:Sheet)(a:Cauchy.Spin):= debtF a (i,s)
lemma AxisS_bvu (x y:Slot)(a b:Cauchy.Spin)(d:Bool): eye apex (yarn d (debtF a x) (debtF b y))=(if x=y∧a=b then K else 0):=by
 rw[portF]; by_cases p:x=y
 · rw[if_pos p]; cases d <;> first|simpa only [thread_un,p,true_and] using luminate a b|simpa only [thread_on,p,true_and,eq_comm] using luminate b a
 simp[p]
lemma Twice_bvu (x y:Slot)(a b:Cauchy.Spin): eye ((2:ℝ) • apex) (yarn false (debtF a x) (debtF b y))=(if x=y∧a=b then L else 0):=by
 rw[portF]; by_cases p:x=y
 · rw [if_pos p,thread_un]; simpa only [p,true_and] using powered a b
 simp[p]
local notation "κS"=> (∅:Finset Sheet)
def LedgerL1 (s:Sheet)(m:Generation)(a b:Cauchy.Spin):Book:= αF (debtF a (m,s)) (debtF b (m+1,s))
abbrev Kπaxis (V W Z:Book):= prism 0 apex ((2:ℝ) • apex) V W Z -- use explicit linear header separately
lemma MinusS_bvu(x y:Slot)(a b:Cauchy.Spin): eye (-A) (yarn false (debtF a x) (debtF b y))= -(if x=y∧a=b then K else 0):=by
 have h:= yin (debtF b y) (debtF a x) (0:E4) A; simp only [sub_zero,zero_sub,AxisS_bvu] at h; rw [← neg_inj, ← h]; simp only[neg_neg,eq_comm]; -- tune
lemma axis_vu(s t u:Sheet)(a b c d e f:Cauchy.Spin): Kπaxis (LedgerL1 s 0 a b) (LedgerL1 t 1 c d) (LedgerL1 u 2 e f)=(if s=t ∧ t=u ∧ a=f ∧ b=c ∧ d=e then K*K*L else 0):=by
 let x:=apex; let y:= (2:ℝ) • apex; unfold Kπaxis LedgerL1; rw [LFla]; unfold RunF; change eye _ _ * eye _ _ * eye _ _+ eye _ _ * eye (apex- ((2:ℝ)•apex)) _ * eye (0-A) _ = _
 rw [show A - ((2:ℝ) • A) = -A from by rw[two_smul]; abel,show ((2:ℝ) • A)-A=A from by rw[two_smul]; abel]; simp only[sub_zero, zero_sub,AxisS_bvu,Twice_bvu,MinusS_bvu, Prod.mk.injEq,show (2:Generation)+1=0 from rfl,show (0: Generation)+1=1 from rfl,show (1: Generation)+1=2 from rfl,show ¬ ((0:Generation) =2) from (by decide),true_and,false_and,↓reduceIte,zero_mul, zero_add]
 split_ifs <;> first|(solve| ring)|grind
-- tune
#print axioms axis_vu
end LeftVU
end YM.GaugeFieldConstruction.Invoice.curvΝ
end
