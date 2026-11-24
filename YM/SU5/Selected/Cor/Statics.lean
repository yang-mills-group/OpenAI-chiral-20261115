import YM.SU5.Selected.Cor.Livery
import YM.SU5.Selected.Cor.Mints
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
namespace Bulb
set_option synthInstance.maxSize 24000
section peninsula
open Mint
attribute [local instance] opCStarAlgebra
variable {d t n:Type}[Fintype d][DecidableEq d][Fintype n][LinearOrder n] [Fintype t][DecidableEq t]
private abbrev Jg(i:d)(b:Bool): t ↪ Bool × d × t:=⟨fun x:t=>(b,i,x),fun x y e=> (Prod.mk.inj (Prod.mk.inj e).2).2⟩
private abbrev B(i: Bool × d) : Matrix (Bool × d × t) t ℂ:= mask (Jg i.2 i.1)
-- sums. use explicit multiplication specializing $yoke * (mask _)ᴴ`.
variable (F : d→ Bool → WRect n t) (i : Bool× d) (A : Mint.Pull n (d× t))
noncomputable def rosterG (n':Type)[Fintype n'](F:d→Bool→ WRect n' t) : WRect n' (Bool × d × t):= Matrix.of fun x u=> (F u.2.1 u.1 x u.2.2)
variable (p:d)(b:Bool)
lemma matr (i:d)(b:Bool){F':WRect n (Bool × d×t)} : (@HMul.hMul _ _ (Matrix n t ℂ) Matrix.instHMulOfFintypeOfMulOfAddCommMonoid F' (B (b,i)))= yoke F' i b:= rfl
lemma re_yoke : yoke (rosterG n F) p b = F p b:= by ext; rw [yoke_at]; rfl
lemma re_build : rosterG n (Mint.yoke A)=A:= by ext x ⟨b,i,j⟩; exact yoke_at .. -- defeq ledger
lemma rally (Y: Op n) : Y * rosterG n F=rosterG n (fun i b=> Y * F i b):= by
 -- manual proof
 ext x ⟨b,i,j⟩; change _=(Y*(F i b)) x j; rfl
lemma uncoil (A A': Mint.Pull n (d×t))(e:∀ (i:d) (b:Bool), yoke A i b=yoke A' i b): A=A':= by rw [←re_build A,←re_build A',funext (fun i=> funext (e i))]
lemma sovereign (Y : Finset n)(e : ∀ i b, Contained Y (yoke A i b)): Contained Y A:= by rw [← re_build A]; unfold Contained; rw [rally,show (fun i b=> cutM Y*yoke A i b)= Mint.yoke A from funext (fun i=>funext fun b=> e i b)]
lemma smallest (Y:Op n)(e:∀ i b,Y*yoke A i b=yoke A i b): Y*A=A:=by apply uncoil _ _; intro i b; rw [yoke,Matrix.mul_assoc]; exact e i b
private lemma fine_yoke (X:WRect n t) (b':Bool)(x:d)(k:Bool)(i:d)(j:t)(a:n): (@HMul.hMul _ _ (Matrix n _ ℂ) Matrix.instHMulOfFintypeOfMulOfAddCommMonoid X ((B (b',x))ᴴ)) a (k,(i,j)) = if i=x ∧ k=b' then X a j else 0:=by
 rw [Matrix.mul_apply]; simp [B,Jg,mask, Matrix.conjTranspose_apply,apply_ite,mul_ite]; by_cases a:i=x <;> by_cases h:k=b' <;> simp [a,h] -- tune sums
lemma tallies {H:ℝ}(h:0≤H)(p:∀ i b, ‖yoke A i b‖≤ H): ‖A‖ ≤ ((2*Fintype.card d:ℕ):ℝ)*H:=by
 let R(i:Bool × d):= @HMul.hMul _ _ (Matrix n _ ℂ) Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (yoke A i.2 i.1) ((B i)ᴴ)
 have he: A=∑ i,R i:=by
    ext x ⟨b,i,j⟩; rw [Matrix.sum_apply,sum_eq_single (b,i)]; unfold R; rw [fine_yoke]; simp only [and_self,ite_true]; exact (yoke_at ..).symm
    · rintro ⟨b',i'⟩ u t; unfold R; rw [fine_yoke,if_neg ?_]; exact fun g=>t (Prod.ext g.2.symm g.1.symm)
    simp
 nth_rw 1 [he]; apply (norm_sum_le ..).trans; calc
    _ ≤ ∑ _i:Bool× d,H:= sum_le_sum fun i u=>by unfold R; exact ((charge_mul (p ..) ( (Matrix.l2_opNorm_conjTranspose ..).trans_le (mask_toll _ (Jg i.2 i.1).injective) )).trans_eq (mul_one _))
    _ = _:=by simp -- tune
end peninsula
namespace Mezz
open Payroll Caste Silks Mint
local notation "ⅈ" => Complex.I
variable {N:Side}{T:Type}[Fintype T][DecidableEq T] (P:Mezz)(A:Society T)
local notation "N₂" => More N
local notation "P'" => P.beams
local notation "W" i:max => WRect i A.Club
local notation "S" => park N P.Broad
variable (i:P.Lot)(b:Bool)(k:Bool)
local notation "Ω" => wrap N₂ (P.grape i.1 b)
local notation "Κ" => park N (P.yard i.1 b)
-- supply rods X (true,lower), ZV (false, visible). Includes SpinR, budgets.
variable (X Z:Coast→ Wq P.marks) (C:ℝ)
local notation "A'" => P.dart A N X
local notation "V'" => P.dart A N Z
local notation "h" b:max => hand b (cutM (Tset N)) -- remove before variable h
local notation "r" => P.cork A N i
local notation "↑X" => design (Ro N) (A') (lowerP C)
local notation "↑Z" => design (Ro N) (V') (upperP C)
def Front (i:P.Lot)(b k:Bool): W (Single N):= if b then yoke (P.dart A N X) i k else (hand false (cutM (Tset N)))* yoke (P.dart A N Z) i k -- avoid binder
lemma frontX: Front P A X Z i true k=(r k A'):=rfl
lemma frontZ: Front P A X Z i false k= h false * r k V':= rfl
def sizeW (C:ℝ)(b: Bool):= if b then lowerP C else upperP C
local notation "s₁" => (sizeW C b)
noncomputable def pole (Z':Pane N):= P.spangle A i b (P.Front A X Z i b k) (sizeW C b) Z'
#print pole
local notation "p₁" U:max => P.pole A i b k X Z C U

-- easier Custline argument explicit proofs
variable {ε:ℝ}{t:ℕ}{M:Tulip.Male}(u:Caste (N:=N) P M C ε t X Z)
include u
lemma budgets (V:P.Fish A N): ‖r k V‖ ≤ ‖V‖:= portion_le _ _ (show Injective (fun j:A.Club=>(k,i,j)) from (Jg i k).injective)
local notation "F" i:max b:max k:max => (Front (N:=N) P A X Z i b k)
lemma lobby : Contained (modesIn N (Κ)) (F i b k):= by cases b; exact u.stage_v P A i k; exact u.stage_x P A i k
lemma tripoli : h b*F i b k=F i b k:= by
 cases b; · rw [frontZ, ←Matrix.mul_assoc, (raft false (cutM_idp ..)).isIdempotentElem];
 rw [frontX]; unfold cork; rw [←Matrix.mul_assoc,u.skates P A]
lemma youngster : ‖F i b k‖≤ C:=by
 cases b; · rw [frontZ]; exact bound_shift (raft false (cutM_idp ..)) ((budgets _ _ _ _ _ _ _ u _).trans (u.volume_pay P A).cost) -- check args
 exact (budgets _ _ _ _ _ _ _ u _).trans (u.volume_pay P A).tribute
lemma talent (Z':Pane N): Contained (modesIn N (Κ)) (p₁ Z'):= P.spangle_hold A i b _ _ (P.yard i.1 b) (lobby P A i b k X Z C u) (P.yard_spin _ _ _ (by decide)) (P.yard_spin _ _ _ (by decide)) Z'
lemma youth (f:1≤C)(Z':Pane N): ‖p₁ Z'‖≤ (sizeW C b)*2*C:= P.spangle_size A i b _ _ (youngster P A i b k X Z C u) (by have f:0<C:=(by linarith); unfold sizeW Caste.lowerP Caste.upperP tollS; cases b <;> simp <;> positivity) _
lemma fashion : Continuous (P.pole (N:=N) A i b k X Z C) := P.spangle_c ..
lemma aura (p q:Pane N) (x:Agrees (Κ) p q): (p₁ p)=(p₁ q):= P.spangle_dep A i b _ _ u (lobby _ _ _ _ _ _ _ _ u) p q x
lemma pole_x (Z':Pane N): (h b) * p₁ Z'= p₁ Z':= P.spangle_section A _ _ _ _ (tripoli _ _ _ _ _ _ _ _ u) _
lemma pole_roll (Z':Pane N): (Ro N).val * p₁ (swoop Z')= ⅈ • p₁ Z':= P.spangle_r ..
lemma whipping (η:ℝ) (f:1≤C)(g:0 ≤ η) (Z':Pane N)(v:Rightful S Z' 1 η): ‖p₁ Z'- p₁ 1‖ ≤ sizeW C b*2*((8*P.beams*η)* C):= by unfold pole; rw [blankH]; have ht:0<C:=zero_lt_one.trans_le f; refine sparkle_bill P A _ _ _ _ u (lobby _ _ _ _ _ _ _ _ u) g ?_ (youngster _ _ _ _ _ _ _ _ u) _ v; unfold sizeW Caste.lowerP Caste.upperP tollS; cases b<;> simp <;> positivity
lemma polo (g: Seat N→SU.E)(Z':Pane N): p₁ (gauge g Z') * (A.arm (g Ω)).val= (tradew N g).val * p₁ Z':= by
 apply spangle_gauge; intro x; cases b; · rw [frontZ, peels_m _ (h false) (tradew N (fun _=>x)) (by rw [handAgainst,gauge_frostT]), P.spirits,Matrix.mul_assoc]; -- tune
 exact P.spirits ..
-- blank: full array via rosterG. below.
omit u
lemma design_taken (V:P.Fish A N) (Z: Op (Single N))(T:UNI (Single N))(p:Commute Z T.val): design T (Z * r k V) C = Z * r k (design T V C):= by rw [←designing T Z p]; unfold design cork; simp only [Matrix.smul_mul,Matrix.sub_mul,Matrix.mul_assoc]
lemma blank_poleX: P.pole A i true k X Z C (1:Pane N)= r k (↑X):= by unfold pole; rw [blankH,frontX]; unfold design cork; rw [Matrix.smul_mul,Matrix.sub_mul,Matrix.smul_mul,Matrix.mul_assoc]; rfl -- defeq size
lemma blank_poleY: P.pole A i false k X Z C (1:Pane N)= h false * r k (↑Z):= by
 unfold pole; rw [blankH,frontZ]; apply design_taken; change _*_=_; exact (congrArg (fun X: Op _=> X*(Ro N).val) (Ro_angle (N:=N) false).symm).trans (twist_product ..)
end Mezz
end Bulb
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern.Bulb
#print axioms Mezz.whipping
#print axioms tallies
#print axioms Mezz.polo
