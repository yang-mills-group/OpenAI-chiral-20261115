import Merino.Corolla.Character

set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 140000
noncomputable section
namespace YM.CF.Merino.Corolla
open Finset Lattice RG Scree Skye Vow
open scoped Topology Classical Matrix Matrix.Norms.L2Operator
open Cadre Sour Push.AbsoluteSums.Trees Vow.TreasuryFog
open Cube Stax Mew Fock
open scoped YM.CF.Mew

variable {I:Type}[LinearOrder I][Fintype I]
variable {n:Side}{P:BudgetPoint}{q:ℕ}{h:ℝ}

open Rill Rue
structure Sep (P:BudgetPoint)(q:ℕ)(h:ℝ)(σ:I→Seat n)(y:I→Bag n)(c d:I→Aura n→ℝ) : Prop where
 fire:∀ i X, Flight P q X h (y i X) (c i X) (d i X)
 far:∀ i X, σ i∉X.val→ y i X=0

def meterZ (u:I→Aura n→ℝ): Aura n→ℝ:= fun X=> ∑j,u j X
def impression(y:I→Bag n)(a:Key I):Bag n:= ∑j,a j • y j
abbrev scores(y:I→Bag n):Key I→Orbit n→Aura n→ FC (Dwell n):=fun a V Y=> impression y a Y V
def ounces(u:I→Aura n→ℝ)(a:Key I) (X:Aura n):ℝ:= ∑j,‖a j‖*u j X
namespace Sep
variable {σ:I→Seat n}{y:I→Bag n}{c d:I→Aura n→ℝ}
variable (k:Sep P q h σ y c d)
local notation "δ"=> cipherK q
include k
lemma sign (i:I)(X:Aura n):0≤c i X ∧ 0≤d i X:=
  let ⟨_,u,_⟩:=(k.fire i X).forms
  ⟨(k.fire i X).tube.price,u.price⟩
lemma biasH(i:I) : Bias δ (y i) P h (c i):=
 ⟨fun X V=> (k.fire i X).tube.body V, fun X=> (k.sign i X).1,
   fun _ Y _ p q r=>(k.fire i Y).tube.offer _ p _ q r⟩


variable (a:Key I)
lemma kick(X:Aura n): Flight P q X h (impression y a X) (ounces c a X) (ounces d a X):=by
   unfold impression ounces; rw [Finset.sum_apply]
   exact Flight.whole _ _ _ _ (fun j _=> (k.fire j X).scR _)

lemma bias : Bias δ (impression y a) P h (ounces c a):=
 ⟨fun X V=>(k.kick a X).tube.body V,fun X=>(k.kick a X).tube.price,
    fun _ Y _ r s u=> (k.kick a Y).tube.offer _ r _ s u⟩
abbrev stripe : Rinse (Seat n) (Copy n):=(k.bias a).payX

lemma weights(g:a∈hill I)(v:0≤h)(X:Aura n):Flight P q X h (impression y a X) (meterZ c X) (meterZ d X):=by
 have ha:=mem_closedBall_zero_iff.mp g
 exact (k.kick a X).large_r v
  (sum_le_sum fun i _=> mul_le_of_le_one_left (k.sign i X).1 ((norm_le_pi_norm a i).trans ha))
  (sum_le_sum fun i _=> mul_le_of_le_one_left (k.sign i X).2 ((norm_le_pi_norm a i).trans ha))


lemma staged(g:a∈hill I)(v:0≤h)(w:3≤P.B):
 Pitch P h δ (k.stripe a) (meterZ c) (scores y a) ∧ 
 ∀ X:Aura n, Fray P h δ X ∅ (k.stripe a X ∅ X 1) (meterZ d X):=by
 have t:=weights k a g v
 have A:Bias δ (impression y a) P h (meterZ c):=
   ⟨(k.bias a).valid,fun X=>(t X).tube.price,fun _ Y _ r s u=> (t Y).tube.offer _ r _ s u⟩
 exact ⟨A.buys w v,fun X=>beer X A (d:=meterZ d) (t X) v w⟩


lemma stripe_formula (X D Y F):
 k.stripe a X D Y F=∑j,a j • (k.biasH j).payX X D Y F:=
    matrix_ramp X D Y (k.bias a) k.biasH a rfl F
lemma gam: Gamble k.stripe:= by
 intro X D _ Y _ i F g; simp_rw [stripe_formula]
 apply Solvent.sum
 intro j _
 let L:=machine X D Y (k.biasH j)
 rw [add_comm i]
 exact Solvent.pair (LinearMap.lsmul ℂ (Copy n)) (Solvent.bill j) (Solvent.map L g)

lemma plain (F:ForceBudget n)(m:ℕ):
 Bake.Turf (fun i:Aura n=> layerN (settleK F) (k.stripe a) m i ∅):=by
 intro X V A; dsimp only; unfold layerN; simp only [Finset.sum_apply]
 exact sum_congr rfl fun _ _=> Stax.clean_p (settleK F) _ V (k.bias a)
   (fun i j y=>(kick k a i).tube.clean j y) A
   (fun i=>by rw [settle0]; rfl) X _

lemma back (j:I)(X D Y)(F:Copy n)(p:σ j∉Y.val):
 (k.biasH j).payX X D Y F=0:=by
 by_cases q':Bias.αt Y X D δ; swap; exact dif_neg q'
 funext i; apply Subtype.ext
 rw [(k.biasH j).truth _ _ _ _ q', k.far _ _ p]
 simp [coll_T,Sault.rind]

open PowerSeries
variable(F:ForceBudget n)
local notation "R:"a:max=> Cadre.chip (stripe k a) (settleK F)
lemma require (b:Key I)(i:ℕ)(X:Aura n)(D:Support (More n))(p:∀i, σ i ∈ X.val→a i=b i): coeff i ((R:a) X D)=coeff i ((R:b) X D):=by
 induction i using Nat.strong_induction_on generalizing X D with
 | h i ih=>
   cases i with
   |zero=> rw [Cadre.peg,Cadre.peg]
   |succ i=>
     nth_rw 1 [Cadre.peel]; nth_rw 1 [Cadre.peel D (k.stripe b)]
     rewrite [sprig,sprig,Cadre.ore,Cadre.ore]
     apply congrArg (fun e:Copy n=> ((↑i:ℝ)+1)⁻¹ • e); apply sum_congr rfl; intro Y _
     apply sum_congr rfl
     intro G t
     have w(Y:Aura n)(v:Y∈G):Y.val⊆ X.val:= (coneL v).trans (by rw [(Cadre.drum_p ..|>.mp t).2.2]; exact subset_union_right) -- Y shadows
     have hv:Y.val⊆ X.val:= by rw [(Cadre.drum_p ..|>.mp t).2.2]; exact subset_union_left
     have q:coeff i (∏j∈G,(R:a) j (D∩j.val))=coeff i (∏j∈G,(R:b) j (D∩j.val)):=by
       rewrite [coeff_prod,coeff_prod]
       refine sum_congr rfl fun u h=>prod_congr rfl fun j g=>ih _ (Nat.lt_succ_of_le ((single_le_sum (fun j _=>Nat.zero_le (u j)) g).trans_eq (mem_finsuppAntidiag.mp h).1)) _ _ fun r v=>p _ (w j g v)

     rewrite [q,stripe_formula,stripe_formula]
     apply sum_congr rfl; intro j _
     by_cases g:σ j∈Y.val
     · rw [p j (hv g)]
     rw [back k j X D Y _ g,smul_zero,smul_zero]

lemma turn (u:ℕ)(X:Aura n)(D:Support (More n)):
 Rive.Hush σ X.val (fun a=> layerN (settleK F) (k.stripe a) u X D):= by
 intro a _ b _ g
 exact sum_congr rfl fun i _=> k.require _ F _ i X D g

lemma void (u:ℕ): layerN (settleK F) (k.stripe 0) u=settleK F:=by
 funext X D; unfold layerN
 rw [sum_eq_single_of_mem (0:ℕ) (mem_range.mpr (by omega)),Cadre.peg]
 intro i _ g; obtain (_|i):=i; contradiction
 nth_rw 1 [Cadre.peel]
 rw [sprig,Cadre.ore]; simp [stripe_formula] 
end Sep
end YM.CF.Merino.Corolla
