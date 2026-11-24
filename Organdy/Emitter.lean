import Organdy.Perch
import YM.SU5.Exchange.Seed.Pip
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Lattice Fock Sour Pastry Scree Skye Cadre Vow Palot Rue Sault Stax Rush Scroll Finset RG
open Cube Rill Mew Ione Bake Rive Vow.TreasuryFog Metric
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator Mew
attribute [local instance] opCStarAlgebra
variable {n:Side} {p:BudgetPoint} {h a b c d:ℝ}{q:ℕ} {I : Type} [LinearOrder I] [Fintype I]

open Neon
variable {σ:I→Seat n}{V:I→Bag n}{A B:I→Aura n→ℝ}
variable (t:Pollen p q h σ V A B) (i:I)
abbrev pendulum (X:Aura n) := (t.token i).payX X ∅ X 1
local notation "f'" => pendulum t
local notation "pull" => t.soar

lemma lurch (X:Aura n)(z:Key I)(x:Orbit n):
    pull z X ∅ X 1 x=∑ i:I,z i • f' i X x:=by
  by_cases u:Bias.αt X X ∅ (cipherK q)
  · rw [t.peony _ u,Finset.sum_apply]; rfl
  simp only [pendulum,Pollen.soar,Bias.payX,dif_neg u,Pi.zero_apply,smul_zero,sum_const_zero]

lemma rhyme (X:Aura n)(x:Orbit n):
   tipI (fun z:Key I=>pull z X ∅ X 1 x) [i]= f' i X x:=by
   simp_rw [lurch]
   exact sTip .. -- inference

lemma circle (X:Aura n):
   Palmlet (f' i X):=by
    intro x τ
    rw [←rhyme,←rhyme]
    apply congrArg (tipI · [i])
    funext z
    exact t.peaceful z X X 1 (fun _ _=>rfl) x τ
lemma vanity {X:Aura n}(w:V i X=0) : f' i X=0:=by
   unfold pendulum
   by_cases u:Bias.αt X X ∅ (cipherK q)
   · funext v; apply Subtype.ext
     rw [(t.token i).truth _ _ _ _ u]
     have z:coll_T p X ∅ (V i X) v=0:=by
        rw [w]
        unfold coll_T; split <;> rfl
     rw [z,zero_mul,Sault.rind,map_zero];rfl
   rw [Bias.payX,dif_neg u]
lemma 
bud (X:Aura n)(d:3≤ p.B)(u:0≤h):
    Medal p X.val ∅ (f' i X) h (B i X):=
   ((covenant d (V i) (A i) (B i)
     (fun x=>(voyager (t.ticket i x)).1)
     (fun x=>(voyager (t.ticket i x)).2)
     u ∅ (by simp)).birth X).merit

def flake (X:Scree.Hub n):InkD n:= fun U=>
    f' i (lagE X) (U,Classical.arbitrary _)
def pend (t:Pollen p q h σ V A B)(i:I):RegBudget n:=
   fun X=> if X.val.1=σ i then flake t i X else 0
lemma opening (τ:Ids n): SpanTip p (pend t i) (σ i) t.soar τ i:=by
    refine ⟨fun X U l=>?_,fun X U l r=>?_⟩
    · unfold pend flake
      split
      · rw [rhyme]
        exact circle t i _ (U,_) τ
      rfl
    rw [rhyme,vanity _ _ (t.port i _ r)]
    rfl
open Nor Hope

abbrev snapshot (p:BudgetPoint)(X:Support (More n))(a:ℝ) :=
   fareX p.B p X*a
abbrev hoard (p:BudgetPoint) :=
   reserveT p.power p.order p.B (biscuit p)
abbrev spending (p:BudgetPoint)(a:ℝ) := hoard p * a
lemma hoard_zero : 0≤ hoard p:=by
   have hb:biscuit p>0:= biscuit_pos
   unfold hoard reserveT coin_n stilK
   positivity

lemma receive (d:3≤p.B)(u:0≤h)
    (x:Scree.Hub n): PressB p x (pend t i x) h (snapshot p x.val.2 (B i (lagE x))):=by
   have hh: oV (flake t i x)=f' i (lagE x):=
      funext fun v=>(circle t i _ v _).symm
   unfold pend
   split
   · exact (show Medal p x.val.2 ∅ (oV (flake t i x)) h (B i (lagE x)) from hh.symm ▸
     (bud t i (lagE x) d u)).preservesE (Classical.arbitrary _) u _
   have he:0 ≤ snapshot p x.val.2 (B i (lagE x)):=mul_nonneg (health_f ..)
     (voucher (t.ticket ..))
   exact hi_p (Vale.rinse x _ _) he

lemma snapshots {v:Aura n→ℝ} (d:0≤v) (g:voyageB v p.B (highLaunch p) ≤b)
   (x:Seat n):
    (∑ i:Scree.Hub n, if x=i.val.1 then p.mass i.val.2 (snapshot p i.val.2 (v (lagE i))) else 0) ≤ spending p b:=by
   let W:=(univ:Finset (Scree.Hub n)).filter fun i=>x=i.val.1
   have hw:Set.InjOn lagE W:=fun i h j h' e=> Subtype.ext (Prod.ext
      ((mem_filter.mp (h:i ∈ W)).2.symm.trans (mem_filter.mp (h':j ∈ W)).2) (congrArg Subtype.val e))
   refine le_trans ?_ (mul_le_mul_of_nonneg_left g hoard_zero)
   rw [←sum_filter,voyageB,mul_sum]
   let s:= W.image lagE
   refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg (subset_univ s) (fun i _ _=>
     mul_nonneg hoard_zero (mul_nonneg (d i) (Real.exp_pos _).le)))
   unfold s;rw [sum_image hw]
   refine sum_le_sum fun i hi=>?_
   have hb:biscuit p >0:=biscuit_pos

   have hp:=Nor.coinPay (k:=p.B) p i.val.2 (biscuit p) hb
   let y:=p.supportExponent
   let a:=coverNumber p.B i.val.2
   let z:=v (lagE i)
   change Real.exp (y*a) * (fareX p.B p i.val.2 * z) ≤ 
     hoard p * (z * Real.exp ((y+8*biscuit p)*a))
   refine le_trans ?_ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
        (show y+biscuit p≤y+8*biscuit p by linarith) (Nat.cast_nonneg _))) (d _)) hoard_zero)
   exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp (d (lagE i))) (Real.exp_pos (y*a)).le).trans_eq
    (by rw [add_mul y,Real.exp_add]; unfold hoard a z; ring)

variable (w:Tine p q h σ V A B a b)
lemma speckles (d:3≤p.B)(u:0≤h):
   IncX Py.primeU (pend w.toPollen i) p h (spending p b):=
   ⟨⟨fun X=>snapshot p X.val.2 (B i (lagE X)),receive w.toPollen i d u, 
       snapshots (fun _=>earring w i) (w.priceB i)⟩,fun _ x=>x.elim⟩

lemma horn {N B₁:Side}{M:ℕ}{V:I→Bag (mid N B₁)}
   (o:I→Site (mid N B₁))
   {A B:I→Aura (mid N B₁)→ℝ}
   (w:Tine p q h (node ∘ o) V A B a b)
   (d:3≤p.B)(u:0≤h)
   (f:Pavilion M p (V i)):
   Axon M (o i) p (pend w.toPollen i) h (spending p b) 0:=by
   refine ⟨speckles i w d u,fun X he=> if_neg he,?_⟩
   intro X g
   have z:pend w.toPollen i X=0:=by
     unfold pend; split
     · funext 
       simp only [Pi.zero_apply,flake, vanity _ _ (f (lagE X) g)]
     rfl
   rw [z,Pill_0,ite_self]
   exact ⟨rfl,rfl⟩
