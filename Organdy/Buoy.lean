import YM.SU5.Interaction.Title.Bonnet
import YM.SU5.Exchange.Seed.Station
import YM.SU5.Exchange.Pilot.Contour
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


variable {X Y:Aura n}{D:Support (More n)}{A B:Firing n}

lemma passport (u:Herb p q X h A a): Title p h (cipherK q) A X a:=
 ⟨u.body,u.offer,fun Y g i v j=> (u.clean Y g i v j).symm,u.price⟩

lemma shove (w:BirthRight p h A X a)
    (v:∀ i:Orbit n,i.1∈σX p X ∅ → rind (A i)=rind (B i)):
    BirthRight p h B X a:=by
  have u : BirthRight p h (B-A) X 0:=by
    apply BirthRight.void
    intro i u
    rw [← tileL,Pi.sub_apply,Sault.rind,map_sub]
    specialize v i u
    unfold Sault.rind at v
    rw [v,sub_self]
    -- goal acts 0 ...
    exact act_zero ..
  simpa only [sub_add_cancel,zero_add] using BirthRight.plus u w

lemma voyager (u:Flight p q X h A a b):
    Title p h (cipherK q) A X a ∧ BirthRight p h A X b:=by
  obtain ⟨W,r,t⟩:=u.forms
  exact ⟨passport u.tube,shove (BirthRight.whole (passport r)) fun i h=>(t X le_rfl i h).symm⟩

lemma voucher (u:Flight p q X h A a b) : 0 ≤ b:=by
  obtain ⟨W,r,_⟩:=u.forms
  exact r.price

def swipe (f:I→Bag n)(z:Key I) : Bag n := fun X=>∑ i:I,z i • f i X
def regatta (f:I→Aura n→ℝ)(z:Key I) : Aura n→ℝ := fun X=>∑ i:I,‖z i‖*(f i X)
abbrev trawling (f:I→Bag n)(z:Key I) := fun i X=>swipe f z X i

structure Pollen (p:BudgetPoint)(q:ℕ)(h:ℝ)(σ:I→Seat n)(V:I→Bag n)(a b:I→Aura n→ℝ):Prop where
 ticket:∀ i:I,∀ X:Aura n,Flight p q X h (V i X) (a i X) (b i X)
 port: ∀ i:I,∀ X:Aura n,σ i∉X.val → V i X=0

variable {a0 b0:I→Aura n→ℝ}{V:I→Bag n} {σ:I→Seat n}
variable (u:Pollen p q h σ V a0 b0)

include u

lemma Pollen.risent (z:Key I) (X:Aura n): Flight p q X h (swipe V z X)
    (regatta a0 z X) (regatta b0 z X):=
 Flight.whole univ _ _ _ fun i _=> (u.ticket i X).scR (z i)

lemma Pollen.vat (z:Key I) : Bias (cipherK q) (swipe V z) p h (regatta a0 z):=
 Title.powerQ _ _ fun X=>(voyager (u.risent z X)).1

def Pollen.soar (u:Pollen p q h σ V a0 b0)(z:Key I) : Rinse (Seat n) (Copy n):=
 (u.vat z).payX

omit u
lemma priceEq {r s:Aura n→ℝ} {z:Bag n} (v:Bias (cipherK q) z p h r)(w:Bias (cipherK q) z p h s): v.payX=w.payX:=by
  funext X D Y F
  unfold Bias.payX
  split
  · funext i; apply Subtype.ext; rfl
  rfl

include u
lemma Pollen.stock (v:3≤p.B)(t:0≤h) (z:Key I)(e:z∈ hill I):
    WickL p h (cipherK q) (u.soar z)
    (∑ i:I, a0 i) (∑ i:I,b0 i) (trawling V z) ∅:=by
  have ha(X):regatta a0 z X ≤ (∑ i:I, a0 i) X :=by
    rw [Finset.sum_apply]; exact sum_le_sum fun i _=>mul_le_of_le_one_left (u.ticket i X).tube.price (hill_i.mp e i)
  have hb(X):regatta b0 z X ≤ (∑ i:I,b0 i) X:=by
    rw [Finset.sum_apply]; exact sum_le_sum fun i _=>mul_le_of_le_one_left (voucher (u.ticket i X)) (hill_i.mp e i)
  have g(X):Flight p q X h (swipe V z X) ((∑ i:I, a0 i) X) ((∑ i:I,b0 i) X):=
    (u.risent z X).large_r t (ha X) (hb X)
  let tq:=fun X=>(voyager (g X)).1
  unfold Pollen.soar
  rw [priceEq (u.vat z) (Title.powerQ _ _ tq)]
  exact covenant v _ _ _ tq (fun X=>(voyager (g X)).2) t _ (by simp)

omit u
variable {r:Aura n→ℝ}{V0:Bag n}
def trans (w:Bias (cipherK q) V0 p h r)(X:Aura n)(D:Support (More n))(Y:Aura n):
    Copy n→ₗ[ℂ]Copy n:=⟨⟨w.payX X D Y,fun A B=>by
  unfold Bias.payX; split; swap; exact (zero_add _).symm
  funext a; apply Subtype.ext
  change Sault.rind (_ * ((A a).val + (B a).val)) =
   Sault.rind (_*_) + Sault.rind (_*_)
  rw [mul_add,Sault.rind,map_add]
  ⟩,fun c A=>by
  unfold Bias.payX; split; swap; exact (smul_zero _).symm
  funext a; apply Subtype.ext
  change Sault.rind (_ * (c • (A a).val)) = c • Sault.rind (_*(A a).val)
  rw [mul_smul_comm,Sault.rind,map_smul]⟩

include u

lemma Pollen.token (i:I) : Bias (cipherK q) (V i) p h (a0 i):=
 Title.powerQ _ _ fun X=>(voyager (u.ticket i X)).1

lemma Pollen.peony (z:Key I)(g:Bias.αt Y X D (cipherK q))(A:Copy n):
    u.soar z X D Y A = ∑ i:I,z i • (u.token i).payX X D Y A:=by
  funext a
  rw [Finset.sum_apply]
  apply Subtype.ext
  let f i := coll_T p X D (V i Y) a
  have t : coll_T p X D (swipe V z Y) a = ∑ i:I,z i • f i:=by
    unfold f coll_T; split
    · rw [swipe,Finset.sum_apply]; rfl
    simp only [smul_zero,sum_const_zero]
  rw [Pollen.soar,(u.vat z).truth X D Y A g a,t,Finset.sum_mul,Sault.rind,map_sum,
   show (∑ i:I, (z i • (u.token i).payX X D Y A) a).val= ∑ i:I, (z i • (u.token i).payX X D Y A a).val
      from map_sum (Dough (Dwell n)).val _ _]
  refine sum_congr rfl fun i _=>?_
  change Sault.rind ((z i • f i)* _) = z i • ((u.token i).payX X D Y A a).val
  rw [smul_mul_assoc, (u.token i).truth _ _ _ _ g _,Sault.rind,map_smul]

lemma Pollen.cardamom : Gamble u.soar:=by
  intro X D ht Y hg k f hv
  by_cases v:Bias.αt Y X D (cipherK q)
  · simp_rw [u.peony _ v]; apply Solvent.sum
    intro i _
    let F:=Solvent.map (trans (u.token i) X D Y) hv
    let M:Copy n→ₗ[ℂ]ℂ→ₗ[ℂ]Copy n:=LinearMap.flip (LinearMap.lsmul ℂ (Copy n))
    exact Solvent.pair M F (Solvent.bill i)
  simp_rw [Pollen.soar,Bias.payX,dif_neg v]
  exact Solvent.zero _

lemma Pollen.quietly (z w:Key I)
    (s:∀ i, σ i∈Y.val → z i=w i):
    u.soar z X D Y = u.soar w X D Y:=by
  have he : swipe V z Y= swipe V w Y:=by
    refine sum_congr rfl fun i _=>?_
    by_cases t:σ i∈Y.val
    · rw [s _ t]
    rw [u.port i Y t,smul_zero,smul_zero]
  by_cases v:Bias.αt Y X D (cipherK q)
  · funext F a; apply Subtype.ext
    rw [Pollen.soar,Pollen.soar,Bias.truth _ _ _ _ _ v,Bias.truth _ _ _ _ _ v,he]
  funext F
  simp only [Pollen.soar,Bias.payX,dif_neg v]

lemma Pollen.vacated : u.soar 0=fun _ _ _ _=>0:=by
  funext X D Y F
  by_cases v : Bias.αt Y X D (cipherK q)
  · rw [u.peony _ v]; simp
  rw [Pollen.soar,Bias.payX,dif_neg v]

def Palmlet (A:Copy n):Prop:=∀ v:Orbit n,∀ t:Ids n, A v = A (v.1,t)

lemma Pollen.peaceful (z:Key I)(X Y:Aura n)(F:Copy n)(r:Palmlet F):
    Palmlet (u.soar z X ∅ Y F):=by
  intro v t
  by_cases g:Bias.αt Y X ∅ (cipherK q)
  · apply Subtype.ext
    have he : coll_T p X ∅ (swipe V z Y) v = coll_T p X ∅ (swipe V z Y) (v.1,t):=by
      unfold coll_T
      dsimp only
      split
      · rename_i h
        apply (u.risent z Y).tube.clean X g.1 (gloss p X ∅ v) _ t|>.symm
        exact ((pillar X.val (open_l p.threshold X.val ∅)).choose_spec.2 v.1).2 h
      rfl
    unfold Pollen.soar
    rw [Bias.truth _ _ _ _ _ g,Bias.truth _ _ _ _ _ g,r _ t,he]
  rw [Pollen.soar,Bias.payX,dif_neg g]; rfl

end YM.CF.Organdy
