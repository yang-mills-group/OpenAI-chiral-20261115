import YM.SU5.Exchange.Pilot.Contour
import YM.CF.Mew.Pot
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
open Hake Jet Sault Stax Sour
attribute [local instance] Sour.loreM Sour.loreN
open Rill Branch Tenant Drapes Leaf


/- API: one funded seed. how it acts on incoming dictionary on FINAL Ti.
  tag independence at no flag, witness even with any reopened flag.
 -/
variable {n:Side} {P:BudgetPoint} {q:ℕ}{h:ℝ}{X Y:Aura n}{D:Support (More n)}
variable {v w: Sour.Bag n}{c r:Aura n→ℝ}

abbrev Canopy (P:BudgetPoint)(q:ℕ)(h:ℝ)(v:Sour.Bag n)(c:Aura n→ℝ):Prop:=
  ∀ X,Herb P q X h (v X) (c X)
lemma asBias (f: Canopy P q h v c):Bias (cipherK q) v P h c:=⟨fun i=> (f i).body,fun i=>(f i).price,fun X Y D u d t=> (f Y).offer X u D d t⟩
abbrev lamp (f: Canopy P q h v c):=(asBias f).payX

abbrev litCan (P:BudgetPoint)(q:ℕ)(X:Aura n)(D:Support (More n))(Y:Aura n)(i:Orbit n):Prop:=
  Bias.αt Y X D (cipherK q) ∧ Gates (σX P X D) X.val i.1

lemma lampPoint (f:Canopy P q h v c)(X:Aura n)(D:Support (More n))(Y:Aura n)
   (V:Copy n)(i:Orbit n):
 (lamp f X D Y V i).val=
   if litCan P q X D Y i then
     Sault.rind (v Y (gloss P X D i) * (V i).val)
   else 0:= by
 by_cases k:Bias.αt Y X D (cipherK q)
 · rw [(asBias f).truth X D Y V k]; unfold litCan; rw [coll_T, if_congr (and_iff_right k) rfl rfl]; split_ifs
   · rfl
   rw [zero_mul,Sault.rind,map_zero]
 have z:lamp f X D Y V=0:=by rw [lamp,Bias.payX,dif_neg k]
 rw [z,if_neg (fun h=>k h.1)]
 rfl

lemma lampOff (f:Canopy P q h v c)(X:Aura n)(D:Support (More n))
 (Y:Aura n)(k:v Y=0)(V:Copy n):lamp f X D Y V=0:=by
 funext i; apply Subtype.ext
 rw [lampPoint]
 split_ifs
 · rw [k,Pi.zero_apply,zero_mul,Sault.rind,map_zero]; rfl
 rfl

open scoped YM.CF.Mew
lemma bread_c {n:Side} (z:ℂ) (v:Cipher n): ((z • v):Cipher n).val=z • v.val:=rfl
-- linear motion

variable (f:Canopy P q h v c)
def linearLamp (f:Canopy P q h v c)(X:Aura n)(D:Support (More n))(Y:Aura n) :
 Copy n→ₗ[ℂ]Copy n where
 toFun:=lamp f X D Y
 map_add' V W:=by
   funext i; apply Subtype.ext
   change (lamp f X D Y (V+W) i).val =
     (lamp f X D Y V i).val+(lamp f X D Y W i).val
   simp only [lampPoint]
   split
   · rw [Pi.add_apply,Subalgebra.coe_add,mul_add,Sault.rind,map_add]
   simp
 map_smul' y V:=by
   funext i; apply Subtype.ext
   change (lamp f X D Y (y•V) i).val = y • (lamp f X D Y V i).val
   simp only [lampPoint]
   split
   · rw [Pi.smul_apply,bread_c,Algebra.mul_smul_comm,Sault.rind,map_smul]
   simp
-- Q needed for turns; Turf adapter
abbrev Leaseless (F:Copy n):Prop := ∀ (V:Orbit n)(A:Ids n), F V=F (V.1,A)
lemma lampLease (X Y:Aura n)(V:Copy n)(hV:Leaseless V):
 Leaseless (lamp f X ∅ Y V):=by
 intro i t
 apply Subtype.ext
 rw [lampPoint,lampPoint]
 by_cases hp:litCan P q X ∅ Y i
 · rw [if_pos hp,if_pos (show litCan P q X ∅ Y (i.1,t) from hp)]
   obtain ⟨k,e⟩:=hp
   have hs:= (pillar (G:=SU.group) X.val (open_l P.threshold X.val ∅)).choose_spec.2 i.1

   have ht:= ((f Y).clean X k.1 (gloss P X ∅ i) (hs.2 e) t)
   rw [←ht,hV i t]
 rw [if_neg hp,if_neg (show ¬litCan P q X ∅ Y (i.1,t) from hp)]

-- special birth (D=∅,V=1) case
abbrev Orchard (P:BudgetPoint)(q:ℕ)(h:ℝ)(v:Sour.Bag n)(c r:Aura n→ℝ):Prop:=
   ∀ X,Flight P q X h (v X) (c X) (r X)
namespace Orchard
variable (z:Orchard P q h v c r)
lemma fullUp (z:Orchard P q h v c r):Canopy P q h v c:=fun i=>(z i).tube
abbrev hyp (z:Orchard P q h v c r):= lamp z.fullUp
abbrev budL (z:Orchard P q h v c r)(X:Aura n):Copy n:= hyp z X ∅ X 1
lemma budLease (z:Orchard P q h v c r)(X:Aura n):Leaseless (budL z X):=
 lampLease z.fullUp X X 1 (fun _ _=>rfl)
lemma up (z:Orchard P q h v c r)(B:3≤P.B)(w:0≤h):
 Pitch P h (cipherK q) z.hyp c (fun i Y=> v Y i):=(asBias z.fullUp).buys B w
lemma budFray (B:3≤P.B)(hw:0≤h)(X:Aura n):Fray P h (cipherK q) X ∅ (budL z X) (r X):=by
 have hx(Y):= (z Y).forms
 choose m R k using hx
 have ho:Canopy P q h m r:=R

 have hh:= ((asBias ho).buys B hw).plays X ∅ (empty_subset _) X le_rfl 1 1
   (show Fray P h (cipherK q) X ∅ 1 1 from ⟨Medal.oneT,fun i x=>by simp [Lattice.halo]⟩)
 have eq:budL z X= lamp ho X ∅ X 1:=by
    funext i; apply Subtype.ext
    rw [budL,hyp,lampPoint,lampPoint]
    split
    · rename_i t
      have hs:= (pillar (G:=SU.group) X.val (open_l P.threshold X.val ∅)).choose_spec.2 i.1
      have he:= k X X le_rfl (gloss P X ∅ i) (hs.2 t.2)
      simpa only [Pi.one_apply,Subalgebra.coe_one,mul_one] using he
    rfl
 rw [eq]
 rw [mul_one] at hh;exact hh

end Orchard

def riseV {J:Type*}[Fintype J] (v:J→Sour.Bag n)(z:Mew.Key J): Sour.Bag n:=fun X i=>∑ j, z j • (v j X i)
abbrev riseF {J:Type*}[Fintype J](c:J→Aura n→ℝ): Aura n→ℝ:=fun X=>∑ j,c j X
lemma valSum_b {J:Type*}(S:Finset J)(f:J→Cipher n):(∑ i∈S,f i).val=∑ i∈S,(f i).val:=
 map_sum (Cipher n).val (M:=Cipher n) f S -- ↑? val subtype_alg to FC 
section
variable {J:Type*} [Fintype J][LinearOrder J]
 {m:J→Sour.Bag n}{Q R:J→Aura n→ℝ}
lemma orch_rise (p:∀ i,Orchard P q h (m i) (Q i) (R i))
  (hw:0≤h)(z:Mew.Key J)(k:z∈Mew.hill J):
  Orchard P q h (riseV m z) (riseF Q) (riseF R):=by
 have hz(i:J): ‖z i‖≤1:=(norm_le_pi_norm z i).trans (mem_closedBall_zero_iff.mp k)
 intro X
 let v(j):=z j • m j X
 have hg:(riseV m z) X=∑ i, v i:=by funext i; unfold riseV; rw [Finset.sum_apply];rfl
 rw [hg]

 exact Flight.whole univ v _ _
   (fun i _ => ((p i X).scR (z i)).large_r hw
     (mul_le_of_le_one_left (p i X).tube.price (hz i))
     (mul_le_of_le_one_left (p i X).forms.choose_spec.1.price (hz i)))

lemma hyp_rise (p:∀ i,Orchard P q h (m i) (Q i) (R i))
 (hw:0≤h)(z:Mew.Key J)(k:z∈Mew.hill J)
 (X:Aura n)(D:Support (More n))(Y:Aura n)(V:Copy n):
 (orch_rise p hw z k).hyp X D Y V=∑ i,z i • (Orchard.hyp (p i) X D Y V):=by
 funext u; apply Subtype.ext
 rw [Finset.sum_apply,Orchard.hyp,lampPoint,valSum_b]
 simp only [Pi.smul_apply,bread_c,Orchard.hyp,lampPoint]
 split
 · rw [riseV,sum_mul,Sault.rind,map_sum]
   simp_rw [Algebra.smul_mul_assoc,map_smul]
 simp
end
end YM.CF.Bay
