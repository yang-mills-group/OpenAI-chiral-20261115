import Bay.Arbor
import YM.SU5.Exchange.Seed.Keys
import YM.CF.Rive.Silk
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
open Mew PowerSeries
open scoped YM.CF.Mew
variable {n:Side} {P:BudgetPoint}


variable {I : Type}[LinearOrder I][Fintype I]
variable {q:ℕ}{h:ℝ} {m:I→Sour.Bag n}
  {c r: I→Aura n→ℝ}(p:∀ i,Orchard P q h (m i) (c i) (r i))
  
/-- The Key-infinitesimal actuation, evaluated layout-restricted or at a
 single pin as required. At unset pin this is ordinary 0, not a projected Reading. -/
def flare (p:∀ i,Orchard P q h (m i) (c i) (r i)) (z: Key I) :
 Rinse (Seat n) (Copy n):=
 fun X D Y V=>∑ i,z i • (Orchard.hyp (p i) X D Y V)

/-- Exposed sum used in Pitch, given the election's actual mark actions V i:
 concreteTip uses ∑Y (flareM v z x Y) once per raw/U transform.-/
abbrev flareM (m:I→Sour.Bag n)(z:Key I)(u:Orbit n)(X:Aura n): FC (Dwell n):=
 (riseV m z) X u

lemma flarePrice(hw:0≤h)(W:3≤P.B)(z:Key I)(k:z∈hill I):
 Pitch P h (cipherK q) (flare p z) (riseF c) (flareM m z) ∧
 ∀ X,Fray P h (cipherK q) X ∅ (flare p z X ∅ X 1) (riseF r X):=by
 rw [show flare p z=(orch_rise p hw z k).hyp from Eq.symm (by funext X D Y V;exact hyp_rise p hw z k X D Y V)]

 exact ⟨Orchard.up _ W hw,Orchard.budFray _ W hw⟩
lemma flareGamble : Gamble (flare p):=by
 intro X D _ Y _ k V hy
 change Solvent (k+1) (fun z:Key I=>∑ i,z i • Orchard.hyp (p i) X D Y (V z))
 apply Solvent.sum
 intro i _
 let L:ℂ→ₗ[ℂ]Copy n→ₗ[ℂ]Copy n:= LinearMap.lsmul ℂ (Copy n)
 have t:= Solvent.pair L (Solvent.bill i) (Solvent.map (linearLamp (p i).fullUp X D Y) hy)
 rw [Nat.add_comm];exact t

-- general layer API: empty, turf, turns
abbrev Blaze (I:Type)(n:Side):= Key I → Rinse (Seat n) (Copy n)
lemma sunrise (S: Aura n→Support (More n)→ Copy n)(K:Rinse (Seat n) (Copy n))
   (X:Aura n)(D:Support (More n))(i:ℕ):
 let L(_Y:Aura n)(G:hook (Seat n)):=∏ j∈G, Cadre.chip K S j (D∩j.val)
 coeff (i+1) (Cadre.chip K S X D)=
   ↑((↑(i+1:ℕ):ℝ)⁻¹) • (∑ Y,∑ G∈drum X Y D,K X D Y (coeff i (L Y G))):=by
 -- use Complex
 dsimp only; rw [←ore] -- tune
 nth_rw 1 [Cadre.peel]
 rw [Cadre.sprig,Nat.cast_add,Nat.cast_one]

lemma peelTurns (S: Aura n→Support (More n)→ Copy n)
  (σ:I→Seat n)(K:Blaze I n)
  (y:(∀ V X D Y,Rive.Hush σ Y.val (fun z=> K z X D Y V)))
  (t:ℕ)(X:Aura n)(D:Support (More n)):
 Rive.Hush σ X.val (fun z=> layerN S (K z) t X D):=by
 have aux:(∀ k (X:Aura n)(D:Support (More n)),Rive.Hush σ X.val
   (fun z=>coeff k (Cadre.chip (K z) S X D))):=by
    intro k
    induction k using Nat.strong_induction_on with
    |h k ih=>
      intro X D a ha b hb u
      dsimp only
      cases k with
      |zero=> rw [peg,peg]
      |succ k=>
       rw [sunrise,sunrise]
       dsimp only
       apply congrArg _; apply sum_congr rfl
       intro Y _
       apply sum_congr rfl
       intro G v
       have g:= ((Cadre.drum_p ..).mp v).2.2
       have hy:Y.val⊆X.val:=by rw [g];exact subset_union_left
       refine (y _ X D Y a ha b hb (fun i p=>u i (hy p))).trans ?_
       apply congrArg _
       rw [coeff_prod,coeff_prod]
       apply sum_congr rfl
       intro w f
       apply prod_congr rfl
       intro j e
       have hj:j.val⊆ X.val:=(coneL e).trans (by rw [g];exact subset_union_right)

       exact ih (w j) (Nat.lt_succ_of_le ((single_le_sum (fun i _=>Nat.zero_le (w i)) e).trans_eq (mem_finsuppAntidiag.mp f).1))
         j _ a ha b hb (fun i p=>u i (hj p))
 intro a ha b hb u
 unfold layerN
 exact sum_congr rfl (fun j _=> aux j X D a ha b hb u)
-- Turf layer: Leaseless preserved
namespace Leaseless
lemma pool {J:Type*}(T:Finset J)(F:J→ Copy n)(z:∀ i∈T,Leaseless (F i)):Leaseless (∑ i∈T,F i):=by
 intro v t; rw [Finset.sum_apply,Finset.sum_apply];exact sum_congr rfl (fun i w=>z i w v t)
lemma pond {J:Type*}(T:Finset J)(F:J→ Copy n)(z:∀ i∈T,Leaseless (F i)):Leaseless (∏ i∈T,F i):=by
 intro v t; rw [Finset.prod_apply,Finset.prod_apply];exact prod_congr rfl (fun i w=>z i w v t)
lemma ironR(f:ℝ)(F:Copy n)(h:Leaseless F):Leaseless (f • F) := fun v t=>congrArg (f • ·) (h v t)
lemma iron(f:ℂ)(F:Copy n)(h:Leaseless F):Leaseless (f • F) := fun v t=>congrArg (f • ·) (h v t)
end Leaseless

lemma peelField (S: Aura n→Support (More n)→ Copy n)
 (K:Rinse (Seat n) (Copy n))
 (A:∀ X,Leaseless (S X ∅))
 (y:∀ X Y V,Leaseless V→Leaseless (K X ∅ Y V))
 (t:ℕ):Bake.Turf (fun i:Aura n=>layerN S K t i ∅):=by
 have aux(k:ℕ):∀ X,Leaseless (coeff k (Cadre.chip K S X ∅)):=by
    induction k using Nat.strong_induction_on with
    |h k ih=>
      intro X
      cases k with
      |zero=> rw [peg];exact A _
      |succ k=>
       rw [sunrise]
       apply Leaseless.ironR
       apply Leaseless.pool;intro Y _
       apply Leaseless.pool;intro G v
       apply y
       rw [coeff_prod]
       apply Leaseless.pool
       intro w f
       apply Leaseless.pond
       intro j e
       rw [empty_inter]
       exact ih (w j) (Nat.lt_succ_of_le ((single_le_sum (fun i _=>Nat.zero_le (w i)) e).trans_eq (mem_finsuppAntidiag.mp f).1)) j
 intro X
 change Leaseless (layerN S K t X ∅)
 exact Leaseless.pool _ _ (fun k _=>aux k X)

lemma peelNull (S: Aura n→Support (More n)→ Copy n)
 (K:Rinse (Seat n) (Copy n))(y:∀ X D Y V,K X D Y V=0)
 (t:ℕ):layerN S K t = S:=by
 funext X D

 unfold layerN
 rw [sum_eq_single 0,peg]
 · intro b k h
   cases b with
   |zero=>exact False.elim (h rfl)
   |succ b=> rw [sunrise]; simp [y]
 simp
variable (S: Aura n→Support (More n)→ Copy n)
abbrev Tether (σ:I→Seat n)(m:I→Sour.Bag n):Prop:=
 ∀ i (Y:Aura n),σ i∉ Y.val → m i Y=0
lemma flareTurn (σ:I→Seat n)(y:Tether σ m) (t:ℕ)(X:Aura n)(D:Support (More n)):
 Rive.Hush σ X.val (fun z=> layerN S (flare p z) t X D):=by
 refine peelTurns S σ (flare p) ?_ t X D
 intro V X' D' Y a ha b hb v
 unfold flare
 apply sum_congr rfl; intro i _
 by_cases g:σ i∈Y.val
 · rw [v i g]
 rw [Orchard.hyp,lampOff _ _ _ _ (y i Y g) _,smul_zero,smul_zero]
lemma flareField (A:∀ X,Leaseless (S X ∅))(z:Key I)
 (t:ℕ):Bake.Turf (fun i:Aura n=>layerN S (flare p z) t i ∅):=by
 refine peelField S _ A ?_ t
 intro X Y V h
 unfold flare
 apply Leaseless.pool;intro i _
 exact Leaseless.iron _ _ (lampLease (p i).fullUp X Y V h)
lemma flareEmpty (t:ℕ):layerN S (flare p 0) t = S:=by
 refine peelNull S _ ?_ t
 intro X D Y V
 change (∑ i, (0:ℂ) • _) = 0
 simp
end YM.CF.Bay
