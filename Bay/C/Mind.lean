import Bay.C.Leather
import Bay.Crenel
import SatinThinQuality
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay.C
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
open Hake Jet Sault Stax Sour
attribute [local instance] Sour.loreM Sour.loreN
open Rill Branch Tenant Drapes Leaf



open Levier Urn Ione
open Peaks


open Salt QuadClock
open Bake

variable {n:Side}(s:Sweep n){m m':Sour.Bag n}
abbrev Steering (s:Sweep n)(m m':Sour.Bag n):=
  ∀ X i,m' (moldA s X) (yellA s i)=jersey s (m X i)

theorem Driving (L b:ℕ)(x:Seat n)(g:Steering s m m'):
 Steering s (stick L x b m)
   (stick L ((boxA s).symm x) b m'):=by
  intro X i
  let A:=lotY s.charge (detX s.s) (socks s)
  change _=A _
  rw [stick,Finset.sum_apply,stick,Finset.sum_apply,map_sum,← Equiv.sum_comp (moldA s)]
  apply sum_congr rfl; intro Y _
  have p:moldA s (plank L b x)=plank L b ((boxA s).symm x):=by
     apply Subtype.ext
     change actY s (Lattice.halo _ _) = _
     have h (D:Support (More n)):
       actY s (Lattice.halo (plankN L*b) D)=Lattice.halo (plankN L*b) (actY s D):=by
         unfold Salt.actY; rw [←sitU,paysT]
     rw [h];simp only[actY,map_singleton];rfl
  have e:αK (moldA s Y) (plank L b ((boxA s).symm x))=moldA s (αK Y (plank L b x)):=by
     rw [←p];exact Subtype.ext (map_union ..).symm
  simp only[e,(moldA s).injective.eq_iff];split;exact g Y i;exact (map_zero A).symm

variable {P:BudgetPoint}{q:ℕ}{h:ℝ}
 {c r c' r':Aura n→ℝ}
 (p:Bias (cipherK q) m P h c)
 (g:Bias (cipherK q) m' P h c')
 (hb: Steering s m m')(D:Support (More n))(V:Orbit n)
local notation "Ta"=> Salt.actY s
local notation "Tu"=> moldA s
local notation "σX'"=> σX (n:=n) P
local notation "W'"=> yellA s V
local notation "δ"=>cipherK q
include p g hb

-- cp. Stax.Bust leap
lemma nore (X Y:Aura n)(t: Bias.αt Y X D δ):coll_T P (Tu X) (Ta D) (m' (Tu Y)) W'=jersey s (coll_T P X D (m Y) V):=by
 let a:=moldA s X; have hv:= (optic s D Y X δ).mpr t; let Λ:=jersey s; let Qv:=σX' X D; let Kv:=p.scope X Y D t.1 t.2.1 t.2.2; let Ku:=g.scope (moldA s X) (moldA s Y) (actY s D) hv.1 hv.2.1 hv.2.2
 by_cases f:Gates Qv X.val V.1; swap
 · unfold coll_T; rw [if_neg ?_,if_neg f,jersey,sauce,singT,win_z,map_zero]; exact mt (lights_V ..).mp f
 obtain ⟨Y',q,v⟩:=f; let Z:Orbit n:=(Y',V.2); let X':= σX' a (Ta D); have he: Agrees _ _ _ ∧ Set.EqOn _ _ _:=yellow s V Z X.val v (fun _ _=>rfl)
 let U:= yellA s Z; rw [Kv.toCrate.latch V Z v (fun _ _=>rfl),Kv.toCrate.pointV Z q,Ku.toCrate.latch _ U he.1 he.2, Ku.toCrate.pointV _ (show U.1 ∈ X' from ((Salt.lights_C ..)).mpr q),hb]
lemma leaps (X Y:Aura n){F' F₀:Copy n}(l:F' W'=suit_Y s (F₀ V)):g.payX (Tu X) (Ta D) (Tu Y) F' W'=suit_Y s (p.payX X D Y F₀ V):=by
 by_cases hA:Bias.αt Y X D δ; swap; · unfold Bias.payX; rw [dif_neg hA,dif_neg (fun t=> hA ((optic s D Y X δ).mp t)),Pi.zero_apply, Pi.zero_apply,map_zero]
 apply Subtype.ext; rw [g.truth _ _ _ _ ((optic s D Y X δ).mpr hA) _,l]
 change Sault.rind (coll_T _ _ _ _ _ *jersey _ _) = jersey _ (p.payX X D Y F₀ V).val; rw [p.truth _ _ _ _ hA _, plier,nore s p g hb D V X Y hA,show jersey s (coll_T P X D (m Y) V*(F₀ V).val)= _ from singm ..]
omit p g

variable (t:Orchard P q h m c r)
 (t':Orchard P q h m' c' r')
lemma sore (o:Seat n)(τ τ':Ids n):
 passingR n s (Orchard.petalReg o t τ) (Orchard.petalReg ((boxA s).symm o) t' τ'):=by
 intro i a
 simp only [Orchard.petalReg,show (moveHub s i).val.1=(boxA s).symm i.val.1 from rfl, (boxA s).symm.injective.eq_iff];split; swap
 · rw [Pi.zero_apply, Pi.zero_apply,map_zero]
 let X:= lagE i
 let V:Orbit n:=(a,τ)
 let W:= yellA s V
 have k:= leaps s (asBias t.fullUp) (asBias t'.fullUp) hb ∅ V X X (F':=1) (F₀:=1) ((map_one _).symm)
 rw [show Ta ∅=∅ from map_empty _] at k
 exact ((t'.budLease (Tu X) W τ').symm).trans k
