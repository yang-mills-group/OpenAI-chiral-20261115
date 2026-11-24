import Merino.Brooch.Span
import Merino.Corolla.Seasons
import Merino.Brooch.Fitting

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 520000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Brooch
open Function Finset Fock Scroll Spire Sault
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Lattice Cube Scree Skye Sour Drapes Tulip Lat Branch Swell
open Thera Hest Levier BProof RG Salt Mew Stax
open Dial Vow TreasuryFog Paige Vault Roots
variable {G B L:Side}{j:ℕ}{jY:Odd L.val}{Y:Pricing j L jY (Thread j)}{e:ℝ}
variable {I:Type}[Fintype I][LinearOrder I]
local notation "Ω"=> mid G B

/-- An office processes a single opening. Anchor at the requested node (not
 necessarily exact). Budget $b$ is *total* birth (not coefficient) here.
-/
structure Office (U:Grasp Y B e)(R:GramM Ω)(K:Scree.Loom Ω)
    (q:ℕ)(h a b:ℝ)(o:Site Ω)(X:Obs Ω)(V:phy Ω)(T:Bag Ω) : Prop where
  badge: Allowed (sleeve R.p o) X
  pouch: Barrage R.p q {node o} h T (Corolla.eighth R.p.B) a b
  science :∀ Z:Orbit Ω,∀ d:IsStarProjection (spar j R.J.M (K Z)),∀ t: Wave (Dwell Ω),
     pilotH U R K Z d (acts (∑ i:Aura Ω,T i Z) t)= acts (V Z) (pilotH U R K Z d t)
  lives:∀ Z:Orbit Ω,Injective (priorP Z.2)→Fock.Sector (modes (sleeve R.p o)) false (V Z)
  pairs:∀ Z:Orbit Ω,Injective (priorP Z.2)→bra (X Z.1) (V Z)


variable {U:Grasp Y B e}{R:GramM (mid G B)}{K:Scree.Loom (mid G B)} {q m:ℕ}{h a b c f d:ℝ}

open Py.Rate.LocalLimit.Preparation

lemma hire (z:ℝ)(s:Sweep Ω){o:Site Ω}{y:Spool Ω}{T:Bag Ω}
    (t:y.Hem K R.p c f d)
    (r:Nest U R K q 24 (boxA s y.post) h (rScale R.p) (ghost s y R.p K z) T a b)
    (u:inReach R.p o s y) (k:12≤R.p.B) (g:24*y.stepY≤R.p.B):
      Office U R K q h a b o (face s y R.p K z) (ghost s y R.p K z) T:=by
  have hp:=touches y R.p g k u
  refine ⟨Bide.mode_p (faceA s z t) hp,?_,r.science,?_,ghostYoke s z t⟩
  · obtain ⟨E,J,G₁,L,V⟩:=r.pouch.price
    have ht:node o ∈ grooveB 24 R.p ((boxA s) y.post):=halo_spec.mpr ⟨_,mem_singleton_self _,by
       rw [separation_comm]
       exact u.trans (by omega)⟩
    exact ⟨E,J,G₁,fun i h=> L i fun f=> h (singleton_subset_iff.mpr (f ht)),V⟩
  intro V v
  exact Garden.scope (ghostA s z t g V v) (fun i h=>(mem_modes ..).mpr (hp ((mem_modes ..).mp h)))

open Py Oise Neon Rive QuadClock
/-- tipped denZ on actual law -/
def syllable(U:Grasp Y B e)(R:GramM Ω)(K:Scree.Loom Ω)
 (D:Key I→ RegBudget Ω)(F:Key I→ForceBudget Ω)(l:List I)(Z:Orbit Ω):Phys Ω:=
 tipI (fun z=> denZ
       (color_b R R.beta (R.F + D z) R.slip (R.K + F z) R.v) U K Z) l

abbrev earnsRoot (U:Grasp Y B e)(R:GramM Ω)(K:Scree.Loom Ω)
 (o:I→Site Ω)(X:I→Obs Ω)
 (D:Key I→ RegBudget Ω)(F:Key I→ForceBudget Ω):Prop:=
   ∀ Z:Orbit Ω,Rue.FleetS R.p.threshold Z.1→Injective (priorP Z.2)→
   ∀ l:List I,ψS (node∘o) l → beamZ Ω (syllable U R K D F l Z)=
     beamZ Ω (acts (l.map (fun i=> X i Z.1)).prod (denZ R U K Z))


lemma afterheel {o:I→Site Ω}{s:Side}{w:ℝ}
 {X:I→Obs Ω}{V:I→phy Ω}{T:I→Bag Ω}
 {D:Key I→ RegBudget Ω}{F:Key I→ForceBudget Ω}
 (u:∀i,Office U R K q h a b (o i) (X i) (V i) (T i))
 (p:Force_M R.p.B (node∘o) m)
 (t:Corolla.Fit R o s w m (Corolla.flowerSum T) h D F)
 (c:12≤ R.p.B)
 (usable:∀ Z:Orbit Ω,IsStarProjection (spar j R.J.M (K Z))):
   earnsRoot U R K o X D F:=by
 intro Z v r l g0
 unfold syllable
 let A:=fun i=> V i Z
 let B':= fun i=> X i Z.1
 have v₀:Pulse R.p o A:=fun i=>(u i).lives Z r
 have v₁:Pulse R.p o B':=fun i=> (u i).badge.modes_use Z.1
 have e(Yi:Bag Ω):(∑i: Aura Ω,Yi i) Z=∑i:Aura Ω,Yi i Z:=sum_apply ..
 have z:spare o l:=List.pairwise_map.mp g0

 rw [t.earned U K Z (usable Z) l g0 A v (sparks _ _ _ _ c p.1 v₀ z) (fun i _=> by unfold Corolla.flowerSum; rw [e];exact (u i).science ..)]
 have he:=cut o l B' A R.p c p.1 v₁ v₀ (fun i=>(u i).pairs Z r) z
 unfold beamZ
 change inner ℂ _ (acts _ _) = inner ℂ _ (acts (l.map B').prod _)
 rw [←act_inner,←act_inner, show _=_ from he]


/-- Fulfilment. Labels arbitrary finite. -/
structure Fall(U:Grasp Y B e)(R:GramM Ω)(K:Scree.Loom Ω)
   (o:I→Site Ω)(q:ℕ)(h a b:ℝ)(X:I→Obs Ω)
   (s:Side)(w:ℝ)(m:ℕ) : Prop where
 cloth:∃ T:I→Bag Ω,∃ V:I→phy Ω,∃ D:Key I→RegBudget Ω,∃ F:Key I→ForceBudget Ω,
   (∀i,Office U R K q h a b (o i) (X i) (V i) (T i))∧
   Corolla.Fit R o s w m (Corolla.flowerSum T) h D F ∧ earnsRoot U R K o X D F


/-- Common purse. q is Roof n, a full, b birth. -/
structure Strong(U:Grasp Y B e)(R:GramM Ω)(K:Scree.Loom Ω)
  (q:ℕ)(h a b:ℝ)(s:Side)(w:ℝ)(m:ℕ):Prop where
 rents:∃ v g, Corolla.Tuning R.p s.val h a b v g w m∧SanB R.K (giftK R.p (Corolla.rip R.p)) R.p h (fun _=> v)
 wake:FlagWidth R.p R.K (Rill.cipherK q)
 day:∀ Z:Orbit Ω,IsStarProjection (spar j R.J.M (K Z))
 region:2*(Corolla.postL s.val*R.p.B)<(More Ω).val
 high: 12≤R.p.B

lemma procures {s:Side}{w:ℝ}
 (j1:Strong U R K q h a b s w m)
 (o:I→Site Ω)(l:Force_M R.p.B (node∘o) m)(X:I→Obs Ω)
 (c:∀i,∃ V T,Office U R K q h a b (o i) (X i) V T):
 Fall U R K o q h a b X s w m:=by
 choose G₁ T e using c
 obtain ⟨v,g,p,J⟩:=j1.rents
 obtain ⟨D,F,y⟩:= Corolla.fitting R p l j1.wake J T j1.region (fun i=>(e i).pouch)
 exact ⟨T,G₁,D,F,e,y,afterheel e l y j1.high j1.day⟩
end YM.CF.Merino.Brooch

