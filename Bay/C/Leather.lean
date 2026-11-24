import Bay.C.Franco
import Bay.C.Ribbon
import YM.CF.Stax.Bust
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


open Salt SU
variable {n:Side}(s:Sweep n)
/-- Sweeps left to right. -/
lemma unyell(x:Orbit n):yellA s⁻¹ (yellA s x)=x:=Prod.ext (revB ..) (tuftT ..)
lemma unact(X:Support (More n)):actY s⁻¹ (actY s X)=X:=by
 ext i; unfold actY; rw [sitU,mem_map_equiv,mem_map_equiv];simp
lemma rebound(X:Support (More n)):actY s (actY s⁻¹ X)=X:=by simpa using unact s⁻¹ X
lemma boast(x:Orbit n)(t:Seat n→E):
  yellA s (gauge t x.1,threadG t x.2)=
   (gauge (chosen s t) (yellA s x).1,threadG (chosen s t) (yellA s x).2) := Prod.ext (revG ..) (by
    funext i
    let c:=boxA s i
    exact Prod.ext rfl (Prod.ext rfl (show polarT s.charge ((x.2 c).2.2*(t c)⁻¹)=_ by rw [map_mul,map_inv]; rfl)))
lemma boast_gg (g:Seat n→E):chosen s (chosen s⁻¹ g)=g:=by
 funext i; change polarT s.charge (polarT s⁻¹.charge (g (boxA s⁻¹ (boxA s i))))=_
 rw [sitU,Equiv.symm_apply_apply,polar_t]
 rw [show s⁻¹.charge=s.charge from rfl, Bool.xor_self]
 rfl

lemma raiseMeas: Measurable (yellA s):= ((flash_p s).measurable.comp measurable_fst).prodMk ((tuft s).measurable.comp measurable_snd)
lemma surRaise:Surjective (yellA s):=fun x=>⟨yellA s⁻¹ x,by simpa using unyell s⁻¹ x⟩
lemma dress (P:BudgetPoint)(X:Aura n)(D:Support (More n))(x:Orbit n):
 (yellA s x).1∈σX P (moldA s X) (actY s D) ↔ x.1∈σX P X D:=lights_C ..

-- canonical Bag action
def dart (f:Firing n):Firing n:=fun i=>jersey s (f (yellA s⁻¹ i))
lemma flighty (f:Firing n)(x:Orbit n):dart s f (yellA s x)=jersey s (f x):=by rw [dart,unyell]
lemma jerseyMes: Measurable (jersey s):=by
 apply Continuous.measurable
 exact (breeze (hail_Q s)).comp (typ_l _)
lemma dart0 :dart s 0=0:= by
 funext x; apply map_zero (Urn.lotY ..)
variable {P:BudgetPoint}{q:ℕ}{X Y:Aura n}{D:Support (More n)}
  {f:Firing n}{h c:ℝ}
local notation "a'" X:max=> moldA s X
local notation "d'" D:max=> actY s D

lemma frame_crate(g:Crate P X D Y f):
 Crate P (a' X) (d' D) (a' Y) (dart s f):=by
 refine ⟨(jerseyMes s).comp (g.cog.comp (raiseMeas s⁻¹)),fun i=>active_t (X:=Y.val) s (g.body (yellA s⁻¹ i)),?_,?_⟩

 · intro i j hi hj p t
   have k (u:Orbit n)(hu:u.1∈σX P (a' X) (d' D)): (yellA s⁻¹ u).1∈σX P X D:=by
     apply (dress s P X D _).mp; have e:=unyell s⁻¹ u; rw [inv_inv] at e; rwa [e]
   have x:=yellow s⁻¹ i j (actY s X.val) p t; rw [unact] at x
   exact congrArg (jersey s) (g.same _ _ (k _ hi) (k _ hj) x.1 x.2)
 · intro i t u
   obtain ⟨j,rfl⟩:= surRaise s i
   let x:= (gauge (chosen s⁻¹ t) j.1,threadG (chosen s⁻¹ t) j.2)
   have a:= boast s j (chosen s⁻¹ t); rw [boast_gg] at a
   rw [flighty, ←a,flighty,g.gauge _ _ ((dress s P _ _ _).mp u)]
   have v:=aim_t s (chosen s⁻¹ t) (g.body j);rw [boast_gg] at v
   exact v


lemma doorP (V:Pane n):‖door_b s V‖≤1:=by
 apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
 intro y
 rw [one_mul]
 exact (pi_norm_le_iff_of_nonneg (norm_nonneg y)).mpr
   fun i=> by rw [cod_E];exact norm_le_pi_norm y _

lemma marquee (v:Velvet s)(g:Marque P X Y D f h c):
 Marque P (a' X) (a' Y) (d' D) (dart s f) h c:=by
 refine ⟨frame_crate s g.toCrate,?_⟩
 obtain ⟨b,t,k,u⟩:= g.vet; obtain ⟨e,toll,H⟩:=lace s v
 refine ⟨fun i j=> b (e.symm i) (e.symm j),fun _ _=>t ..,?_,?_⟩
 · intro j;obtain ⟨j,rfl⟩:=e.surjective j
   rw [←Equiv.sum_comp e]; simp only [Equiv.symm_apply_apply,Rail,toll]
   exact k j
 intro x a Z d i j
 obtain ⟨i,rfl⟩:=e.surjective i;obtain ⟨j,rfl⟩:=e.surjective j
 let f':=fun y:tangD n=> f (pressQ P (actY s⁻¹ Z) (yellA s⁻¹ x).1 y,(yellA s⁻¹ x).2)
 have p':Pence P.order (fun y=>f' y i j) 0 (b i j):=u (yellA s⁻¹ x) (by
    apply (dress s P X D _).mp; have j:=unyell s⁻¹ x; rw [inv_inv] at j;rwa [j]) _ (by
      have r:actY s⁻¹ (actY s D)⊆actY s⁻¹ Z:=map_subset_map.mpr d
      rwa [unact] at r) i j

 simp only [Equiv.symm_apply_apply]
 let L:= door_b s⁻¹ x.1
 have w(y:tangD n):dart s f (pressQ P Z x.1 y,x.2)=jersey s (f' (L y)):=by
   unfold dart; change jersey _ (f (flashA s⁻¹ (pressQ _ _ _ _),_))=_; rw [parl_v]
 simp_rw [w]
 exact H L f' _ _ _ _ (doorP ..) p'


lemma undressE (x:Orbit n)(u:(yellA s x).1∈σX P (a' X) ∅):x.1∈σX P X ∅:=
 (dress s P X ∅ x).mp (by rw [show actY s ∅=∅ from map_empty _];exact u)
lemma rat(v:Velvet s)(g:Herb P q X h f c):Herb P q (a' X) h (dart s f) c:=by
 refine ⟨g.price,?_,?_⟩
 · intro Y a D i j
   obtain ⟨Y,rfl⟩:=(moldA s).surjective Y
   obtain ⟨D,rfl⟩:=(show ∃ z,actY s z=D from ⟨_,rebound ..⟩)
   obtain ⟨a,i,j⟩:= (optic s D X Y (cipherK q)).mp ⟨a,i,j⟩
   exact marquee s v (g.offer Y a D i j)
 intro Y a x t l
 obtain ⟨Y,rfl⟩:=(moldA s).surjective Y
 obtain ⟨x,rfl⟩:= surRaise s x
 obtain ⟨l,rfl⟩:=(show ∃ z,bun s z=l from ⟨_,by exact inv_inv s ▸ tuftT s⁻¹ l⟩)
 rw [show ((yellA s x).1,bun s l) = yellA s (x.1,l) from rfl, flighty, flighty, g.clean Y (map_subset_map.mp a) x (undressE s x t)]

lemma plier (A:FC (Dwell n)): jersey s (Sault.rind A)= Sault.rind (jersey s A):= Sault.plower ..
lemma fuzz {d:ℝ}(v:Velvet s)(g:Flight P q X h f c d):Flight P q (a' X) h (dart s f) c d:=by
 obtain ⟨W,k,l⟩:=g.forms
 refine ⟨rat s v g.tube,dart s W,rat s v k,?_⟩
 intro Y a x t
 obtain ⟨Y,rfl⟩:=(moldA s).surjective Y
 obtain ⟨x,rfl⟩:=surRaise s x
 rw [flighty,flighty,←plier, ←plier,l Y (map_subset_map.mp a) x (undressE s x t)]

abbrev quiver (m:Sour.Bag n): Sour.Bag n:=fun i=>dart s (m ((moldA s).symm i))
lemma salute (m:Sour.Bag n)(X:Aura n)(x:Orbit n):
 quiver s m (moldA s X) (yellA s x)=jersey s (m X x):=by rw [quiver,Equiv.symm_apply_apply,flighty]

lemma crew {m:Sour.Bag n}{r d:ℝ}(v:Velvet s)
 (g:Barrage P q D h m r c d):Barrage P q (actY s D) h (quiver s m) r c d:=by
 have ht(t:Aura n→ℝ):voyageB (t ∘ (moldA s).symm) P.B r= voyageB t P.B r:=by
   unfold voyageB; rw [←Equiv.sum_comp (moldA s)]
   apply sum_congr rfl; intro i _
   unfold Sour.tact widthK
   simp only [Function.comp_apply,Equiv.symm_apply_apply,show (a' i).val=actY s i.val from rfl]
   rw [Ione.glow_q]
 obtain ⟨a,b,u,p,G,H⟩:=g.price
 refine ⟨_,_,?_,?_,(ht a).trans_le G,(ht b).trans_le H⟩
 · intro i; dsimp [quiver]
   obtain ⟨i,rfl⟩:=(moldA s).surjective i;rw [Equiv.symm_apply_apply]
   exact fuzz s v (u i)
 intro i x; dsimp only [Function.comp_apply, quiver]
 obtain ⟨i,rfl⟩:=(moldA s).surjective i;rw [Equiv.symm_apply_apply]
 obtain ⟨t,r,z⟩:=p i (mt map_subset_map.mpr x)
 rw [t,dart0,r,z];exact ⟨rfl,rfl,rfl⟩
