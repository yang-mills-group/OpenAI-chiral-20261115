import Bay.C.Purse
import Bay.Loggia
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

set_option maxRecDepth 3500
set_option synthInstance.maxHeartbeats 160000
open Py Py.Rate Thera Dial Nacre Laic
open LocalLimit Preparation


open Salt SU Swell
open QuadClock
open Mew Vow.TreasuryFog Roots
open scoped YM.CF.Mew
variable {n:Side}
open BProof.Bide

structure SealV(n:Side) where
 root:Seat n
 limb:footprint n
 price:ℝ
 shown:Stencil n
 hidden:phy n
 ink:Sour.Bag n

abbrev Located(P:BudgetPoint)(x:Seat n)(A:footprint n):Prop:=
  ∀z∈A,separation x z ≤ 50*P.B

variable (w:Berth)
structure Grant (C D:ℝ→ℝ)(S:SealV w.side):Prop where
 near : Located w.p S.root S.limb
 entourage : Accompanies S.limb S.price S.shown S.hidden
 earns: Grass w S.hidden S.ink
 charged:w.loanY S.root S.ink C D
variable {w}

/-- no phase convention suppressed: `move` is BProof.Bide.move -/
def watch (s:Sweep n)(S:SealV n):SealV n:=
 ⟨(boxA s).symm S.root,actY s S.limb,S.price,move s S.shown,clash s S.hidden,quiver s S.ink⟩

variable {m:ℕ}{a b c:ℝ}{C D C' D':ℝ→ℝ}
lemma Grant.watchful {S:SealV w.side}(g:Grant w C D S)
 (r:w.Rig a c m)(s:Sweep w.side)(v:Velvet s): Grant w C D (watch s S):=by
 refine ⟨?_,march_mates s g.entourage,tug r s g.earns,?_⟩
 · intro x t
   change separation ((boxA s).symm _) _ ≤ _
   rw [←sitT s,Equiv.apply_symm_apply]
   exact g.near _ (mem_map_equiv.mp t)
 have q:=crew s v g.charged
 simp only [actY,map_singleton] at q
 exact q

lemma Grant.bigger {S:SealV w.side}(g:Grant w C D S) (r:w.Rig a c m)
 (v:C w.x≤C' w.x)(t:D w.x≤D' w.x) : Grant w C' D' S:=⟨g.near,g.entourage,g.earns,g.charged.bigR v (mul_le_mul_of_nonneg_right t r.qq.le)⟩

lemma locatedGlue(P:BudgetPoint) {u z:Seat n}(A:footprint n)
 (t:∀x∈A, separation z x ≤ 26*P.B)
 (c:u∈grooveB 24 P z):
 Located P u A:=by
 intro x hx
 refine (separation_triangle u z x).trans ?_
 have g:= t x hx
 obtain ⟨b,p,h⟩:=halo_spec.mp c
 rw[mem_singleton.mp p,separation_comm] at h
 omega

variable (w)
-- gauge heel argument independent of anchor choice, pre-pose
def seam (x:Site w.side)(o:Seat w.side)(f:w.First)(m:ℕ)(b:ℝ)
 (v:Sour.Bag w.side):SealV w.side:=
 ⟨o,w.supportY m x,w.hue * costY b,w.marked129 x f m,w.cloth x f m,v⟩
variable {w}{x:Site w.side}{o:Seat w.side}{f:w.First}{v:Sour.Bag w.side}

lemma seamL (r:w.Rig a c m)(g:w.Tall)
 (d:w.WearY m x f a c b v)(t:o∈grooveB 24 w.p (node x)):
 Grant w (till129 w.P a c b m) (reserve129 w.P a c b m) (seam w x o f m b v):=by
 refine ⟨locatedGlue w.p _ ?_ t,d.fit,fun u _ j=> d.stitch.science u j,
      Berth.rootLodge w d.stitch.pouch t⟩
 intro y p
 change y∈w.supportY m x at p
 obtain ⟨z,p,h⟩:=halo_spec.mp p
 rw[mem_singleton.mp p] at h
 have b:=r.sizes.1;unfold Berth.Tall at g;omega

variable {I:Type}[LinearOrder I][Fintype I]
abbrev gr(S:I→SealV n):=fun i=>(S i).root
abbrev gl(S:I→SealV n):=fun i=>(S i).limb
abbrev gp(S:I→SealV n):=fun i=>(S i).price
abbrev showSet(S:I→SealV n):=fun i=>(S i).shown
abbrev agent(S:I→SealV n):=fun i=>(S i).hidden
abbrev paints(S:I→SealV n):=fun i=>(S i).ink

variable {M L:ℕ}{F:ℝ→ℝ}{r:blazeK w.side}
variable (w)
-- Forgetful projection

structure Hops (S:I→SealV w.side)(L:ℕ)(t:ℝ)
 (U:Mew.Key I→ RegBudget w.side)(W:Mew.Key I→ForceBudget w.side):Prop where
 wide(l:List I): ψS (gr S) l→independent l (gl S)
 book: w.Moored (gl S) (gr S) (gp S) (showSet S) (agent S) Pine L t U W

variable {w}{E B:I→Aura w.side→ℝ}{S:I→SealV w.side}
lemma hops_book (g:w.Thermal M L F C D r)(h:w.Rig a c m)(k:w.Tall)
  (u:w.GaugeBill M (gr S))(z:∀ i,Grant w C D (S i))
  (d:w.Cached (gr S) (paints S) L E B C D)(s:ℕ)(j:w.lampCap≤ s)(τ:Ids w.side):
 Hops w S L (icedCost w.P M L F D w.x) (w.flareE d (gr S) s τ)
      (w.flareF d (gr S) s) ∧
 ∀ i,νTip (w.flareE d (gr S) s τ) i=kilnTip d.bill (gr S) τ i∧
    emberTip (w.flareF d (gr S) s) i=νΦK (rootF w.R (flare d.bill) s) {i}:=by

 have p:w.Quest (gl S) (gp S) (showSet S) (agent S) (paints S) Pine:=⟨fun i=>(z i).entourage,
       fun x i t=>(z i).earns x t⟩
 obtain ⟨a,b⟩:=Berth.unspooled g h u d p (earnedP w.side) s j τ
 refine ⟨⟨?_,a⟩,b⟩

 let X:=gr S
 have c(i:I)(b)(h:b∈gl S i):separation (X i) b≤50*w.p.B:=(z i).near b h
 have hh:50 ≤ w.p.B^2:= (show 50 ≤ (20:ℕ)^2 by decide).trans (pow_le_pow_left₀ (Nat.zero_le _) k _)
 intro l t
 refine (List.pairwise_map.mp t).imp fun {i j} f=> disjoint_left.mpr fun {b} e p=>?_
 have y:2*w.p.B^3+2*w.p.B < separation (X i) (X j):=u.2 i j f
 have h:=le_trans (separation_triangle (X i) b (X j)) (Nat.add_le_add (c i _ e) ((separation_comm ..).trans_le (c j _ p)))
 have hx:=Nat.mul_le_mul_right w.p.B hh
 rw [show (3:ℕ)=2+1 from rfl,pow_succ w.p.B] at y;omega
