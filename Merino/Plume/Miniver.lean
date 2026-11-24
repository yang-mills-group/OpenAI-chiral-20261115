import Merino.Plume.Osier
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
set_option maxRecDepth 3500
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Plume
open Filter Topology Lattice Lat Tulip Branch Cube Tenant Drapes Metric
open _root_.Zephyr.Chern
open scoped Matrix Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Finset Swell

variable {n:Side}

open Py.Rate.LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection
open Skye Scree Vale RG
open Py (hueW stemS pinpr)
variable (P:Spine)


open Cuff Hem Medal Lace
open Buffered Lifted Afterglow Journey Tower Tower.SlabMark



variable (p:Bolts)(s i k:ℕ)
abbrev badge (d:Gown P p (priceTick P) s i k):=
  (lure_origin P p (priceTick P) s i k d)∘ dark (RegNum P s i) (etch P s)
abbrev Cairn (f:LinksC→ℂ) :=
  Still (etch P s) (tempM P s) p.c P.par.d f
variable {s i k}
lemma sealFee (d:Gown P p (priceTick P) s i k)
    (h:etch P s+1<(RegNum P s i).val):
   Cairn P p s (badge P p s i k d)∧
    ∀ t:ℕ,glance (RegNum P s i) t (clearM P s) (badge P p s i k d)=emit P p s i k t d:=by
 let R:= LedgerM P s i k
 let o:=node (wrap (RegNum P s i) zeroBase)
 have g:fitted (etch P s) o R.p:=
    ⟨h, by unfold etch;rw [←d.hot.claims];exact space_at (b:=R.p.B) (home_fits _) le_rfl⟩
 have x:= d.ticket.hem.sip
 change Trunk (node d.y.origin) _ _ _ _ _ at x
 rw [d.here] at x
 have u:=calibrated (s:=s) (i:=i) P d.hot.admit.2.le
 have z:(R.p).threshold=tempM P s:=by unfold R;rw [u.1];exact (P.run.meter.boot _).1
 constructor
 · exact closed_dark d.hot.sky p.decay.le x g z
 intro t


 have a:badge P p s i k d∘onC _=lure_origin P p (priceTick P) s i k d:=
    funext (cut_period d.hot.sky p.decay.le x g)
 rw [glance,a]
 rfl

private lemma emptyC:Cairn P p s (fun _=>0):=by
 let m:=etch P s
 refine ⟨⟨measurable_const,fun _ _ _=>rfl,fun _ _=>rfl,fun _=>norm_zero.trans_le p.crown.le⟩,fun _ _ _=>?_⟩
 rw [dist_self];exact mul_nonneg (cable_pos _ p.crown.le _) dist_nonneg

structure Constellation where
  α : ℝ
  δ : ℝ
  bigE : ℝ
  r:ℝ
  L:ℝ
  ε:ℝ
  oa:0 < α
  od:0 < δ
  oe:0 < bigE
  ro:0 < r
  lo:0 < L
  pos:0 < ε
  small: ε ≤ leadCoin hueInk α/2
abbrev Ct (Q:Constellation):=leadCoin hueInk Q.α/8

def warrant (C:Constellation)(s i k:ℕ)(f:LinksC→ℂ):Prop:=
 merrier P s i k ∧ ∃ d:Gown P p (priceTick P) s i k,
   Glowing P (priceTick P) p zeroBase s i k C.δ C.bigE d ∧
   (∃T,Emblem P p s i k C.α C.r C.L C.ε d T) ∧
   f=badge P p s i k d ∧
   ∀ t:ℕ,glance (RegNum P s i) t (clearM P s) f=emit P p s i k t d



abbrev Demand (C:Constellation)(s:ℕ)(F:ℕ→LinksC→ℂ):Prop:=
 ∀ᶠ j in atTop, warrant P p C s (P.nomadic j) (P.engine j) (F j)
abbrev lamp (s:ℕ):=Strut (scaleM P s) (hike (2*priceTick P) (scaleM P s))
lemma chooseCape (C:Constellation)(h:twinkling P p C.α C.δ C.bigE C.r C.L)(A:P.NightCop):
 ∃F:ℕ→ℕ→LinksC→ℂ, (∀s j,Cairn P p s (F s j)) ∧
    ∀ᶠ s:ℕ in atTop,lamp P s∧Demand P p C s (F s):=by
 let f (s j:ℕ)(x:LinksC→ℂ):Prop:=
    Cairn P p s x ∧ warrant P p C s (P.nomadic j) (P.engine j) x
 have t:∀s j:ℕ,∃g:LinksC→ℂ,Cairn P p s g ∧ ((∃x,f s j x)→f s j g):=by
    intro s j; by_cases u:∃x,f s j x
    · obtain ⟨x,a,b⟩:=u
      exact ⟨x,a,fun _=> ⟨a,b⟩⟩
    exact ⟨_,emptyC P p,fun v=>(u v).elim⟩
 choose F q using t
 refine ⟨F,fun s j=>(q s j).1,?_⟩
 filter_upwards [h C.ε C.pos C.small] with s z
 refine ⟨z.1,?_⟩


 filter_upwards [P.stockGo.eventually z.2,path_admit P A s,
   (P.amount_go s).eventually_gt_atTop (etch P s+1)] with j m n v
 obtain ⟨d,M,J⟩:= m _ n
 obtain ⟨r,c⟩:=sealFee P p d v
 exact ((q s j).2 ⟨_,r,n,d,M,J,rfl,c⟩).2


/-- Simultaneous limiting values at all needed heights. -/
lemma chooseRibbon (C:Constellation)(h:twinkling P p C.α C.δ C.bigE C.r C.L)(A:P.NightCop):
 ∃(r':ℕ→ℕ)(F:ℕ→ℕ→LinksC→ℂ)(g:ℕ→LinksC→ℂ),
  StrictMono r' ∧
  (∀s:ℕ, Plump (Lattice.box (etch P s)) p.c (F s ∘ r') (g s)) ∧
    ∀ᶠ s:ℕ in atTop,lamp P s∧Demand P p C s (F s):=by
 obtain ⟨F,M,w⟩:=chooseCape P p C h A
 have j:∀s,∃g,blizzard (F s) g:=fun s=>
    mantle (q:=quiz _ (tempM P s)) (echoC_bounded (etch P s)) (cable_pos _ p.crown.le P.par.d)
      (fun m=>(M s m).sport) p.c (fun m=>(M s m).bound)
 choose g u using j
 obtain ⟨r,h,b⟩:=parked u
 exact ⟨r,F,g,h,fun s=> ⟨fun _=>(M s _).toSwan,b s⟩,w⟩

end YM.CF.Merino.Plume
