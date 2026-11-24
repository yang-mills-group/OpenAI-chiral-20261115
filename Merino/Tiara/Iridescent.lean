import Merino.Tiara.Fitting
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxRecDepth 2500
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Tiara
open Function Filter Metric SU Lat Lattice Cube Finset Spire Scroll Tulip Skye Window Vale Girt Buffered Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open BProof Hive Swell Hem Merino.Mitre Plume
open Afterglow Tower Lifted Journey

open Py.Rate.LocalLimit Preparation Tower.VacuumSelection
open Medal Lace Cuff Swell Hem
variable (P:Spine)(p:Bolts)(s i k:ℕ)
local notation "Ω"=>RegNum P s i
local notation "Γ"=>LedgerM P s i k
local notation "K"=> LoomM P s i

open Satin
def Host (S:Finset Cover) {K':Calibration}
  (X:ℕ→Reins K')(J:Reins K'):=∀σ a,Elite S (fun n=>X n σ a) (J σ a)
abbrev Point(s:ℕ):=Signed × Axis × Evens (Lattice.box (etch P s)) × LinksC
abbrev ft {s}(x:Scarf P s)(w:Point P s):=x w.1 w.2.1 w.2.2.1 w.2.2.2
lemma snowglobe (X : ∀ s, ℕ→Scarf P s)(pX:∀s n,Osmium P p s (X s n)):
 ∃ u,StrictMono u ∧ ∀s,∃j,Host (Lattice.box (etch P s)) (rail P∘X s∘u) j:=by
 have w:∀s σ a i,∃g, blizzard (fun n=>X s n σ a i) g:=fun s σ a k=>
      mantle (q:=quiz _ (tempM P s)) (echoC_bounded (etch P s))
        (mul_nonneg (by norm_num) (cable_pos _ p.crown.le P.par.d))
       (fun n=>(pX s n σ a).sport k) _ (fun n=>(pX s n σ a).bound k)
 choose G h using w
 have t:∀s, blizzard (ft P ∘ X s) (ft P (G s)) := by
   intro s e v
   have n:= eventually_all.mpr fun σ=>eventually_all.mpr fun a=>eventually_all.mpr fun k=>
       h s σ a k e v
   exact n.mono fun j d y=>d y.1 y.2.1 y.2.2.1 y.2.2.2


 obtain ⟨u,a,b⟩:=parked t
 refine ⟨u,a,fun l=>⟨rail P (G l),?_⟩⟩
 intro σ j
 have s:∀k,spray (fun n=>X l (u n) σ j k) (G l σ j k):=fun k e p=>
    (b l e p).mono fun n g x=>g (σ,j,k,x)
 have v(n): Willow P.calibration (p.c+p.c) (X l (u n) σ j):= (pX l _ _ _).toWillow
 exact ⟨ivy _ s (add_nonneg p.crown.le p.crown.le) v,fun n=>(v n).sang,
     (varnish _ s v).sang⟩

lemma stirs{S:Finset Cover}{u:ℕ→ℕ}{f:LinksC→ℂ}{F:ℕ→LinksC→ℂ}
 (a:StrictMono u)(h:Plump S p.c F f):Plump S p.c (F∘u) f:=
 ⟨fun _=>h.1 _,fun e z=>a.tendsto_atTop.eventually (h.2 e z)⟩
structure Carol (P:Spine)(p:Bolts)(C:Constellation)(r:ℕ→ℕ)(s:ℕ)
 (F:ℕ→LinksC→ℂ)(g:LinksC→ℂ)(X:ℕ→Reins P.calibration)
 (j:Reins P.calibration):Prop extends Ala P p C r s F g where
  rail: Host (Lattice.box (etch P s)) X j
  fitted: ∀ᶠ m in atTop,Tailored P p s (P.nomadic (r m)) (P.engine (r m)) C (F m) (X m)

-- strengthen Hill, selecting data once even prior to tolls in eventual s.
lemma aria(C:Constellation)(h:Hill P p C):
 ∃ (r:ℕ→ℕ)(F:ℕ→ℕ→LinksC→ℂ)(g:ℕ→LinksC→ℂ)
  (X:ℕ→ℕ→Reins P.calibration)(J:ℕ→Reins P.calibration),
    StrictMono r ∧ ∀ᶠ s in atTop,Carol P p C r s (F s) (g s) (X s) (J s):= by
 obtain ⟨r,k,a⟩:=h
 have t:∀s,∃ F g,(∃ f h,Ala P p C r s f h)→Ala P p C r s F g:= by
   intro s
   by_cases z:∃ f h,Ala P p C r s f h
   · obtain ⟨f,h,v⟩:=z;exact ⟨f,h,fun _=>v⟩
   exact ⟨0,0,fun u=>(z u).elim⟩
 choose F g v using t
 choose X gX using (fun s=>tulle P p C (s:=s) (F s) r k)
 obtain ⟨u,m,B⟩:=snowglobe P p X (fun s=>(gX s).1)
 choose j jX using B
 refine ⟨r∘u,fun s=>F s∘u,g,fun s=> rail P∘ X s∘u,j,k.comp m,?_⟩


 filter_upwards [a] with s c
 have z:=v s c
 have y:=stirs p m z.rolls
 exact ⟨⟨m.tendsto_atTop.eventually z.path,y, fun _=> y.stillHalf P _,z.lit,z.stellar⟩,
     jX s,m.tendsto_atTop.eventually ((gX s).2 z.path)⟩
end YM.CF.Merino.Tiara
