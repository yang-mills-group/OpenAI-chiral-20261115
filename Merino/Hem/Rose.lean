import Merino.Hem.Agate
import Merino.Hem.Selvedge
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Hem
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


open Cuff

lemma home_fits (n:Side): separation 0 (node (wrap n zeroBase))≤4:=by
 have t:wrap (More n) 1=1:=by ext;change ((1:ℤ):Per (More n))=(1:Per _); simp
 rw [separation_comm,node_wrap,separation,sub_zero]
 rw [←t] -- tune
 rw [←map_add]
 exact (pdist_wrap ..).trans (by simp [zeroBase,Laurent.size])

lemma ss_stars (m:ℕ)(l:List Axis)(x:Site n):
    star (squareSum millQ m l x)=squareSum millQ m l x:=by
 induction l generalizing x with
 | nil =>
    rw [squareSum,millstock]
    exact (Tye.stockX _ false).1
 | cons a l ih=>
    simp [squareSum,stripSum,star_sum,ih]

open Spire
lemma tick_stars(n:Side):star (Dial.tickA n)=Dial.tickA n:=by
 rw [touchP]; ext i j
 change star (Fock.cutM _ j i)=_
 by_cases h:i=j <;> simp [Fock.cutM,h,Ne.symm]

lemma honest (x:Site n)(M:Op (Single n))(h:star M=M)(m:ℕ):
    ((M-Dial.tickA n)*windmill x m).trace.im=0:=by
 let X:=M-Dial.tickA n; let Y:=windmill x m
 have w:star X=X:=by simp [X,h,tick_stars]
 have c:star Y=Y:=ss_stars ..
 have e:star (X*Y).trace=(X*Y).trace:=by
    rw [←Matrix.trace_conjTranspose,←Matrix.star_eq_conjTranspose,star_mul,w,c,
      Matrix.trace_mul_comm]
 have p:=congrArg Complex.im e; rw [Complex.star_def,Complex.conj_im] at p
 change (X*Y).trace.im=_; linarith

variable (p:Bolts)(m s i k:ℕ)
local notation "b"=>zeroBase
local notation "N"=>RegNum P s i
local notation "K"=>LoomM P s i
local notation "R"=>LedgerM P s i k

abbrev Gown (P:Spine)(p:Bolts)(m s i k:ℕ):=Dress P s i k p m (wrap _ zeroBase)
abbrev lure_origin (d:Gown P p m s i k):Pane N→ℂ:=
   traceCost K (R).p (node (wrap _ zeroBase)) d.y.color
def lure (d:Gown P p m s i k):Pane N→ℂ:=pstar (lure_origin P p m s i k d)

lemma honest_charge (d:Gown P p m s i k)(V:Pane N):
    |(lure_origin P p m s i k d V).im|≤loseM P p.a s*p.c:=by
 unfold lure_origin traceCost masked
 by_cases h:V∈pass (R).p (node (wrap _ zeroBase))
 · rw [Set.indicator_of_mem h]
   let z:Orbit N:=(V,fixedTags _)
   let x:=d.hot.sky.slot z
   have e:= congrArg Matrix.trace (d.glaze_funds x)
   rw [Matrix.trace_add] at e
   have w:=congrArg Complex.im e
   change ((Dial.spar P.par.K.j (R).J.M (K z)-Dial.tickA N)*windmill _ _).trace.im=_ at w
   rw [honest _ _ (d.hot.usable z).isSelfAdjoint _,Complex.add_im] at w
   change |(d.y.color x.val).trace.im|≤_
   rw [eq_neg_of_add_eq_zero_left w.symm,abs_neg]
   exact (Complex.abs_im_le_norm _).trans (soak_trace d.wane x p.decay.le)
 rw [Set.indicator_of_notMem h]
 have a:=p.crown; simp; unfold loseM; positivity

abbrev etch (P:Spine)(s:ℕ):=radiusM P s+16
abbrev Etched (P:Spine)(p:Bolts)(m:ℕ)(r C δ:ℝ)(s i k:ℕ):Prop:=
  ∀ d:Gown P p m s i k,
   ∃ T:InkFace (RegNum P s i), δ<dripQ T (needle _) (needle _) ∧
    Scar (etch P s) (tempM P s) r C (loseM P p.a s*p.c)
      (lure P p m s i k d) T
lemma rosebud (h:SprigFee P)(hm:0 < m):
   ∃ r C δ:ℝ,0<r∧0<C∧0<δ∧onReg P (Etched P p m r C δ):=by
 obtain ⟨δ,e,f⟩:=wreathing P h hm zeroBase p
 obtain ⟨r,D,u⟩:=Room.reserve P.par.dpos
 let B:=D*(quota^2*p.c)
 let C:=max (B*(tow p.a)^2) (max B p.c)
 have c:p.c≤C:=le_trans (le_max_right ..) (le_max_right ..)
 refine ⟨r,C,δ,u.haveR,p.crown.trans_le c,e,?_⟩
 unfold onReg at *
 filter_upwards [f] with s g
 filter_upwards [g,(regnum_big P s).eventually_gt_atTop (4*(lead (radiusM P s/10)+8)+1)]
    with i j l k w d
 have v:=d.hot.claims
 rw [←v] at l
 have x:=d.ticket.hem.sip
 change Trunk (node d.y.origin) _ _ _ _ _ at x
 rw [d.here] at x
 have t:(LedgerM P s i k).p.threshold=tempM P s:=by
   rw [(calibrated P w.2.le).1]; exact (P.run.meter.boot _).1
 unfold etch
 rw [←v,←t] -- may rewrite too much?
 exact flocked u d.hot.sky x p.decay (home_fits _) l (le_max_left ..)
  ((le_max_left B p.c).trans (le_max_right ..)) c (honest_charge P p m s i k d)
   (j k w d)
