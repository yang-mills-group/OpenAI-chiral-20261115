import SU5SatinMarkedCurrentNovember7
import Merino.PublicPlume
import Merino.Retinue.Joust
import Merino.JadeEye.Basalt
import Merino.Bravura.Toccata
import Merino.Dais.Lode
import Merino.Dais.Drum
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 1500000
set_option maxRecDepth 4500
namespace YM.CF.Merino
open Filter Lattice Buffered Afterglow Tower Tower.VacuumSelection 
    Py.Rate.LocalLimit Preparation
open Dais Tiara Bravura
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator Classical
variable (P:Spine)(p:Bolts)(Mc:ℕ)(C:Plume.Constellation)


open Py Lifted Plume

/-- Explicit seal *on the subsequence*. Wickday included (can use any
Gown). Arrival includes Worthy. J and Z invoices immediately included,
also at stage s+1. Div+ readings use Tailored where needed. -/
def Confluence:Prop:=
 ∃ (r:ℕ→ℕ)(F:ℕ→ℕ→LinksC→ℂ)(g:ℕ→LinksC→ℂ)
  (Y:ℕ→ℕ→Reins P.calibration)(J:ℕ→Reins P.calibration)
  (E D:ℝ→ℝ)(Pay kc Γf:ℝ) (T:Hove.Grant P.par.K.j 2) (n:ℕ)
  (Z W V1 Kf:ℝ→ℝ),
   StrictMono r ∧ Diva.{0,0} P C g J ∧ BPress.NPL E∧ BPress.NPL D∧
   Sweepcraft P.run T Pay kc Γf n Mc ∧ BladeQ P.par.R Z W V1 Kf ∧
   ∀ f u:ℕ, ∃ dJ dZ:ℕ,
    ∀ᶠ s in atTop,
    Unison P p C r f (s+1) (F (s+1)) (g (s+1)) (Y (s+1)) (J (s+1)) ∧
    Setout P (s+1) C (g (s+1)) ∧
    ∀ᶠ j in atTop,
     let i:=P.nomadic (r j)
     let k:=P.engine (r j)
     Tailored P p (s+1) i k C (F (s+1) j) (Y (s+1) j) ∧

     Arrival P s i k p (liftCoat P Pay kc Γf T n) Γf Mc Z W V1 Kf f u
       (|E (scaleM P (s+1))|) (|D (scaleM P (s+1))| * Qprice P (s+1)) ∧
     Retinue.Court P (s+1) i k p dJ f u∧ JadeEye.Court P (s+1) i k p dZ f u ∧
     (∀ d t,Medal.Strut (scaleM P (s+1)) t→t%2=0→∀ σ,
        Wickday P p f (s+1) i k d t σ)


theorem confers (a:Cotillion P p Mc)(b:Retinue.Dressage P p)(d:JadeEye.Dressage P p)
 (w:Charms P p)(z:Fanfare P p C):Confluence P p Mc C:=by
 obtain ⟨E,D,Pay,kc,Γf,T,n,Z,W,V,L,a1,a2,a3,a4,a5⟩:=a
 obtain ⟨r,F,g,Y,J,e1,e2,e3⟩:=z
 refine ⟨r,F,g,Y,J,E,D,Pay,kc,Γf,T,n,Z,W,V,L,e1,e2,a1,a2,a3,a4,?_⟩
 have t:= P.stockGo.comp e1.tendsto_atTop
 intro f u
 obtain ⟨j,b⟩:= b f u
 obtain ⟨k,d⟩:= d f u
 refine ⟨j,k,?_⟩
 filter_upwards [a5 f u,later b,later d,later (w f),later (e3 f)] with s a h i y l
 refine ⟨l.1,l.2,?_⟩
 filter_upwards [t.eventually a,t.eventually h,t.eventually i,t.eventually y,l.1.1.fitted]
    with v a h i y l
 have u':= l.1
 exact ⟨l,a _ u'.1,h _ u'.1,i _ u'.1,y _ u'⟩


universe u
/-- Checkpoint. No premises except fixing Mc, no conclusions as yet
about the antecedents of Diva, or an interacting continuum/current on
the selected vacuum. -/
theorem revel (Mc:ℕ):
 ∃ P K x p, Spine.RibbonCourts.{u} P K x Mc ∧
  Dazzles P p ∧ Coin.Windfall P p ∧ Dais.Cotillion P p Mc ∧ Tiara.Charms P p ∧
  Mitre.Rosette P p ∧ Retinue.Dressage P p ∧ JadeEye.Dressage P p ∧
  ∃ C:Plume.Constellation, twinkling P p C.α C.δ C.bigE C.r C.L ∧
   Plume.Hill P p C ∧
   Bravura.Fanfare P p C ∧ Confluence P p Mc C:=by
 obtain ⟨P,K,x,p,j,w,C,a,b⟩:=assembledPlume.{u} Mc
 have c:=Coin.acquisition P p j
 have z:=Dais.hosted P p Mc j.gala c
 have v:=Tiara.favored P p c
 have t:=Mitre.finery P p c
 have l:=Retinue.charged P p j.gala
 have m:=JadeEye.charged P p j.gala
 have r:=Bravura.outlay P p (Bravura.laureate P C p (Tiara.crowned P p b v))
 exact ⟨P,K,x,p,j,w,c,z,v,t,l,m,C,a,b,r,confers P p Mc C z l m v r⟩

#check revel
#print axioms revel

#print axioms Brooch.Gifts.earns
#print axioms Coin.Worthy.reward
#print axioms Dais.cavalcade
#print axioms Dais.minor
#print axioms Dais.transported
#print axioms Dais.proximity
#print axioms Dais.sounding
#print axioms Retinue.solves
#print axioms JadeEye.solves
#print axioms Tiara.scepter
end YM.CF.Merino

