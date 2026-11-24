import Merino.Plume.Ala
import Merino.Tiara.Bead
import Merino.Tiara.Canopy
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


abbrev Scarf(s:ℕ):= Signed→Axis→Tassels (Lattice.box (etch P s))
abbrev rail {s}(x:Scarf P s):Reins P.calibration:=
 fun σ i'=> braid P.calibration (x σ i')
abbrev Osmium(s:ℕ)(x:Scarf P s):Prop:=
 ∀σ a,Gilt (etch P s) (tempM P s) (p.c+p.c)
 (2*cable (etch P s) p.c P.par.d) P.calibration (x σ a)
-- send, µ
lemma sideVal:P.calibration.c (momentm P.run i s)=RegNum P s i:= terrain ..

def Tailored (C:Constellation) (F:LinksC→ℂ)(x:Reins P.calibration):Prop:=
 merrier P s i k ∧ ∃ d:Gown P p (priceTick P) s i k,
   Glowing P (priceTick P) p zeroBase s i k C.δ C.bigE d ∧
   (∃ T,Emblem P p s i k C.α C.r C.L C.ε d T) ∧
   F=badge P p s i k d ∧
   F∘onC Ω= traceCost K (Γ).p d.y.post d.y.color ∧
   ∀σ a,ship (sideVal P s i) (x σ a (momentm P.run i s))=
     toMark (prance (rim Ω σ) (d.y.jPole K (Γ).p a))

variable {s i k}
theorem taffeta {C:Constellation}{F}
 (t:Tivoli (Lattice.box (etch P s)) (P.calibration.c (momentm P.run i s)))
 (w:warrant P p C s i k F)
 (h:etch P s+1<(RegNum P s i).val):
 ∃x:Scarf P s,Osmium P p s x ∧ Tailored P p s i k C F (rail P x):=by
 obtain ⟨c,d,m,f,rfl,_⟩:=w
 rw [sideVal P s i] at t
 let R:= LedgerM P s i k
 let o:=node d.y.origin
 have y:separation 0 o≤4:=by unfold o;rw [d.here];exact home_fits _
 have g:fitted (etch P s) o R.p:=
    ⟨h, by unfold etch;rw [←d.hot.claims];exact space_at (b:=R.p.B) y le_rfl⟩
 have X:= d.ticket.hem.sip


 have u:=calibrated (s:=s) (i:=i) P d.hot.admit.2.le
 have z:(R.p).threshold=tempM P s:=by unfold R;rw [u.1];exact (P.run.meter.boot _).1
 have rad:R.p.B+16=etch P s:=by unfold R etch;rw [d.hot.claims]
 have e:badge P p s i k d∘onC Ω=traceCost K (Γ).p d.y.post d.y.color:=by
    have ha:= funext (cut_period d.hot.sky p.decay.le X g)
    unfold badge lure_origin
    rw [←show d.y.post=node _ from congrArg node d.here]
    exact ha
 have j(σ:Signed)(a:Axis):=fancy_at (sideVal P s i) t
   (floss (rim _ σ) d.ticket.hem rad (rim0 σ) y z a)
 choose x r using j
 exact ⟨x,fun σ a=>(r σ a).1,c,d,m,f,rfl,e,fun σ a=>(r σ a).2⟩


-- Across a Hill.
lemma tulle (C:Constellation){s:ℕ}(F:ℕ→LinksC→ℂ)
 (r:ℕ→ℕ)(hr:StrictMono r):
 ∃x:ℕ→Scarf P s, (∀n,Osmium P p s (x n))∧
 ((∀ᶠ j in atTop, warrant P p C s (P.nomadic (r j)) (P.engine (r j)) (F j))→
   ∀ᶠ j in atTop,Tailored P p s (P.nomadic (r j)) (P.engine (r j)) C (F j) (rail P (x j))):=by
 let a(j:ℕ):=P.nomadic (r j)
 let c(j:ℕ):=P.engine (r j)
 let d(j:ℕ)(x:Scarf P s):=
    Osmium P p s x∧Tailored P p s (a j) (c j) C (F j) (rail P x)
 have t:∀j,∃x:Scarf P s,Osmium P p s x∧((∃y,d j y)→d j x):=by
    intro j
    by_cases h:∃y,d j y
    · obtain ⟨y,g⟩:=h;exact ⟨y,g.1,fun _=>g⟩
    have u:=p.crown.le
    exact ⟨_,fun _ _=> void (add_nonneg u u)
       (mul_nonneg (by norm_num) (cable_pos _ u _)),fun k=>(h k).elim⟩


 choose x h using t
 refine ⟨x,fun j=>(h j).1,fun w=>?_⟩
 have v:=P.stockGo.eventually (turning P.run P.large s (Lattice.box (etch P s)))
 have h2:=(P.amount_go s).eventually_gt_atTop (etch P s+1)
 filter_upwards [w,hr.tendsto_atTop.eventually v,hr.tendsto_atTop.eventually h2] with j y a b
 exact ((h j).2 (taffeta P p a y b)).2
end YM.CF.Merino.Tiara
