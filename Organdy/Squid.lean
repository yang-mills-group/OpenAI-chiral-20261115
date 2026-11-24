import Organdy.Thrum
import Organdy.Walrus
import Organdy.Fleece
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Topology Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel
open Swell StressExchange Buffered
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra

open _root_.Zephyr.Chern


open Vale Py Py.Rate LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection
open BPress (PL NPL)

/-- normalization (128), plus weight for (129). -/
abbrev Yen (L:Side)(x:ℝ) := pinpr L x / (Pressure.temp x)^2
variable {N:Side}
abbrev Pearl (L:Side)(x:ℝ) (K:Scree.Loom N)(p:BudgetPoint)(o:Site N)(J:Axis→ SOp N)(X:SOp N)(m:ℕ):=
  (Yen L x:ℂ) • Yc K p o J X m
abbrev Coral (L:Side)(x:ℝ) (K:Scree.Loom N)(p:BudgetPoint)(o:Site N)(J:Axis→ SOp N)(X:SOp N)(m:ℕ):=
  (hueW L x:ℂ) • Yc K p o J X m
lemma pearlCoral (L:Side)(x:ℝ) (K:Scree.Loom N)(p:BudgetPoint)(o:Site N)(J:Axis→ SOp N)(X:SOp N)(m:ℕ):
 Coral L x K p o J X m = (stemS x:ℂ) • Pearl L x K p o J X m:=by
 rw [Coral,hueW,Pearl,Yen,smul_smul,Complex.ofReal_mul,mul_comm]

variable (P:Spine)(i k s:ℕ)
local notation "Λ"=>P.par
local notation "xt"=>hat (Λ).R.L (Λ).x s
local notation "N'"=> age P.run i s
local notation "KL"=> (P.run.voyage i).CapeT s
local notation "R✤"=>RootBook P.run i k s

local notation "p'" => (R✤).p
local notation "mA"=> Moire.bloom (R✤).J.P
local notation "mS"=> PresN P i k s
local notation "hue"=> hueW (Λ).R.L xt
local notation "Q'"=> pinpr (Λ).R.L xt
local notation "n'" => ((p').B/10)
abbrev remPay (p:BudgetPoint)(a b:ℝ) := Real.exp (-a*((p.B/10:ℕ):ℝ))*b

/-- raw values with (129) normalized version; all and the opening use the
**same** truncation. Here T,Y are paid discarded kernels. -/
structure Kit (o:Site N') (m:ℕ)
 (a b:ℝ) (J T:Axis→SOp N') (X Y:SOp N'):Prop where
 medal(t:Axis): Trunk (node o) (J t) n' a b (Λ).d
 spurt(t:Axis): Soak (node o) (T t) a (remPay p' a b) (Λ).d
 knot: Trunk (node o) X n' a b (Λ).d
 shave: Soak (node o) Y a (remPay p' a b) (Λ).d
 hem(l:Axis)(z:Openc (More N') (Λ).d): spur (millIntro mS mA) o l m z.val=J l z.val + T l z.val
 bone(z:Openc (More N') (Λ).d): (mS z.val - tickA N')*windmill o m=X z.val+Y z.val

structure Squid (m:ℕ)(o:Site N')
 (a b:ℝ)(F D:ℝ→ℝ) (J T:Axis→SOp N') (X Y:SOp N')(V:Sour.Bag N'):Prop
 extends Kit P i k s o m a b J T X Y where
 appointment :
    Cymbal (Porch p' o) (Coral (Λ).R.L xt KL p' o J X m)
       ((hue:ℂ) • puffLine KL p' o J X m)
       (hue*yInvoice b)
 flight :
    Nest (Λ).U R✤ KL (Λ).J.n 24 (node o) (Λ).h (rScale p')
      ((hue:ℂ) • puffLine KL p' o J X m) V
       (F xt) (D xt * Q')

/-- Auxiliary but genuinely simultaneous. Supports M2 launches and pays (124)
already on this pre-scaling. a',b' need not price the same choice of
decomposition of S,T as Kit. -/
structure Tide (m w:ℕ)(a' b':ℝ):Prop where
 solo: Solo a' b' mS (Λ).d ∧ Solo a' b' mA (Λ).d
 docks: DockPulse p' KL (Λ).J.k (Λ).d a' (Λ).h 32 24 (Λ).J.n
 pilots: Staffer mS mA (Λ).d
 roundZ:(Λ).U.roundZ≤(N').val
 noslip:(R✤).slip=0
 radius: (p').B=Pressure.radiusB xt
 orderP: (p').order=6
 powerP: (p').power=2
 sphere: (p').threshold=Pressure.temp xt
 strobe: (p').supportExponent=1
 shell : Sectoral p' (Λ).J.n (scald p' (Ione.head_L (R✤).F))
    (Λ).h (rScale p' + (↑(p').B:ℝ)⁻¹) (RΓK p' (Λ).R.L xt)
 room: w≤n'
 lot:24*m+4≤(p').B
 stages:StageSet KL p' (Λ).d
 qPos : 0<Q'
 hPos : 0<hue

/-- Positive masked affine jet for *all* permitted openings and the
actual funded one (same, origin). Uniformity includes all periods. -/
structure Pearling (P:Spine)(m:ℕ)(a b a' b' D δ:ℝ)(w:ℕ)
 (f g:ℝ→ℝ):Prop where
 rosy: Rosy P a b P.par.d m D δ w
 slope : 0<a
 cost: 0<b
 cold : NPL f
 down : NPL g
 slopeAux : 0<a'
 coat : ∃ c, f=coatFull P.par.R.L (P.run.meter.a 0) m P.par.h a c b ∧ g=coatVoid P.par.R.L (P.run.meter.a 0) m P.par.h a c b
 costAux : 0<b'
 appointment :
   ∀ᶠ s:ℕ in atTop, ∀ᶠ i:ℕ in atTop, ∀ k:ℕ, s<P.run.uv k →
   let N:=age P.run i s
   let Q:=RootBook P.run i k s
   Tide P i k s m w a' b' ∧
   (∀ J T X Y, Kit P i k s 0 m a b J T X Y →
    Flourish N (PresN P i k s) m
     (chime ((P.run.voyage i).CapeT s) Q.p (node 0) X) Y D
     (D * Real.exp (-a*((Q.p.B/10:ℕ):ℝ))) δ) ∧
   ∀ o:Site N,∃ J T X Y V,Squid P i k s m o a b f g J T X Y V

/-- Combine factorium, (124) and the mask budget spatial and angular.
In particular go back to a *single* RootBook for all, the same period and
UV choices on the elected path. -/
theorem boughtPearls {Mc:ℕ}(W:Stakes Mc P)(m:ℕ)(t:0 < m):
 ∃ a b a' b' D δ w f g, Pearling P m a b a' b' D δ w f g:=by
 have h:=W.first.roster.prepared
 obtain ⟨a,b,f,g,u,v,r,l,cz,H⟩:=factoriumCoat P.run h W.visa W.rate m
 obtain ⟨a',_,b',_,_,y,_,z,_,_,E⟩:=statements P.run h W.rate W.visa m
 obtain ⟨D,δ,w,paid⟩:=rosyPaid P u v (P.par.dpos) t
 refine ⟨a,b,a',b',D,δ,w,f,g,paid,u,v,r,l,y,cz,z,?_⟩
 let Λ':=P.par; let R:=Λ'.R.L; let tt:=hat R Λ'.x
 have G:Tendsto (Pressure.radiusB ∘ tt) atTop atTop:=
    Work.E01.radiusB_tendsto.comp (turnover P.par)
 filter_upwards [G.eventually_ge_atTop (100*(w+m+Λ'.J.n+1)),
   (turnover P.par).eventually (draft_π R),H,E,paid.intact] with s₀ hg draft ff tt' U
 filter_upwards [ff,tt'] with i₀ resource active k₀ eligible
 intro N Q
 obtain ⟨B,P',L,M,round,slide,_,hi,hr,hp,ht,h1,sector,_⟩:=active k₀ eligible

 let K:=(P.run.voyage i₀).CapeT s₀
 have ks : 100*(w+m+Λ'.J.n+1) ≤ Q.p.B:=hi.symm ▸ hg
 have h₁:w ≤ Q.p.B/10:=by omega
 have h₂:24*m+4≤Q.p.B:=by omega
 have h₃:Q.p.B/10+Λ'.J.n≤Q.p.B:=by omega
 have X:StageSet K Q.p Λ'.d:= ⟨P.par.dpos,_,_,_,L.roof,L.reach,le_rfl,h₃⟩
 obtain ⟨_,e,_,_,j⟩:=draft
 have qx:0<pinpr R (tt s₀):= j.symm ▸ pow_pos e _
 have hpw:0<hueW R (tt s₀):= by
   have hh:0<Pressure.temp (tt s₀):= ht ▸ Q.p.threshold_pos
   unfold hueW stemS; exact mul_pos (div_pos qx (sq_pos_of_pos hh)) (Real.rpow_pos_of_pos (BPress.drift_pos _) _)
 refine ⟨⟨⟨B,P'⟩,L,M,round,slide,hi,hr,hp,ht,h1,sector,h₁,h₂,X,qx,hpw⟩,?_,?_⟩
 · exact fun J T XA Y F=>U _ _ _ _ _ _ h₁ (dressing X) F.knot F.shave F.bone

 intro o
 obtain ⟨J,T,XA,Y,mo,ta,kn,vs,he,bo,bag,nestZ⟩:=resource k₀ eligible o
 refine ⟨J,T,XA,Y,bag,⟨mo,ta,kn,vs,he,bo⟩,?_,nestZ⟩
 have ht:=(standY (dressing X) u.le h₂ kn mo).resize (hueW R (tt s₀):ℂ)
 rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hpw] at ht; exact ht
