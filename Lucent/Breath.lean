import Lucent.Drill
import Lucent.Gist
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.Lucent
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Buffered Buffered.Lifted Skye MeasureTheory NormedSpace
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
open Ballad EmberWind Window Lamour.Bridge Celeste
open WakeInvestment

open Peaks Scree
open Pannier.Chancel Py.Rate.Pannier
open Cube Laic Buffered.Afterglow Journey Dial
open Rous Pressure Worth
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
variable (s i k:ℕ)
set_option quotPrecheck false
local notation "■" => RootBook Y i k s
local notation "ℕ'" => side Y i s
local notation "flatP" => Dial.spar P.K.j (RootBook Y i k s).J.M (1:Pane (side Y i s))
open Buffered.Afterglow
open Window Cliplet

open Vale
open Worth.Pays Jewel WakeInvestment Regis Gleam Pressure Laurent
open Gleam.Wake
local notation "X" => hat P.R.L P.x s
local notation "σ" => sPow P s
variable {I:Type} [Fintype I] {m d:ℕ}
/- Exponent inflation. separate gauge degree and geometry cost. -/

open Regis.Circuit Regis.Head.Brecht Regis.Resonance Exterior Gist
open ProbabilityTheory Precision RG
local notation "vuseq"=> reachCost Y s i k 
local notation "Bd"=> P.V.L.H (Y.uv k-s)
local notation "GN"=> More (side Y i s)

-- unscaled Wick payment
local notation "ϙ" => P.V.L.mood (Y.uv k-s)
local notation "ħ" => P.V.L.tied (Y.uv k-s)
local notation "BE"=> stamen ϙ ħ GN 

abbrev emittance (N:Side)(W:I→Staff)(t:Tint I) : Body 2 (More N):=
 (wrap (More N) (W t.1).face.1, plaquette (W t.1).face.2)
def splitG (N:Side)(H: Bed)(u:ℝ)(W:I→Staff)(t z:Tint I):ℂ:=
 (sch (G:=SU.group) t.2 z.2:ℂ) * (u:ℂ)^2 * rimble (More N) H (emittance N W t) (emittance N W z)
variable (ρ:ℝ) (W:I→Staff)
abbrev yolk (t:Tint I): BE := (plar ϙ ħ (emittance ℕ' W t) (vuseq ρ)) t.2
def heed (G:Tint I→ Tint I → ℂ) (p:List (Loop I)→ℂ)(j:Join I):ℂ:= vell G j.flash * p j.loom

local notation "qB"=> P.K.top.clip
local notation "price"=>splitG ℕ' Bd (vuseq ρ) W
lemma link_duet(t z:Tint I):
    (inner ℝ (yolk Y s i k ρ W t) (yolk Y s i k ρ W z):ℝ)= price t z:=by
 let D:= P.V.L.roof (Y.uv k-s)
 have p:Even (GN).val:=⟨(ℕ').val,by change (ℕ').val*2=_; omega⟩
 have hv:= chimes ϙ ħ (D.2.1 GN) D.1 P.K.width t.2 z.2 (emittance ℕ' W t) (emittance ℕ' W z) p
 simp_rw [←joy,appraisal] at hv; rw [yolk,yolk,plar,plar,real_inner_smul_left (trill ϙ ħ t.2 (emittance ℕ' W t)) ((vuseq ρ) • (trill ϙ ħ z.2 (emittance ℕ' W z))), real_inner_smul_right (trill ϙ ħ t.2 (emittance ℕ' W t)) (trill ϙ ħ z.2 (emittance ℕ' W z))]
 rw [splitG]; push_cast; rw [hv]; ring
lemma hatchY (F:(Tint I→ℝ)→ℂ)(x:BE) :
 (VesselR W ℕ').basin (vuseq ρ) F qB x.val=F (fun t=>spanX (yolk Y s i k ρ W t) x):=by
 obtain ⟨v,rfl⟩:=song ϙ ħ x; have e:( (tiler ϙ ħ).rangeRestrict v).val=tiler ϙ ħ v:= rfl; rw [e,Vessel.belly ϙ ħ]; apply congrArg F; funext t; rw [spanX,yolk,plar,real_inner_smul_left (trill ϙ ħ t.2 (emittance ℕ' W t)) ((tiler ϙ ħ).rangeRestrict v),joy]; rw [emittance,inspire]; rw [e,Head.Etch.river_now qB ϙ ħ]

lemma paya {E:Type}[NormedAddCommGroup E][InnerProductSpace ℝ E] (L:List (Tint I))(φ:Tint I→E)(x:E):
   glint (fun t=>spanX (φ t) x) L=↑(payday (L.map φ) x):=by
 induction L with
 | nil=>rw [glint_nil,show payday (([]:List (Tint I)).map φ) x=1 from rfl,Complex.ofReal_one]
 | cons i L h=> rw [glint_cons,h,List.map_cons]; change _= (↑(spanX _ x * payday _ x):ℂ); rw [Complex.ofReal_mul]

lemma breath_bill (S:Stencil I): dontStop Y s i k W ρ S = S.quote (heed price (press Y s i k W)):= by
 let μ:= stdGaussian (BE); let φ:= yolk Y s i k ρ W
 let g(j:Join I)(x: BE):ℂ:= ↑(payday (j.flash.map φ) x)*press Y s i k W j.loom
 let v (S:Stencil I)(x: BE) := S.quote (fun j=>g j x)
 have he(j: Join I): Integrable (g j) μ ∧ (∫ x,g j x ∂μ)= heed price (press Y s i k W) j:=by
    unfold g heed
    constructor
    · apply Integrable.mul_const
      exact (payday_val _).accepted.ofReal
    rw [integral_mul_const,integral_complex_ofReal]
    exact congrArg (· * _) (vellWick price φ (link_duet Y s i k ρ W) j.flash)
 rw [dontStop,seatT]; change (∫ x:BE,(VesselR W ℕ').basin (vuseq ρ) (icing Y s i k W S) qB x.val ∂μ)=_
 have hY(x:BE): (VesselR W ℕ').basin (vuseq ρ) (icing Y s i k W S) qB x.val= v S x:=by rw [hatchY Y s i k ρ W]; simp_rw [icing,paya]; rfl
 apply (integral_congr_ae (ae_of_all μ hY)).trans
 suffices ∀ T:Stencil I,Integrable (v T) μ ∧ (∫ x, v T x∂μ)=T.quote (heed price (press Y s i k W)) from (this S).2
 intro T; cases T with|mk L=>induction L with
 | nil=>exact ⟨integrable_zero ..,integral_zero ..⟩
 | cons b L h=>
   have hb:Integrable (fun x=>b.k*g b.toJoin x) μ:= (he _).1.const_mul b.k
   rw [show v {out:=b::L}=(fun x=> b.k*g b.toJoin x+v {out:=L} x) from rfl]
   exact ⟨hb.add h.1,by rw [integral_add hb h.1,h.2,integral_const_mul,(he b.toJoin).2];rfl⟩
