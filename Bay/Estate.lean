import Bay.Kettle
import YM.SU5.Exchange.Visa.Moon
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

open Py Py.Rate LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection
open Zephyr.Chern
open BPress (PL NPL)
local notation "fluxV"=>Zephyr.Chern.stream
local notation "VΩ"=>Buffered.Afterglow.Tower.VacuumSelection.Spine


open Buffered.Afterglow.Tower
open Buffered.Afterglow.Tower.VacuumSelection.Spine Pitching.Focus
open Push.SectorMeasure
open QuadClock Preparation.Yoke

def spaceW (P:VΩ)(s:ℕ):ℝ:=1/(P.par.R.L.val:ℝ)^s
-- physical macro step: t_s=2m in gauge clock units, m matter
lemma tickW (P:VΩ)(s:ℕ):
  P.macroStep s = (↑(tabW P):ℝ) * spaceW P s ∧
  SlabMark.ruler P.par.block = 2 * (↑(tabW P):ℤ):=by
 refine ⟨?_,by unfold tabW SlabMark.ruler; push_cast; ring⟩
 simp only [macroStep,timeMesh,MeshClock.mill,spaceW,tabW,NNReal.coe_div,NNReal.coe_pow,
     NNReal.coe_natCast]
 push_cast; ring

open Ione Vow
universe u
structure Hammer (P:VΩ)(Mc:ℕ)(X:TintDemand) : Prop where
 gate:Gate P
 rates:RateStamp P.run
 steady:Compass_sol P.run
 leases:FirstLease P
 floor: 8 ∣ P.par.M.val
 cover: ∃ (n:ℕ)(Pay kc G : ℝ)(Tξ:Hove.Grant P.par.K.j 2),
     ((2+(Mc:ℝ))*Ione.strive_E 6)<(n:ℝ) ∧
     0≤Pay ∧ 0≤kc ∧ 0≤G ∧ Taxi.DayT 6 G ∧
     crayon X P.par.K P.par.L Pay kc G Tξ ≤ P.par.R.L.val ∧

     (Neon.KX 5)^3<P.par.R.L.val ∧
     (Neon.PKard 5)^3<P.par.R.L.val ∧
     10≤P.par.R.L.val∧
     RateCover P.par.J Chi.canonical P.par.h P.par.N0 Pay kc G Tξ n P.par.P ∧
     Sweepcraft P.run Tξ Pay kc G n Mc

/-- Same Tuple with crayon & Sweep purchases retained **up to** choose-good.
    In particular exports FirstLease hence Post124. cf planetaryPolar. -/
lemma harbor (Mc:ℕ)(X:TintDemand):
  ∃ (P:VΩ)(K:P.Register), Hammer P Mc X ∧
    ∀ (good : P.Spectrum0 3 → Prop),
      (∀ᵐ x ∂ P.pillars 3, good x) →
      ∃ x,good x ∧ JointTuple.{u} P K x:=by
 obtain ⟨n,h⟩:=exists_nat_gt ((2+(Mc:ℝ))*strive_E 6)
 have hz :0≤ strive_E 6:= by unfold strive_E Jet.composeCost; positivity
 obtain ⟨P,K,q,r,H,⟨T,t⟩,j,y,hv,hy,D,⟨C,_,_,p⟩,a,k⟩:=
    bookedS n (le_trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Nat.cast_nonneg _):(2:ℝ) ≤ 2+Mc) hz) h.le)
       X blankSupplier 1 1 zero_lt_one
 obtain ⟨Pay,kC,Γ,Tξ,v₀,v,s,Z,w,p1,p2,πx,m⟩:= T.fromCrew
 have ht : Odd P.par.R.L.val:= ⟨P.par.R.L.val/2,by omega⟩

 have ink:= RateCover.includes _ _ _ m
 have tc:TintCommercial n (crayon X) P.par:=⟨Pay,kC,Γ,Tξ,v₀,v,s,Z,w,p1,p2,πx,ink⟩
 exact ⟨P,K,⟨r.prepared,EarningsRate.atMask P.run (RateCover.stepRate m) r.prepared,
          visa_onPath P.run r.prepared t,
          ⟨r,⟨n,_,tc⟩,H,y,hv,j,D⟩,
          hy,n,Pay,kC,Γ,Tξ,h,v₀,v,s,Z,w,p1,p2,πx,m,
          bandRadius P.run (ink.staysOn (by rw [P.par.kJ]; exact ⟨2,rfl⟩)
          P.par.kJ.ge v₀ v Z s p1 p2 Mc
          ((mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by norm_num)) hz).trans h.le))
          r.prepared⟩,
      Buffered.Afterglow.Tower.VacuumSelection.Spine.reside.{u} P K q r H ht k p⟩

/-- Single orientation, single root: joint specification.
    Bourne.cradle.1 vends emblem_pure for the u in SignY.
    Existence of priced stencils & centering. -/
structure Bourne (w:Berth)(a c b W δ:ℝ)(m:ℕ):Prop where
 cradle:Rigs a c b m w
 swell: ∃ f V,
     w.Before a b m (w.home corner) f ∧
     Beau (w.smallFlow (w.home corner) f) (w.fluxBare (w.home corner) m)
                δ (W*w.wid a b) ∧
     gem (w.priceFlow (w.home corner) f) (w.price*δ) ∧
     w.WearY m (w.home corner) f a c b V ∧
     w.SignY m (w.home corner) f V b

/-- Bay1 offerings. -/
def OfBay1 (P:VΩ):Prop:=
  let m:=tabW P
  ∃ a c b W δ:ℝ,0<a ∧ 0<c ∧ 0<b ∧ 0<W ∧ 0<δ ∧
      NPL (till129 P a c b m) ∧ NPL (reserve129 P a c b m) ∧
      Dry P (fun w=> Bourne w a c b W δ m)

lemma Hammer.one {P:VΩ}{Mc:ℕ}{X:TintDemand}(f: Hammer P Mc X): OfBay1 P:=by
 obtain ⟨a,c,b,W,δ,ha,hc,hb,j,y,e,k,t⟩:=cupful P f.gate f.rates f.steady
 refine ⟨a,c,b,W,δ,ha,hc,hb,j,y,e,k,dryMono t ?_⟩
 rintro w _ ⟨hs,g,V,p,q,r,h⟩
 exact ⟨hs,g,V,p,q,r,h,Berth.wearSign hs.1 h⟩

theorem Bay1:
    ∃ (P:VΩ)(K:P.Register)(x:P.Spectrum0 3),
      JointTuple.{u} P K x ∧ FirstLease P ∧ Post124 P.run ∧
      SprigFee P ∧ OfBay1 P:=by
 obtain ⟨P,K,g,k⟩:=harbor.{u} 1 (fun _ _ _ _ _ _=>0)
 obtain ⟨x,_,m⟩:=k (fun _=>True) (Eventually.of_forall fun _=>True.intro)
 exact ⟨P,K,x,m,g.leases,g.leases.post,SprigFee.paid P,g.one⟩

#print axioms harbor
#print axioms Bay1
end YM.CF.Bay
