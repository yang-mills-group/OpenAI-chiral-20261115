import Bay.Rosace
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


abbrev takeUp (P:VΩ)(s i k:ℕ): Berth:= ⟨P,s,i,k⟩

/-- high s / large period at fixed s / uniform in all interior cutoffs. -/
def Dry (P:VΩ)(F:Berth→Prop):Prop:=
 ∀ᶠ s:ℕ in atTop, ∀ᶠ i:ℕ in atTop, ∀ k, s < P.run.uv k → F (takeUp P s i k)
lemma dryMono {P:VΩ}{F G:Berth→Prop}(p:Dry P F)(g:∀ w,w.P=P→F w→G w):Dry P G:=by
 filter_upwards [p] with s x
 filter_upwards [x] with i y k u
 exact g _ rfl (y k u)

def Rigs (a c b:ℝ)(m:ℕ)(w:Berth):Prop:=
 w.Rig a c m ∧ ∀x, ∃ f, w.Before a b m x f

def Gate (P:VΩ):Prop:=
 ∀ i k,((P.run.voyage i).X k).Prepared P.par.P P.par.delay
theorem calendar (P:VΩ)
  (g:Gate P)(r:RateStamp P.run)(p:Compass_sol P.run)
  (m:ℕ):
 ∃ a c b:ℝ,0<a ∧ 0<c ∧ 0<b ∧ NPL (till129 P a c b m) ∧ NPL (reserve129 P a c b m) ∧ Dry P (Rigs a c b m):=by
 obtain ⟨a,b,c,_,_,ha,hb,hc,_,_,v⟩:=statements P.run g r p m
 obtain ⟨i,j⟩:= coatMoney P.par.R.L (pStart P) P.par.h a c b m ha
 refine ⟨a,c,b,ha,hc,hb,i,j,?_⟩

 let x:=xTop P
 have hz:Tendsto x atTop atTop:=turnover P.par
 filter_upwards [v,
    (Work.E01.radiusB_tendsto.comp hz).eventually_ge_atTop
        (24*m+2*P.par.J.n), hz.eventually (draft_π P.par.R.L)] with s t w h
 change 24*m+2*P.par.J.n≤Pressure.radiusB (x s) at w
 obtain ⟨hx,hq,u,_,q⟩:=h
 have hqq: 0<pinpr P.par.R.L (x s):=q ▸ pow_pos hq 2
 filter_upwards [t] with i e k y
 obtain ⟨f,K,G,H,A,U,Y,pb,po,pf,tv,az,S,mc⟩:=e k y
 have z:24*m ≤ (RootBook P.run i k s).p.B ∧
         P.par.J.n + (RootBook P.run i k s).p.B/10 ≤ (RootBook P.run i k s).p.B:=by
   rw[pb];unfold x xTop at w;omega
 refine ⟨⟨y,f,K,G,H,A,U,Y,z,pb,po,pf,tv,az,hx,S,hqq⟩, fun o=>?_⟩
 obtain ⟨j,k,u,l,h,h₁,h₂,h₃,h₄,h₅⟩:=(mc o).tickets
 exact ⟨⟨j,k,u,l⟩,h,h₁,h₂,h₃,h₄,h₅⟩

namespace Berth
abbrev home (w:Berth)(z:Cover):Site w.side:=wrap _ z

abbrev Handsome (w:Berth)(a c b W δ:ℝ)(m:ℕ)(z:Cover):Prop:=
 ∀ f, w.Rig a c m→w.Before a b m (w.home z) f→
   Beau (w.smallFlow (w.home z) f) (w.fluxBare (w.home z) m) δ
     (W*w.wid a b)

end Berth
lemma existOil (a b W:ℝ)(P:VΩ)(ha:0<a):
 Tendsto (fun s:ℕ=> W*(exponentialR a (xTop P s) * b)) atTop (𝓝 0):=by
 have z:Tendsto (fun s:ℕ=>(↑(Pressure.radiusB (xTop P s)/10:ℕ):ℝ)) atTop atTop :=by
    apply tendsto_natCast_atTop_atTop.comp
    refine tendsto_atTop.2 (fun n=>?_);let f(s):= Pressure.radiusB (xTop P s)
    have h:Tendsto f atTop atTop:=Work.E01.radiusB_tendsto.comp (turnover P.par)
    filter_upwards [h.eventually_ge_atTop (10*n)] with s q
    show n≤f s/10
    omega
 have h:= ((Real.tendsto_exp_neg_atTop_nhds_zero.comp (z.const_mul_atTop ha)).mul_const b).const_mul W
 simpa only [Function.comp_def,exponentialR, neg_mul,mul_zero,zero_mul] using h


theorem handsome (P:VΩ)(a c b:ℝ)(m:ℕ)(j:0 < m)(z:Cover)(u:0<a):
  ∃ W δ:ℝ,0<W∧0<δ ∧ Dry P (fun w=> w.Handsome a c b W δ m z):=by
 let l:=List.ofFn (id:Axis→Axis)
 obtain ⟨W,⟨x⟩⟩:=oily u P.par.dpos (breadth z)
 obtain ⟨δ,hδ,v⟩:= goldCup P m j l z
 have hx:= (existOil a b W P u).eventually (ge_mem_nhds (half_pos hδ))
 refine ⟨W,δ/2,x.bound,half_pos hδ,?_⟩
 filter_upwards [v,hx] with s t q
 filter_upwards with i k N f r h
 let w:=takeUp P s i k
 have hX: W*w.wid a b ≤ δ/2:=by
   unfold Berth.wid; rw[show w.p.B=_ from r.sizeB];exact q
 
 have L:gem (w.fluxBare (w.home z) m) (δ/2+δ/2):=
    (add_halves δ).symm ▸ (show gem (w.fluxBare (w.home z) m) δ from t i k)
 exact pearlJet (Berth.clearance r) (boxSeal h.stone u.le) h.endStone h.lump x (deep_grace z) L hX

-- A 2-grade handed over at same origin. 
def corner:Cover:=-1
lemma tabW0 (P:VΩ) : 0<tabW P:=by unfold tabW; exact mul_pos (by norm_num) P.par.block.property

/-- Purchased in truly successive filters, not claiming rectangle. Credit
 glyphs and dual prices unscaled apart from marked/opening factor, not yet
 signed integrated claim. W cost in Handy uses Bare. -/
structure Cupful (w:Berth)(a c b W δ:ℝ)(m:ℕ)(z:Cover):Prop where
 crib:Rigs a c b m w
 born: ∃ f V,w.Before a b m (w.home z) f ∧
        Beau (w.smallFlow (w.home z) f) (w.fluxBare (w.home z) m) δ (W*w.wid a b) ∧
        gem (w.priceFlow (w.home z) f) (w.price*δ) ∧
        w.WearY m (w.home z) f a c b V
lemma cupful (P:VΩ)(g:Gate P)(r:RateStamp P.run)(p:Compass_sol P.run):
 ∃ a c b W δ:ℝ,0<a ∧ 0<c ∧ 0<b ∧ 0<W ∧ 0<δ ∧ NPL (till129 P a c b (tabW P)) ∧ NPL (reserve129 P a c b (tabW P)) ∧ Dry P (fun w=> Cupful w a c b W δ (tabW P) corner):=by
 obtain ⟨a,c,b,ha,hc,hb,f,g,t⟩:=calendar P g r p (tabW P)
 obtain ⟨W,δ,hj,hx,y⟩:= handsome P a c b _ (tabW0 P) corner ha

 refine ⟨a,c,b,W,δ,ha,hc,hb,hj,hx,f,g,?_⟩
 filter_upwards [t,y] with s v Q
 filter_upwards [v,Q] with i u J k j
 let w:=takeUp P s i k
 have T:=u k j
 obtain ⟨f,X⟩:= T.2 (w.home corner)
 obtain ⟨V,Y⟩:= Berth.weft T.1 X
 let b0:=J k j f T.1 X
 exact ⟨T,f,V,X,b0,Berth.flowRate T.1 b0,Y⟩
end YM.CF.Bay
#print axioms YM.CF.Bay.cupful
