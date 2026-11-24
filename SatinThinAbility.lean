import SatinThinAlarm
import SatinThinRod
import SatinThinVendor
import SatinThinFund
import SatinThinMinister
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Neon
open Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
open Tapestry Advance Papyrus Papyrus.Franc
variable {n:Side}
local notation "L"=>P.R.L
local notation "B"=> P.block
local notation "D"=> P.K.j
variable (s i k:ℕ)
local notation "VO"=> Y.voyage i
local notation "Ω" s:max => side Y i s
local notation "Gξ" s:max=> Vale.apt (Y.ir i) P.block P.R.L s
local notation "XP" s:max=> RootBook Y i k s
local notation:max "S" s:max=> (VO).CapeT s

open Graph -- for recX
open scoped ComplexOrder
-- permit perturbations
abbrev pertain (G:GramM n)(F Z:RegBudget n)(K:ForceBudget n):GramM n:= color_b G G.beta F Z K G.v

lemma existingMarket (b:s≤Y.uv k) : let G:=RootBook Y i k s; MarketR G P.h (3*dleaf P.R.L (hat P.R.L P.x s)*sites (side Y i s)):=by
 intro G; obtain ⟨w,g,h,he,G_⟩:= Papal.prices_plot Y s i k b; have hh:= zero_le_one.trans P.height; let Z:= dleaf P.R.L (hat P.R.L P.x s); let Ω':ℝ:= sites (Ω s);
 exact ⟨_,_,_,fixedFromE G_.reg hh,fixedFromE G_.slip hh,fixedFromF G_.force hh,(le_of_eq (show Z*Ω'+ _+ _= _ from by unfold Ω' sites Z; ring))⟩ -- tune

local notation "ΩL" => Single (side Y i s)
local notation "A'"=> side Y i s
variable {v E T R z c d:ℝ} (G₀:GramM n)
lemma market_roof (H:MarketR G₀ c d) (t:0≤c){U: RegBudget n}{F:ForceBudget n}(u:Pavilion G₀.p c v z U F): Graph.MarketR (pertain G₀ (G₀.F+U) G₀.slip (G₀.K+F)) c (d+2*(z+v*sites n)):=by
 obtain ⟨x,A,y,Z,rfl,rfl,hx,hy,hA,hZ⟩:=u.pay; obtain ⟨i,j,k,w,g,e,he⟩:=H; refine ⟨_,_,_,fixed_uniteE w (fixed_uniteE hx (fixedFromE hA t)),g,fixed_uniteF e (fixed_uniteF hy (fixedFromF hZ t)),?_⟩
 unfold sites; linarith only [he]

-- procurement of uniform h (augmented supplier)
structure Drawbill (P:Preparation)(C:ℝ):Prop where
 bought: ∃ v R:ℝ, ∃ N0:ℕ, 0<v ∧ 0<R ∧ C=2+(45*(1+R))^2+ (1+R)^2∧ CF.Papyrus.Franc.postage P.K.j R ∧ (v+1)*(45*(1+R)) ≤ P.h ∧ ∀ n:Side, N0 ≤ n.val→∀ (U: Pane n),Guard U P.d→∀ M:Tulip.Male,∀ i:Single n,Gall.dialZ (acts (spar P.K.j M U) (basisKet i)) ≤ v

open Papal (safety prices_plot roofage)
/- strength meter: total entry allowances. Booking `C` controls per unit / every extra occupation consumed by the entire enlargement. -/
noncomputable def metroStress (j:ℕ)(G:GramM n)(V:Scree.Loom n)(x:Orbit n)(g:Seat n→SU.E):ℝ:= ‖Pec.pigment G.J.I (V x)‖ + revE (actF j G V x)+ revE (twist (tradew n g) (spar j G.J.M (V x)) - spar j G.J.M (1:Pane n))
-- for normalization beamZ can lift counter. publish also letterRead counterpart
lemma seeMarket
    (w:Orbit (side Y i s)) (X:RegBudget (side Y i s))(J:RegBudget (side Y i s))(Y':ForceBudget (side Y i s))(A0:FC (Single (side Y i s)))
    (hη:MarketR (pertain (RootBook Y i k s) X J Y') P.h z)
    (g:Seat (side Y i s)→ SU.E) (u:0<R)
    (Q:IsStarProjection (spar P.K.j (RootBook Y i k s).J.M (1:Pane (side Y i s)))) (hz:0<v)(m:ℕ)(c:ℝ)
    (hp:(v+1)*(45*(1+R)) ≤ P.h)(e:∀ k':Single (side Y i s), Gall.dialZ (acts (spar P.K.j (RootBook Y i k s).J.M (((Y.voyage i).CapeT s) w)) (basisKet k')) ≤ v) (y_:CF.Papyrus.Franc.postage P.K.j R)(B_: ‖(metroS g Q m).glow A0‖ ≤ Real.exp c):
 let G:= XP s; let R':=S s; ‖letterRead A0 (recX P.U (pertain G X J Y') R' w)‖ ≤ Graph.past G w.1 * Real.exp (z+ stunt m (tickA (side Y i s)) (spar P.K.j G.J.M (1:Pane _))+ c+(2+(45*(1+R))^2+(1+R)^2)*metroStress D G R' w g):=by
 intro G R'
 let G' := pertain G X J Y'; let S₀:= spar P.K.j G.J.M (1:Pane (side Y i s)); let ϒ:= (R' w); let P₀:= spar D G.J.M ϒ; let Y₀:= tradew (side Y i s) g; let f:= changeM P.U ϒ G.J.M; let K':= tickA (side Y i s); let α:= metroS g Q m; let ρ:=45*(1+R); let D':= 2+ρ^2+(1+R)^2
 let T:= stunt m K' S₀; let U:= Pec.pigment G'.J.I ϒ; let Ce:= actF D G' R' w; let H:= revE Ce; have h1:=revE_ge Ce
 obtain ⟨qw,hq⟩:= Papal.safety Y s i k w
 have hug:Guard (Lattice.gauge g ϒ) P.d:=Cube.Guard.cov ((Papal.roofage Y i s).paid w) g
 have hr:0<ρ:=by unfold ρ; positivity
 have hy:IsStarProjection (twist Y₀ P₀):=by
    have hx:Brace.Sparkle (side Y i s) P.d G.J.M D:=P.U.broadness _ (P.J.gran.trans ((Y.voyage i).ownership s).size) _
    rw [← hx.covary _ g ((Papal.roofage Y i s).paid w)]; exact hx.projection _ hug -- tune
 let C:=metroStress D G R' w g; let J_:=revE (twist (tradew (side Y i s) g) P₀-S₀); have hj':0≤J_:=revE_ge _
 obtain ⟨ht,hB⟩:= metroBuy g Q y_ m
 have htk:‖α.glow (tank P₀ (G'.board w))‖ ≤ Real.exp z:= market_glow α G' P₀ w z hη (zero_le_one.trans P.height) (fun i=> (α.tag_glow ρ ht hB P₀ v hr.le hz.le e i).trans hp)
 have hv: ‖α.glow (exp (dg Ce))‖≤ Real.exp (ρ^2*H):=by rw [α.glowExp]; exact (bootC _).trans (Real.exp_monotone (α.dg_glow ρ ht hB _ hr.le))
 let B':=mile D G' R' w
 have hx:‖α.glow B'‖ ≤ Real.exp (z+ρ^2*H+‖U‖):=by
    unfold B' Graph.mile; rw [α.glow_free,norm_smul,α.glow_mult]; calc
       _ ≤ Real.exp ‖U‖*(Real.exp z*Real.exp (ρ^2*H)) := mul_le_mul ((Complex.norm_exp_le_exp_norm _).trans (by rw [norm_neg])) ((norm_mul_le ..).trans (mul_le_mul htk hv (norm_nonneg _) (Real.exp_pos _).le)) (norm_nonneg _) (Real.exp_pos _).le
       _ ≤ _ := by rw [Real.exp_add (_+_),Real.exp_add z]; exact le_of_eq (mul_comm ..)
 let W':=(((1+R)^2+1)*J_/2)
 have hC:‖acts (quant α.sell) f‖ ≤ Real.exp W':= metro_windE g Q y_ P₀ hy f hq m
 have hW:‖acts (quant (star α.buy)) (mateK (side Y i s))‖ ≤ Real.exp T:= (metro_mate g Q m).le
 rw [Graph.porch, (letterRead _).map_smul_of_tower, norm_smul, Real.norm_of_nonneg (Real.exp_pos _|>.le)]
 apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _|>.le)
 change ‖inner ℂ (mateK _) (acts A0 (acts B' f))‖≤ Real.exp _
 rw [←act_mul,Shaft.lawn α];
 apply (norm_inner_le_norm ..).trans; rw [Shaft.glow_mult,act_mul]
 calc _ ≤ Real.exp T*(Real.exp c*(Real.exp (z+ρ^2*H+‖U‖)* Real.exp W')):=mul_le_mul hW ((Graph.spentS _ _ _).trans (mul_le_mul B_ ((Graph.spentS _ _ _).trans (mul_le_mul hx hC (norm_nonneg _) (Real.exp_pos _).le)) (norm_nonneg _) (Real.exp_pos _).le)) (norm_nonneg _) (Real.exp_pos _).le
      _ ≤ _:= by rw [←Real.exp_add (z+ρ^2*H+‖U‖),←Real.exp_add c,←Real.exp_add T]; apply Real.exp_monotone; unfold W'; change _≤ z+T+c+(2+ρ^2+(1+R)^2)*(‖U‖+H+J_); have h1: 0 ≤ H:=h1; nlinarith only [mul_nonneg (sq_nonneg (1+R)) h1,mul_nonneg (sq_nonneg (1+R)) hj',mul_nonneg (sq_nonneg ρ) (norm_nonneg U),mul_nonneg (sq_nonneg ρ) hj',mul_nonneg (sq_nonneg (1+R)) (norm_nonneg U),h1,hj',norm_nonneg U] -- tune shadow i

structure RegionCapability (j:ℕ)(C:ℝ)(X:Supplier)(P:Preparation): Prop where
 lend: Drawbill P C
-- easier
lemma draw_grants {RΘ:Preparation→Prop}(T_: CommissionVector RΘ): CommissionVector (fun P=> RΘ P ∧ ∃ C, Drawbill P C):= by
 constructor; intro e' ε he Q
 obtain ⟨R,u,y⟩:= CF.Papyrus.Franc.grantH 4 (by omega)
 obtain ⟨v,δ,hv,hδ,N0,p⟩:= Graph.burley 4 (by omega)
 let T:=(v+1)*(45*(1+R))
 let X:Supplier:=fun K p Lm V Bm d W U M J ℓ Z=> max (Q K p Lm V Bm d W U M J ℓ Z) T
 obtain ⟨P,ℓ,Z,Y,p',u',t',r,c,A,w,X',L',G',B',J⟩:= T_.purchased (min e' δ) ε (lt_min he hδ) X
 refine ⟨P,ℓ,Z,Y,(show decorate Q P ℓ Z ≤ P.h from (le_max_left (decorate Q P ℓ Z) T).trans p'),u',t'.trans (min_le_left ..),r,c,A,⟨w, 2+(45*(1+R))^2+(1+R)^2, ?_⟩,X',L',G',B',J⟩
 refine ⟨v,R,N0,hv,u,rfl,?_,(show T≤ P.h from (le_max_right ..).trans p'),?_⟩
 · rw [P.kJ]; exact y
 rw [P.kJ]; exact fun n z U v M i=>p n z U (v.shrink (t'.trans (min_le_right ..))) M i

lemma beam_nil (f:Phys n): beamZ n f=letterRead 1 f:=by change _=inner ℂ (mateK _) (acts 1 f); rw [act_one]
structure MarketCost (C:ℝ)(Y:Course P (VolumeCape.Dream.Nimbus ℓ))(s i k:ℕ):Prop where
 buys : ∀ (z:ℝ)(X:RegBudget (side Y i s))(J:RegBudget (side Y i s))(Y':ForceBudget (side Y i s)), MarketR (pertain (RootBook Y i k s) X J Y') P.h z→ let G:=RootBook Y i k s; let R':=(Y.voyage i).CapeT s; ∀ (w:Orbit (side Y i s))(g:Seat (side Y i s)→SU.E), ‖beamZ _ (recX P.U (pertain G X J Y') R' w)‖ ≤ Graph.past G w.1 * Real.exp (z+ Cascade.angleFin G.J.M (side Y i s) P.K.j+C*metroStress P.K.j G R' w g)

lemma granted_wind (t:Drawbill P v)(Nw:ℕ) -- underscore secondary parameter for effort combination
 : ∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ, MarketCost v Y s i k:=by
 obtain ⟨x,R,N,hx,u,rfl,hα,hP,hK⟩:= t.bought
 apply Eventually.of_forall; intro s
 filter_upwards [(Papal.count_grows Y s).eventually_ge_atTop N] with i t k
 constructor; intro z X J F e G R' w g
 let b:= Cascade.angleFin G.J.M (side Y i s) P.K.j
 let ρ:=45*(1+R); let C:=2+ρ^2+(1+R)^2
 let hT:0< (↑(side Y i s).val:ℝ)^4:=pow_pos (by positivity) _
 let D':=C*metroStress P.K.j G R' w g
 let N':ℝ:=(↑(side Y i s).val:ℝ)^4
 let T:=fun x:ℝ=>Graph.past G w.1 * Real.exp (z+b+x*N'+D'); have hT':Continuous T:=by unfold T; fun_prop
 have hV:Filter.Tendsto T (nhdsWithin 0 (Set.Ioi (0:ℝ))) (𝓝 (Graph.past G w.1 * Real.exp (z+b+D'))):= by simpa only [ContinuousWithinAt,T,zero_mul,add_zero] using hT'.continuousWithinAt (x:=0) (s:=Set.Ioi (0:ℝ))
 letI:NeBot (nhdsWithin 0 (Set.Ioi (0:ℝ))) := inferInstance -- tune nebot
 let q':= side Y i s; let E':= RootBook Y i k s; let Q:=spar P.K.j E'.J.M (1:Pane q'); have hQ:IsStarProjection Q:= (P.U.broadness _ (P.J.gran.trans ((Y.voyage i).ownership s).size) E'.J.M).projection _ (guard0 P.dpos.le)
 change _ ≤ Graph.past G w.1*Real.exp (z+b+D')
 apply ge_of_tendsto hV
 filter_upwards [self_mem_nhdsWithin (s:=Set.Ioi (0:ℝ)) (a:=0)] with ε hε
 obtain ⟨m,hm⟩:= (CF.Papyrus.Franc.purge P.K.j (by rw [P.kJ]; decide) ε hε).exists
 have hp:= seeMarket Y s i k w X J F (1:FC (Single q')) e g u hQ hx m 0 hP (hK _ t (R' w) ((Papal.roofage Y i s).paid w) E'.J.M) hα (by rw [Shaft.glow_nil,norm_one]; exact le_of_eq (Real.exp_zero).symm)
 rw [beam_nil]; refine hp.trans (mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (Real.exp_pos _).le)
 let u:= stunt m (tickA q') Q; have ht:u≤ b+ ε*N':=hm q' E'.J.M hQ; change z+u+0+D' ≤ z+b+ε*N'+D'; linarith only [ht]
lemma seeBase (v:ℝ) (p:s≤Y.uv k)(D':MarketCost v Y s i k): let G:= XP s; let R':=S s; let l:= side Y i s; ∀ (w:Orbit (side Y i s))(g:Seat (side Y i s)→SU.E), ‖beamZ _ (recX P.U G R' w)‖≤ Graph.past G w.1 * Real.exp (3*dleaf P.R.L (hat P.R.L P.x s)*sites l+ Cascade.angleFin G.J.M l P.K.j+v*metroStress P.K.j G R' w g):=by
 intro G R' l w g
 exact D'.buys _ G.F G.slip G.K (existingMarket Y s i k p) w g

end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
#print axioms YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.seeMarket
#print axioms YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.granted_wind
#print axioms YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.draw_grants
#print axioms YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.seeBase
