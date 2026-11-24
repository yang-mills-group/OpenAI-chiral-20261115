import SatinThinJetsForward
/-!
# See full Six by shifts; then choose time **jets** instead
-/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option quotPrecheck false
noncomputable section
namespace YM.SatinJets
open Function Set Filter
open scoped NNReal InnerProductSpace Classical ComplexOrder
def seventh (i:Fin 6): {x:Seven// x ≠ 0}:= ⟨i.succ, i.succ_ne_zero⟩
lemma harmonic (H:Hilbert){α:Type}[Fintype α][DecidableEq α](k:α ≃ Fin 6)(v: Seven → H)(t:LinearIndependent ℂ v)(m:α→ℂ)(w:∀ i:α,m i≠0):
  Six.Clean (Matrix.gram ℂ (fun i:α=> m i • (v (seventh (k i)).val-v 0))):=by
 let U(i:α):= Units.mk0 (m i) (w i); let f:=seventh ∘ k
 have hp: Injective f:= (show Injective seventh from fun i j h=> Fin.succ_inj.mp (congrArg Subtype.val h)).comp k.injective
 have hv:= ((affineIndependent_iff_linearIndependent_vsub ℂ v 0).mp (t.affineIndependent ℂ)).comp f hp |>.units_smul U
 let M:= Matrix.gram ℂ (fun i:α=> m i • (v (seventh (k i)).val-v 0))
 have h: M.PosDef:=Matrix.posDef_gram_of_linearIndependent (show LinearIndependent ℂ (fun i:α => m i • (v (seventh (k i)).val-v 0)) from hv)
 exact ⟨h.det_pos.ne',fun _=> h.diag_pos.ne'⟩
end YM.SatinJets

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup.Balloon
open MacroGrid SatinNucleus Set
open YM.Six YM.SatinJets
-- complexOrder instance scope opened
variable (P:Spine)(x:P.Spectrum0 3)
local notation "κ"=> P.wealth 3 (P.advocate 3 x 3)
local notation "Γ"=> P.cartage 3 (P.advocate 3 x 3)
local notation "H"=> P.ManyF 3 (P.advocate 3 x 3)
local notation "S"=> P.seasons 3 (P.advocate 3 x 3)
local notation "E"=> (S).E
local notation "ℒ"=> Lead.Clan
local notation "V!"=> ∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j)
variable (f n:ℕ)(V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))
local notation "Z" k:max=> (purePrice k:ℂ)
-- `leading_y` THIN target after fusion with particular Family

def route_y (k:Lead.Clan) (t:ℝ):H:= (Z k) • (κ (V 3 [] t))
local notation "H!"=> P.route_y x V
-- Difference chord components; time-shifted auxiliaries, for rank estimation only
def family_six: (ℒ) ≃ Fin 6:= Fintype.equivFinOfCardEq (by decide)
def offset_d (i:Seven):ℝ≥0:= P.launchTick f n (stride i)
local notation "T"=> P.offset_d f n
local notation "Λ" i:max=> (seventh (family_six i)).val
def chordF (s:ℝ)(i:ℒ): H:= E (T (Λ i)) (H! i s)- E (T 0) (H! i s)
local notation "Q"=> P.chordF x f n V
-- BOTH stories: while exploring (not the ultimate mark shapes), and final shapes (after CP14)
-- Spacetime gap. Actor formally NOT declared at coincident points (don't use there)
def chartRoles (p:Vantage)(u:(ℒ)→ H) : CrossRead:= Matrix.of fun i j=> inner ℂ (u i) (Γ p (u j))

def reach_chords (p:Vantage) := P.chartRoles x p (Q (p 3/2))
local notation "R!"=> P.reach_chords x f n V
variable {Y:ℕ→ P.Apron} (R: GalaxyShow P x f n Y V)
-- Point rank forced by pf plan: use analytic K only for UNSATURATED jets
include R
lemma route_pos (i:ℒ): SatinJets.Positive (S) (H! i):= by intro a b h c; unfold route_y; rw [map_smul]; exact congrArg (Z i • ·) (P.height_pass x 3 V R.heat [] h c)
lemma chord_pos (i:ℒ): SatinJets.Positive (S) (fun t=> Q t i):= by
 intro a b h c; let d:=(b-a).toNNReal; dsimp only [chordF]; rw [map_sub,P.route_pos x f n V R i a b h c]
 have e(t): (E t).comp (E d)=(E d).comp (E t):=by rw [←(S).time,←(S).time,add_comm]
 exact congrArg₂ (fun x y:H=> x-y) (DFunLike.congr_fun (e _) _) (DFunLike.congr_fun (e _) _)

omit f n V R in
lemma chartRoles_cont : Continuous (fun t:(Vantage × ((ℒ)→ H))=> P.chartRoles x t.1 t.2):=
 continuous_pi fun i=> continuous_pi fun j=> ((continuous_apply i).comp continuous_snd).inner (P.caravan 3 (P.advocate 3 x 3) Prod.fst _ continuous_fst ((continuous_apply j).comp continuous_snd))
lemma chord_visible (p:Vantage)(h:0 < p 3): ContinuousAt R! p:= by
 apply (P.chartRoles_cont x).continuousAt.comp (f:=fun u=> (u,Q (u 3/2)))
 exact continuousAt_id.prodMk (continuousAt_pi.mpr (fun i=>(Positive.cont _ _ (P.chord_pos x f n V R i) (half_pos h)).comp (f:=fun p:Vantage=> p 3/2) ((continuous_apply 3).div_const 2).continuousAt))

-- calculate on one axis, then move
lemma stellar_chord: Clean (R! (update 0 3 (2:ℝ))):=by
 let a := (2:ℝ); let F(i:Seven):= (E (T i)) (κ (V 3 [] (a/2)))
 let p:=update (0:Vantage) 3 a; have h: R! p= Matrix.gram ℂ (fun i:ℒ=> (Z i) • (F (Λ i)-F 0)):=by
   ext1 i j; change inner ℂ (Q (p 3/2) i) (Γ p (Q (p 3/2) j))=inner ℂ (_:H) _
   unfold p; unfold chordF route_y; simp only [of_slideP x 3 (update (0:Vantage) 3 a) 0 (fun i s=> update_of_ne s ..),P.cart_zero, ContinuousLinearMap.id_apply, update_self,F,map_smul,smul_sub]
 rw [show update (0:Vantage) 3 (2:ℝ)=p from rfl,h]
 exact harmonic H family_six _ (R.independence (a/2) (by unfold a; norm_num)) (fun i:ℒ=> Z i) (fun i=> Complex.ofReal_ne_zero.mpr (purePrice_p i).ne')
-- beware shadow AnalyticAt ℝ matrix not norm? ∏ type
local notation "K"=> P.railKernel x 3 V V [3] []
private lemma shifted_one (a b:ℒ)(s t:ℝ≥0)(p:Vantage)(h:0<p 3):
    inner ℂ (E s (H! a (p 3/2))) (Γ p (E t (H! b (p 3/2)))) = (Z a)*( (Z b)* K (p+aislePt 3 (↑(s+t)))):=by
 let r:=p+aislePt 3 ↑(s+t)
 have hv:r 3=(p 3/2+(s:ℝ))+(p 3/2+(t:ℝ)):=by simp [r,aislePt]; ring
 have hp(c:ℝ≥0):0<p 3/2 +(c:ℝ):= add_pos_of_pos_of_nonneg (half_pos h) c.property
 rw [show p+aislePt 3 ↑(s+t)=r from rfl, P.rail_prices x R.heat hv (hp s) (hp t), of_slideP x 3 r p (fun i h=> (by simp [r,aislePt,h])), ← Positive.moves (S) _ (P.route_pos x f n V R a) (half_pos h) s, ← Positive.moves (S) _ (P.route_pos x f n V R b) (half_pos h) t]
 unfold route_y; rw [map_smul,inner_smul_left,inner_smul_right,Complex.conj_ofReal]

lemma chord_analytic (J:P.Ellis 3 x) (p:Vantage)(h:p∈brightShelf)(k:Axis)(i j:ℒ):
    AnalyticOnNhd ℝ (fun t:ℝ=> R! (update p k t) i j) (Set.Ioi 0):=by
 let u:ℝ→ Vantage:= update p k
 let F (s t:ℝ≥0):ℝ → ℂ:= fun b:ℝ=> inner ℂ (E s (H! i (u b 3/2))) (Γ (u b) (E t (H! j (u b 3/2))))
 have ht(s t:ℝ≥0)(b:ℝ)(w:0<b): AnalyticAt ℝ (F s t) b:=by
   have v: AnalyticAt ℝ (fun x'=> (Z i)*((Z j)* K (u x'+aislePt 3 (↑(s+t))))) b:= analyticAt_const.mul (analyticAt_const.mul (P.rail_analytic3 x R.heat J h _ _ (fun i' => by by_cases e:i'=3; subst i'; simp [aislePt]; positivity; simp [aislePt,e]) b w))
   apply v.congr; filter_upwards [lt_mem_nhds w] with p₀ hp; exact (shifted_one P x f n V R i j s t (u p₀) ((show u p₀ ∈ brightShelf from shelf_update (I:=fun _=> Set.Ioi (0:ℝ)) h hp) 3)).symm
 intro t g; let a:= Λ i; let b:= Λ j
 refine ((ht (T a) (T b) t g|>.sub (ht (T 0) (T b) t g)).sub ((ht (T a) (T 0) t g).sub (ht (T 0) (T 0) t g))).congr ?_
 filter_upwards with v
 -- unfold
 change _ = inner ℂ (Q ((u v) 3/2) i) (Γ (u v) (Q ((u v) 3/2) j))
 rw [chordF, chordF,map_sub,inner_sub_right,inner_sub_left,inner_sub_left]; rfl
-- Approach p (space zero) by shelf centers. no analytic extension through 0 time needed
lemma right_spread (J:P.Ellis 3 x): brightShelf ⊆ closure {p∈ brightShelf | Clean (R! p)}:=by
 refine shelf_clean_dense R! (fun _=> Set.Ioi (0:ℝ)) (fun _=> isOpen_Ioi) (fun _=> isPreconnected_Ioi) (P.chord_analytic x f n V R J) ?_
 let p:= update (0:Vantage) 3 (2:ℝ); have e:0<p 3:=by simp [p]
 let g(t:ℝ):= p+ (fun _:Axis=> t); have ht: Tendsto g (𝓝[>] 0) (𝓝 p):=by
    have hg:Continuous g:= continuous_pi (fun i=> by unfold g; simp only [Pi.add_apply]; fun_prop)
    exact (hg.tendsto' _ _ (by unfold g; ext; simp)).mono_left nhdsWithin_le_nhds
 obtain ⟨t,hw,hp⟩:= (((P.chord_visible x f n V R p e).tendsto.comp ht).eventually ((clean_open continuous_id).mem_nhds (P.stellar_chord x f n V R))).and (self_mem_nhdsWithin (a:=0 ) (s:=Set.Ioi (0:ℝ))) |>.exists
 refine ⟨g t,?_,hw⟩; intro i; change 0<p i+t; unfold p; simp only [Function.update_apply]; split; · exact add_pos (by norm_num) hp
 change 0<(0:ℝ)+t; simpa only [zero_add] using hp

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.right_spread
