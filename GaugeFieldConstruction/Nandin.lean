import GaugeFieldConstruction.Jessel
import YM.CF.Roots.Seat
import SatinThinPiers
import YM.CF.Mica.Sleet
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 30000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
local notation "GS"=> SU.group
variable {n:Side}{p: BudgetPoint}{Q: InkD n}{o:Skye.Seat n}{X:Scree.Hub n}{h c:ℝ}
namespace Lenten
open Bank Laurent Bloch Tap Hove Spire
open Haro Hove Moto Tap
namespace Layout
open scoped YM.CF.Mew
open HushP ModuleB Pastry Flot
namespace Fren
open Skye Levier Scroll Spire Ione
open Lattice
open ProjectorNext.Equivariance (bonds pull_increment roll pulledDirection)
-- Point root always moves by pull. x at old.
variable (s:Sweep n)(R:Signed)
open Rush
-- anchor costs on this chart.
open QuadClock Vault
variable {A B U:InkD n}{v f r:ℝ}
abbrev sheen(R:Signed)(b:Bool)(X:Waves):Waves:= (thought_feast R b X).choose
lemma sheen_v(R:Signed)(b:Bool)(X: Waves) : Thoughts R b X (sheen R b X):=(thought_feast ..).choose_spec -- tune
abbrev Mason (u:Waves) := sheen s.s s.charge u
lemma fℓies (M:Male)(T:InkD n)(v:PressB p X Q h c)(t:PressB p (moveHub s X) T h f)(u:Turns s Q T)(hp:0≤h)(V:Waves)(e:MetaB X.val.1 M V Q p h)(w:100 < n.val)(b:Nonwrapping X.val.2 X.val.1): MetaB (moveHub s X).val.1 M (Mason s V) T p h:=by -- tune ident ligature
 let W:=exportM (moveHub s X).val.1 M t hp rfl; have hw:=export_full _ M t hp rfl; rw [show Mason s V=W from ThoughtU s.s s.charge V _ _ (sheen_v ..) (lives s M v t u hp V W e hw w b)]; exact hw
variable (M: Male)(o:Skye.Seat n)
lemma dose_E (F:Waves)(v:300<n.val)(h₁:0<h)(w:p.power≤3)(e:p.order≤6) : MetaB (sh s o) M (Mason s F) (WakeQ s (αPress o M p F h)) p h:=by
 have hv:20<n.val:=lt_trans (by norm_num) v; exact fℓies s M _ (brace_C _ _ h₁ F w e hv) ((move_Φ s o).symm ▸ rent_μ o s F M hv w e h₁) (Wake_acts ..) h₁.le F (brace_M o M h₁ F w e hv) (lt_trans (by norm_num) v) (Window_z o v) -- tune rent binder order
-- To iterate two even on synthetic n, need 'leg scopes' on any WakeQ αPress. Preserve degree<=2 by paint laws. Costs on moved-moving Mark via splitting sage_L & rest, with two grants. Easier invoke Ξ flips at original budgets (views K), for any s,t; no purchases. Need synthetic s*t chosen there; use Turns.s trans.
private lemma monoT {f:InkD n}(v:monoTwo f)(s:Sweep n): monoTwo (WakeQ s f):=by
 let D:=WakeQ s f; have he(y:Pane n): D y=wage_Q 2 (D y):=by
    have hm: f=restK f:= (restore f v).symm; conv_lhs=> unfold D WakeQ step_F; rw [hm]; -- hm dependent rhs, tune
    unfold D WakeQ step_F; simp only [restK,Function.comp_apply]; exact (pose_U ..).symm
 intro i j p; change crumb (D i).val j= _; rw [he i,price_X,if_neg p]
private lemma sageT {f:InkD n}(v:sage_L f=f)(s:Sweep n): sage_L (WakeQ s f)=WakeQ s f:=by
 funext i; nth_rw 2 [←v]; unfold WakeQ sage_L step_F; simp only [Function.comp_apply]; exact pose_U ..
set_option maxHeartbeats 90000 in
lemma plum_p (t:Sweep n)(p₁:p.power ≤3)(q:p.order≤6)(h₁:0<h)(V:Waves)(v:20<n.val): ∃ a: ℝ, PressB p (Zhub (sh t (sh s o))) (WakeQ t (WakeQ s (αPress o M p V h))) h a:=by
 let S:= Zhub o; let G:= αGauge o p V; let T:=αPure o M p V h; let P:=αMixed o M p V h
 have hp:monoTwo T:=m2sum _ _ (fun i _=> ph_rankH 0 i _ _ o); have hz: monoTwo P:=m2sum _ _ (fun i _=> ph_rankH 0 neutralK (mallet o (αGuide o M p V h) p i) h o)
 rw [←move_Φ,←move_Φ]; unfold αPress; rw [Wake_add, Wake_add,Wake_add,Wake_add]
 let Q:=h₁.le; let Vq:= sageT (f:=G) (gauge_rankH ..) s; let L:=spin_h t Vq Q (spin_h s (gauge_rankH ..) Q (suit_H o h₁ V p₁ q v)); let E:= spin_p t (monoT hp s) Q (spin_p s hp Q (suit_P o M h₁ V p₁ q v)); let F:= spin_p t (monoT hz s) Q (spin_p s hz Q (suit_M o M h₁ V p₁ q v))
 exact ⟨_, Larch.prop_add _ _ L (Larch.prop_add _ _ E F)⟩ -- tune
-- synthetic n L=401. explicit. high . raw.
omit o M
private abbrev Kery := (301:Side) -- tune postfix
private abbrev StudX:Skye.Seat Kery:=0
private abbrev MintX : Male :=⟨1,odd_one⟩
private lemma N_jet : 300< (301:Side).val:=by norm_num
private lemma haze : mindChart.power ≤3 := le_rfl
private lemma haze_e : mindChart.order ≤6 := le_rfl
private lemma N_ξ :20< (301:Side).val:=lt_trans (by norm_num) N_jet
lemma sheen_a (R T: Signed)(p q:Bool)(W:Waves): sheen T q (sheen R p W)= sheen (R*T) (p.xor q) W:=by
 let s:Sweep (301:Side):=⟨R,0,p⟩; let t:Sweep (301:Side):=⟨T,0,q⟩; let o:= StudX; let P:= mindChart; let V:=αPress o MintX P W 1; let F:=WakeQ s V; let A:=WakeQ t F; let Z:= sh s o; let Y:= sh t Z
 have hp:=dose_E s MintX o W N_jet (h:=1) zero_lt_one haze haze_e;
 obtain ⟨c,h⟩:= plum_p s MintX o t (p:=P) haze haze_e zero_lt_one W N_ξ
 have hz: PressB P (Zhub Z) F 1 _ := rent_μ o s W MintX N_ξ haze haze_e zero_lt_one
 have ha: WakeQ (s*t) V=A:=(T_uni (s*t) (T_comp s t (Wake_acts s V) (Wake_acts t F))).symm -- argument tune
 have he: sh (s*t) o= Y:=by
    exact congrArg (fun x:Scree.Hub (301:Side)=> x.val.1) (push_sum (X:=Zhub o) s t)
 have hf : MetaB Y MintX (Mason t (Mason s W)) A P 1:= fℓies t MintX _ hz ((move_Φ t Z).symm ▸ h) (Wake_acts ..) zero_le_one (Mason s W) hp (lt_trans (by norm_num) N_jet) (Window_z _ N_jet)
 have hs :MetaB (sh (s*t) o) MintX _ (WakeQ (s*t) V) P 1:=dose_E (s*t) MintX o W N_jet zero_lt_one haze haze_e; rw [ha,he] at hs; exact metaUnique Y MintX A P 1 _ _ hf hs -- tune binder order
lemma lands_t (t:Sweep n)(V: Waves): Mason t (Mason s V)=Mason (s*t) V:= sheen_a .. -- mk s.s mul orientation
lemma sheen_o(F:Waves): sheen 1 false F=F:=by
 let Z:= αPress StudX MintX mindChart F 1; let T:Sweep Kery:=1; have ht: WakeQ T Z=Z:=by funext i; unfold WakeQ step_F T; rw [inv_one]; simp only [Function.comp_apply,inv_one,toon_Q,flare_i]
 have he:sh T StudX=StudX:=by apply (boxA T).injective; rw [show boxA T (sh T _)=_ from (boxA T).apply_symm_apply StudX]; exact (shy_z _).symm
 have hp: MetaB (sh T StudX) MintX (Mason T F) (WakeQ T Z) mindChart 1:=dose_E T MintX StudX F N_jet zero_lt_one haze haze_e; rw [ht,he] at hp; exact metaUnique _ _ _ _ _ _ _ hp (brace_M StudX MintX zero_lt_one F haze haze_e N_ξ) -- tune
lemma lands_o(F:Waves): Mason (1:Sweep n) F=F:= sheen_o ..
lemma lands_k(F:Waves): Mason s⁻¹ (Mason s F) = F:=by rw [lands_t,mul_inv_cancel,lands_o]
private abbrev PinX(F:Waves):InkD Kery:= αPress StudX MintX mindChart F 1
private abbrev arm (R:Signed)(v:Bool):Sweep Kery:=⟨R,0,v⟩
private lemma badgeU (T:Sweep Kery)(F:Waves): PressB mindChart (Zhub (sh T StudX)) (WakeQ T (PinX F)) 1 (Turnp mindChart* ‖F‖):= rent_μ StudX T F MintX N_ξ haze haze_e zero_lt_one
private lemma chartU(T:Sweep Kery)(F:Waves): MetaB (sh T StudX) MintX (Mason T F) (WakeQ T (PinX F)) mindChart 1:=dose_E T MintX StudX F N_jet zero_lt_one haze haze_e
lemma sheen_plus (R:Signed)(q:Bool)(f g:Waves): sheen R q (f+g)= sheen R q f+ sheen R q g:=by
 let T:=arm R q; let o:=sh T StudX; have hp: PinX (f+g)=PinX f+PinX g:= map_add (hatchP _ MintX (h:=1) zero_lt_one haze haze_e N_ξ) f g; have hx:=chartU T (f+g); rw [hp, Wake_add] at hx; apply metaUnique o MintX _ _ _ _ _ hx; exact linearHU _ _ (chartU T f) (chartU T g) zero_le_one (badgeU T f) (badgeU T g)
lemma sheen_p (R:Signed)(q:Bool)(f:Waves)(x:ℂ): sheen R q (x • f)= cSignX (q.xor (detX R)) x • sheen R q f:=by
 let T:=arm R q; let o:=sh T StudX; have hp:PinX (x • f)=x • PinX f:= map_smul (hatchP _ MintX (h:=1) zero_lt_one haze haze_e N_ξ) x f; have ht:=chartU T (x • f); rw [hp,Wake_smul] at ht; apply metaUnique o MintX _ _ _ _ _ ht; exact linearHE _ _ (chartU T f) (badgeU T f) _ zero_le_one
abbrev tilos:ℝ:=|SectorVal*Turnp mindChart|
set_option maxHeartbeats 220000 in
lemma sheen_norm (R:Signed)(q:Bool)(f:Waves): ‖sheen R q f‖ ≤ tilos* ‖f‖ :=by
 let s:=arm R q; have he:= well_Z (sh s StudX) MintX (badgeU s f) zero_le_one rfl _ (chartU s f); refine he.trans ?_; rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
-- full Reach once even. note turn_{p} depends at only signed frame, cost pick uniform over two powers. 
-- define turned section at root & average. Intertwine. Use Fintype linear map explicit.
end Fren
end Layout
end Lenten
end YM.CF.TableF
end
