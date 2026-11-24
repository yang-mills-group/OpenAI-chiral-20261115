import GaugeFieldConstruction.Joist
import YM.CF.Roots.Seat
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
open HushP ModuleB Pastry
-- entries in PH houses: both endpoints. not represented yet as Mark physical.
open Housing
variable (o:Skye.Seat n)
-- A1 frame: g star transport from root at x. B_F paid using transported O.
-- algebra of insertion indices (complex linear in G). prove on paid subspace.
open Flot
set_option maxRecDepth 2800
variable (M:Tulip.Male)
open scoped YM.CF.Mew
variable {T U V:InkD n}{F W:Waves}{a b:ℝ}(h)
-- Assembly on puncture label (separate from unit).
variable {h}
def αPureX(p:BudgetPoint)(f:Waves):yardLot:=fieldX M o (chartF f) -- may parity. κ aperture
abbrev αPure (p:BudgetPoint)(f:Waves)(h:ℝ): InkD n:= blurred o (αPureX o M p f) h
def αGuide (p:BudgetPoint)(f:Waves)(h:ℝ): ComG →L[ℝ]Pal:= (bm5 f).val-(landA M o (αPure o M p f h) p h)
abbrev αGauge (p:BudgetPoint)(f:Waves):InkD n:= flowF o (bF4 f).val (bF5 f) p
abbrev αMixed(p:BudgetPoint)(f:Waves)(h:ℝ):InkD n:= capT o (αGuide o M p f h) p h
def αPress(p:BudgetPoint)(f:Waves)(h:ℝ): InkD n:=αGauge o p f+(αPure o M p f h+αMixed o M p f h)
def Ψport := (Fintype.card lotV:ℝ)*(CargoMax*palCost)
abbrev Poid :ℝ:= |Ψport| * QuiltB
variable (s:0<h)(f:Waves)(p₁:p.power≤3)(e:p.order≤6)(t:20 < n.val)
include s p₁ e t
lemma suit_P : PressB p (Zhub o) (αPure o M p f h) h (Poid*‖f‖):=by
 have he:=bean_G f _ le_rfl; let g:=αPureX o M p f;
 have hx:fena g≤ QuiltB*‖f‖:=by
    have hv:0≤ QuiltB:=by unfold QuiltB; unfold doll₂ doll₁; have hz:=leg_p; have he:=rail_p; have hu:=mint_Z; positivity
    exact (Cushion (M:=M) o (chartF f) t).trans (mul_le_mul_of_nonneg_left he.1 hv)
 have hf:= press_P o g (field_u M o (chartF f) (chart_j f)) t p₁ e s.ne'; apply lift_PV hf; change Ψport * fena g ≤ Poid* _; exact (mul_le_mul (le_abs_self _) hx (norm_nonneg g) (abs_nonneg _)).trans_eq (mul_assoc ..|>.symm)
set_option maxHeartbeats 240000 in
lemma tagged_P : ViewsM (αGuide o M p f h):=by
 have hv: landA M o (αPure o M p f h) p h∈ G15:= portalG M (suit_P o M s f p₁ e t) -- tune
 let A:= (bm5 f).val; let T:=landA M o (αPure o M p f h) p h; have ht:ViewsM A:= (bm5 f).property; have he:ViewsM T:=hv; refine ⟨fun i=>?_,fun g a i=>?_⟩
 · change baseF false*(A i-T i)*_=A i-T i; rw [Matrix.mul_sub,sub_mul,ht.binned,he.binned] -- tune
 change (A _-T _) * KinX g=_*(A _-T _); rw [sub_mul,mul_sub,ht.main,he.main]
def zenMaze:= |mulZone| * QuiltB
set_option maxHeartbeats 240000 in
lemma clock_mismatch : tautF (αGuide o M p f h-(bm5 f).val) ≤ zenMaze*p.threshold*‖f‖:=by
 let A:=(bm5 f).val; let g:= αPureX o M p f; let Y:=landA M o (αPure o M p f h) p h
 have hb:=field_u M o (chartF f) (chart_j f); have hx: tautF Y ≤ mulZone*p.threshold*fena g:=earnB_1 o M g hb t e p₁ s.ne'; have he:0≤ QuiltB:=by unfold QuiltB; unfold doll₂ doll₁; have hz:=leg_p; have he:=rail_p; have hu:=mint_Z; positivity
 let K (A Y:ComG→L[ℝ] Pal): tautF (A-Y-A)= tautF Y:= by exact (show ∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](A Y:ComG→L[ℝ] E), tautF (A-Y-A)=tautF Y from by intro _ _ _ A Y; unfold tautF; rw [show A-Y-A= -Y from by abel,norm_neg]) A Y
 unfold αGuide; rw [K]; apply hx.trans; have ht:0≤ |mulZone| *p.threshold:= mul_nonneg (abs_nonneg _) p.threshold_pos.le; apply (mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self _) p.threshold_pos.le) ((Cushion (M:=M) _ _ t).trans (mul_le_mul_of_nonneg_left (bean_G f ‖f‖ le_rfl).1 he)) (show 0 ≤ fena g from (norm_nonneg g)) ht).trans_eq; unfold zenMaze; ring -- tune Normed ambiguity
abbrev κzone := (1:ℝ)+ |zenMaze|
abbrev ρzone:= |valorP| * κzone
set_option maxHeartbeats 240000 in
lemma entrust_M : tautF (αGuide o M p f h) ≤ κzone*‖f‖ :=by
 let K (A B:ComG→L[ℝ] Pal):tautF A ≤ tautF (A-B)+tautF B:=by exact (show ∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](A B:ComG→L[ℝ]E), tautF A ≤ tautF (A-B)+tautF B from fun {_} _ _ _ _=>norm_le_norm_sub_add ..) A B
 have hz:zenMaze*p.threshold ≤ |zenMaze|:= (mul_le_mul_of_nonneg_right (le_abs_self _) p.threshold_pos.le).trans (mul_le_of_le_one_right (abs_nonneg _) p.threshold_le)
 apply (K _ (bm5 f).val).trans; apply (add_le_add ((clock_mismatch o M s f p₁ e t).trans (mul_le_mul_of_nonneg_right hz (norm_nonneg _))) (bean_G f ‖f‖ le_rfl).2.2.2).trans_eq; unfold κzone; ring
lemma suit_M : PressB p (Zhub o) (αMixed o M p f h) h (ρzone*‖f‖):=by
 let V:=αGuide o M p f h; apply lift_PV (tipB o V (tagged_P o M s f p₁ e t) t p₁ e s.ne')
 exact (mul_le_mul (le_abs_self _) (entrust_M o M s f p₁ e t) (taut_nonneg _) (abs_nonneg _)).trans_eq (mul_assoc ..|>.symm)
abbrev suitCostH:= glyphs.choose*2
lemma suit_H : PressB p (Zhub o) (αGauge o p f) h (suitCostH*‖f‖):=by
 let L:= (bF4 f).val; let J:=bF5 f; let Z:= CoverP o L J p; let C:=glyphs.choose
 have hv:=bean_G f ‖f‖ le_rfl; let i:=glyphs.choose_spec.2 n o L J p p₁ e; let V:=ψTax p (bloomT L J) o;
 let a:= i.rends 1 (ping_f p _); apply lift_PV (Moto.litho p (Zhub o) Z i.live V i.swift.measurable _ a.grade i.rends); exact (mul_le_mul_of_nonneg_left (add_le_add hv.2.1 hv.2.2.1) (zero_le_one.trans glyphs.choose_spec.1)).trans_eq (by rw [← two_mul,← mul_assoc])
abbrev sector_C:ℝ:=suitCostH+(Poid+ρzone)
lemma brace_C : PressB p (Zhub o) (αPress o M p f h) h (sector_C* ‖f‖):=by
 let X:=Zhub o; rw [sector_C,add_mul,add_mul]; exact Larch.prop_add _ _ (suit_H o s f p₁ e t) (Larch.prop_add _ _ (suit_P o M s f p₁ e t) (suit_M o M s f p₁ e t)) -- tune
lemma brace_M : MetaB o M f (αPress o M p f h) p h:=by
 let V:=αPress o M p f h; let T:=αPure o M p f h; let K:=αGuide o M p f h; let Z:=αMixed o M p f h; let G:=αGauge o p f; let A:=(bF4 f).val; let J:=bF5 f; let Y:=αPureX o M p f
 obtain ⟨hx,hT⟩:= κFish o A J p p₁ e (beanFlip (A:= bF4 f)) (show 10 < (More n).val from (by change _<n.val*2; omega)); obtain ⟨eG,hg,gL⟩:= knit o A J p M h;
 have pV:lifeH V=lifeH G:=by change lifeH (G+(T+Z))= _; rw [life_add,life_add,show lifeH T=0 from light_blur .., show lifeH Z=0 from tide_scalar ..,add_zero,add_zero]
 have hΦ: ploy V=ploy G:=by unfold ploy; rw [show term V=term G from funext fun i=>congrFun pV _]
 constructor
 · -- fave
   change A= fave p o V; rw [← hx]; unfold fave luke; rw [hΦ]
 · change bF5 f=_; change J=claw p o V; rw [←hT]; unfold claw klem; rw [hΦ]
 · have hp: orbitPH (V 1)=notesK o Y h:=by
       change orbitPH (G _+(T _+Z _))=_; rw [plainPlus,plainPlus,show orbitPH (G 1)=0 from keel_Z ..,show orbitPH (Z 1)=0 from tide_g ..,show orbitPH (T 1)=_ from (show orbitPH (T 1)= notesK o Y h from snap_blur o Y),add_zero,zero_add]
   change _=winJ o M h (orbitPH (V 1)); rw [hp]; exact (spline M o (chartF f) t s.ne' (chart_j f)).symm
 have hh: landA M o Z p h=K:= tide_Z o M K (tagged_P o M s f p₁ e t) t p₁ e s.ne'
 let l:=suit_P o M s f p₁ e t; let x:=suit_M o M s f p₁ e t; unfold αPress; rw [landPlus M (suit_H o s f p₁ e t) (Larch.prop_add _ _ l x),landPlus M l x]; change (bm5 f).val= landA M o G p h+(landA M o T p h+landA M o Z p h); rw [hh,show landA M o G p h=0 from hg]; unfold K αGuide; -- use explicit
 exact (show ∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](A X:ComG→L[ℝ]E), A=0+(X+(A-X)) from fun {_} _ _ _ _=>by abel) _ (landA M o T p h)
omit s p₁ e t in
lemma skin_C (p:BudgetPoint)(f:Waves)(h:ℝ): lifeH (αPress o M p f h) 1=0:=by
 let V:= αGauge o p f
 have he:= knit o (bF4 f).val (bF5 f) p M h; unfold αPress; rw [life_add,life_add,show lifeH (αPure o M p f h)=0 from light_blur ..,show lifeH (αMixed o M p f h)=0 from tide_scalar ..,add_zero,add_zero]; exact he.2.2
end Layout
end Lenten
end YM.CF.TableF
end
