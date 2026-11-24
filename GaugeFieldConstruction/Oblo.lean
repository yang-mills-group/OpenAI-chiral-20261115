import GaugeFieldConstruction.Lotteries
import GaugeFieldConstruction.Fangs
/-! graded operator shape & comparison.-/
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
open Function NormedSpace Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open Tarn Cay Slate Cour Hest
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Fief Jet Vol Rel
open Yaw Pig
open Feu Feu.Corset Haro
section
open Py Riant Lattice Prism Tap FlightFlux TableF Boom Axon Flot Taxi
open Lenten.ModuleB
open Lich.Muster
open Hake Vow Bake Rue Larch
open TableF Lenten.Bank Lenten Lenten.Layout Fren
open Frugal
open scoped YM.CF.Mew
open BellPrice PinRack
open BellPrice PinRack
open Py.Rate.Pitching.Focus Py.Rate.Pitching
variable {N:Side}{P:BudgetPoint}{h t s a b v μ:ℝ}{E:Lattice.Support (More N)} {L:Side}{X:Scree.Hub N}{o:Seat N}{i j l k D:ℕ}
-- solve.H1 mechanical pre-cap
lemma ΓZero {V:Waves}(p:i≤j)(e:MSlot j V=0):MSlot i V=0:=by rw [←MStore V p,e,void_M]
abbrev Alto := (1:ℝ)/1000
abbrev RamoK (L:Side):ℝ:=(L.val:ℝ)^Alto
lemma ramo_v (K:Side):1 ≤ RamoK K:= Real.one_le_rpow (by exact_mod_cast K.property) (by norm_num [Alto]) -- tune
lemma rate_lt (p:i ≤ j): Rateκ L j ≤ Rateκ L i:=PinRack.existα L _ _ (by omega) -- tune method
structure TollsK (P:BudgetPoint)(o:Seat N)(f:Male)(V:RegBudget N)(L:Side)(q:ℝ)(h B:ℝ)(D:ℕ)(T:Waves): Prop where
   funds : ∃ C, ArenaC P V o C (5/4) h (B*q)
   control : Tangle L.val (KeyUp P) (Zhub o) f h D V
   cen : let X:=Zhub o; MSlot D (SealT X (V X) (KeyUp P) h f)=(q:ℂ) • T
lemma forte_f (p:i<j)(s:j≤2)(V: Waves)(v:MSlot j V=0):Nail V (i+1):= short_none (ΓZero p.le v) (p.le.trans s)
variable {M:Tulip.Male}{F:RegBudget N}{W:Waves}
abbrev ToneQ (F:RegBudget N)(P:BudgetPoint)(o:Seat N)(M:Male)(h:ℝ): Waves:=let X:=Zhub o; SealT X (F X) (KeyUp P) h M
private lemma Base_V {W:Waves}: Nail W 0:=⟨fun i=> False.elim (by omega),fun i=>False.elim (by omega),fun i=>False.elim (by omega),fun i=>False.elim (by omega),fun i=>False.elim (by omega),fun i=>False.elim (by omega)⟩
lemma driver (p₀:TollsK P o M F L t h b k W)(v: i ≤ k)(w:k ≤2)(hx:0≤h)(hc:Cresc L.val P (Zhub o))(p:∀ j:ℕ, ΓProj j W= if i ≤ j then W else 0): PromptQ M P o F L h i (ToneQ F P o M h):=by
 obtain ⟨Z,pZ⟩:= p₀.funds; let X:= Zhub o; have hQ(x:Scree.Hub N):= meterL (pZ.fits x) hx M
 have hj := hQ X
 have hv:CarBot _ o (KeyUp P) M (F X) h i:=by
    rw [Knock (P:=(show MetaB o M _ _ _ _ from hj)) (by omega)] -- tune o reducibility
    refine ⟨(p₀.control X hc).1,?_⟩; cases i with
    | zero=> exact Base_V
    | succ i =>
       let W':= SealT X (F X) (KeyUp P) h M; apply short_none _ (by omega); change ΓProj i W'= 0
       have He : ΓProj k W'=(t:ℂ) • W:=p₀.cen; rw [←show ΓProj i (ΓProj k W')=ΓProj i W' from MStore W' (by omega), He, (ΓProj i).map_smul,p,if_neg (by omega)]; exact Troot_z Packs_U _
 refine ⟨hQ X,?_,hv,?_⟩
 · intro j u t; by_cases z:j=X; · rw [z]; exact hv
   rw [←u]; refine (Knock (hQ j) (by omega)).mpr ⟨(p₀.control j t).1,?_⟩; cases i with
   | zero=> exact Base_V
   | succ i => exact forte_f v w _ ((p₀.control j t).2 z)
 intro j u t z; rw [←u]; refine (Knock (hQ j) (by omega)).mpr ⟨(p₀.control j t).1,short_none (ΓZero v ((p₀.control j t).2 z)) (v.trans w)⟩
lemma over_C (p:TollsK P o M F L t h b k 0)(u:k≤2)(w:0≤h):HeelB M P o F L h (k+1):=by
 intro j x v; obtain ⟨Z,pZ⟩:=p.funds; rw [←x]; apply (Knock (meterL (pZ.fits j) w _) (by omega)).mpr
 refine ⟨(p.control j v).1,short_none ?_ u⟩; by_cases t':j=Zhub o; · rw [t']; exact p.cen.trans (Troot_z Packs_U _) -- p.cen let access? tune
 exact (p.control j v).2 t'
abbrev Winner (s τ:ℝ):= 2*τ*s+2*s+1
abbrev Gapμ (L:Side)(s:ℝ):=2*RamoK L*s+1
abbrev Slipρ (L:Side)(s:ℝ):=Gapμ L s*αN L
lemma PosW {s τ:ℝ}(v:0 ≤ s)(t:0 ≤ τ):0≤ Winner s τ:=by unfold Winner; linarith [mul_nonneg v t]
lemma PosR {s:ℝ}(v:0 ≤ s): 0≤ Gapμ L s:=by unfold Gapμ; have hp:= ramo_v L; nlinarith only [v,hp,mul_nonneg v (show 0 ≤ RamoK L from zero_le_one.trans hp)]
lemma RightF {x:ℝ}{c:ℕ} (w:ℝ)(p:s ≤ 2*t)(hx:0≤μ)(k:c≤2) (y:b ≤ Rateκ L 3*t) (hs:x ≤ s*w)(pW:0 ≤ w)(tV:0 ≤ t)(h:αN L*RamoK L ≤1) : μ*(αInk L c x + αInk L (c+1) (RamoK L*s))+b ≤ Winner μ w *(Rateκ L c*t):=by -- x c undecl
 let U:=RamoK L; have hU: 0≤ U:=zero_le_one.trans (ramo_v _)
 have hv: Rateκ L (c+1)=Rateκ L c* αN L:= pow_succ ..
 apply le_trans (add_le_add (b:=μ*((Rateκ L c)*( (2*t)*w)+ (Rateκ L (c+1)*(U*(2*t)))) ) (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left (hs.trans (mul_le_mul_of_nonneg_right p pW)) (Rate_pr ..).le) (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left p hU) (Rate_pr ..).le)) hx) (y.trans (mul_le_mul_of_nonneg_right (rate_lt (le_trans k (by omega))) tV))) -- b binder maybe
 rw [hv]; have ht:αN L*U ≤ 1:=h; have hb:= mul_nonneg (mul_nonneg hx tV) (Rate_pr L c).le; unfold Winner; nlinarith only [mul_le_mul_of_nonneg_right ht hb] -- unfold Winner
lemma LeftF (p:s ≤2*t)(hx:0≤μ)(k:D ≤2) (y:b ≤ Rateκ L 3*t)(tV:0≤t): μ*αInk L (D+1) (RamoK L*s)+b ≤ Gapμ L μ* (Rateκ L (D+1)*t):=by
 let U:= RamoK L; have hU: 0 ≤ U:=zero_le_one.trans (ramo_v _); let Z:= Rateκ L (D+1);
 calc
    _≤ μ*(Z*(U*(2*t)))+Z*t:= add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left p hU) (Rate_pr ..).le) hx) (y.trans (mul_le_mul_of_nonneg_right (rate_lt (by omega :D+1 ≤ 3)) tV))
    _=_:=by change _= (2*U*μ+1)*(Z*t); ring
end
end YM.CF.Oath
end
