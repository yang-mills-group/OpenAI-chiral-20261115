import GaugeFieldConstruction.Yields
set_option autoImplicit false
set_option maxHeartbeats 80000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden.MastTin.ArtCart
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
open Buffered Lifted Girt Skye Window Vale
open TableF TableF.Lenten Layout Flot Moto Tap Bank ModuleB Haro Hove Fren Work.F03 Taxi Ember Fir HushP
variable {G H:Paper n}{p:BudgetPoint}{c v h:ℝ}(M: Male){o:Seat n}
open Spectrix Simmer Next.Rank.Spindle
open Gleam Gleam.Guide Fock.Flux
open Py.Rate.LocalLimit.Papal Py.Rate.LocalLimit.Papal.FrameP
open AnalyticBridge VerifiedReset
open Gleam.Guide.Pitcher Coins Fock.Flux Fock.Flux.Pacts
open YM.GaugeFieldConstruction.Wick.Yacht YM.GaugeFieldConstruction.Wick.Yacht.Vesper Violets
-- Precision of anch spectra.T unpow field -> price.Weight.
variable (x:Cover) (w:300<n.val)
include w
private lemma symmet (P:TrackD p (Pach (Θk n x)) h G c)(u:portable G)(p0:p.power≤3)(p1:p.order≤6)(t:0<h)(i j:tangD n): let o:=Θk n x; ploy (AlphaY G) (caster o (cast_P o i)) (caster o (cast_P o j))=ploy (AlphaY G) i j:=by
 intro o; let Q:=ploy (AlphaY G); let v(k):= caster o (cast_P o k); let r:=sprig o P p0 p1 u
 have hx(v' w'): Q v' w'= Q w' v':=ploy_herm r t.le _ _
 have he(i j:tangD n): Q i j=Q (v i) j:=by
    obtain ⟨g,hk⟩:= torn_K i o w; have hp:=ploy_nil r t.le _ _ j hk; rw [map_sub,_root_.sub_apply,sub_eq_zero] at hp; exact hp
 calc Q (v i) (v j)=Q i (v j):= (he i _).symm
      _= Q (v j) i:=hx ..
      _= _:= (he j i).symm.trans (hx j i)
-- vectors evaluations paired. include weight scaling. prove via summing repeated.Budget
private lemma expandI {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{I: Type}[DecidableEq I][Fintype I](K:E→L[ℝ] E→L[ℝ]ℂ)(f:I→E)(p q:I→ℝ): ∑ i:Fin 2→I,(p (i 0)*q (i 1)) • K (f (i 0)) (f (i 1))= K (∑ i,p i • f i) (∑ i,q i • f i):=by
 let P:= Fin.consEquiv (fun _:Fin 2=>I); let Q:= Fin.consEquiv (fun _:Fin 1=>I)
 rw [←Equiv.sum_comp P (fun i=> (p (i 0)* q (i 1)) • _),Fintype.sum_prod_type, map_sum K,ContinuousLinearMap.sum_apply]; apply sum_congr rfl; intro i _; rw [map_smul, ContinuousLinearMap.smul_apply,map_sum,Finset.smul_sum]
 rw [← Equiv.sum_comp Q (fun i:Fin 1→I => _),Fintype.sum_prod_type]; apply sum_congr rfl; intro j _; rw [Fintype.sum_unique,map_smul]; apply mul_smul -- tune
variable {M}
omit w
lemma staple (G:Paper n)(u v:tangD n): entry_H G none 2 ![u,v]= ploy (AlphaY G) u v:=by rw [ploy_iter]; rw [entry_H,show TableF.term (AlphaY G)=PressAt (G none) from funext fun i=>(bpu_T ..).2] -- tune
private lemma potB (P:TrackD p (Pach (Θk n x)) h G c)(z:ℝ)(i: Shx n x):let o:=Θk n x; let u(p:Frills o):= caster o (Pi.single p 1); guc n x (z • G) i= (z/2) • ploy (AlphaY G) (u (i 0)) (u (i 1)):=by -- tune shadow
 intro o y; change ((Nat.factorial 2:ℝ)⁻¹) • entry_H (z • G) none 2 _= _
 let H:= PressAt (G none); have he:entry_H (z • G) none 2=z • entry_H G none 2:=by
    unfold entry_H; rw [show PressAt ((z • G) none)=z • H from rfl]; exact iteratedFDeriv_const_smul_apply (i:=2) ((readiness _ P none).of_le (by norm_num))
 rw [he,ContinuousMultilinearMap.smul_apply]; let A:=caster o; have hv:(fun l:Fin 2=>A (Pi.single (i l) 1))=![y (i 0),y (i 1)]:=by ext1 j; fin_cases j <;> rfl
 change (_:ℝ) • z • entry_H G _ 2 (fun l:Fin 2=>A (Pi.single (i l) 1))=_; rw [hv,staple,smul_smul]; congr 1; norm_num; ring
include w
private lemma leadQ (P:TrackD p (Pach (Θk n x)) h G c)(v:portable G)(b:p.power ≤3)(t:p.order≤6)(l:0<h)(i j:tangD n)(z y:StampSet n x→ℝ)(hI: cast_P (Θk n x) i=p.threshold • z)(g: cast_P (Θk n x) j=p.threshold • y):
 ∑ k:Shx n x,(z (k 0)*y (k 1)) • guc n x (Genre.gauge.coinB p h • G) k=(1/2:ℝ) • ploy (AlphaY G) i j:=by
 let o:= Θk n x; let V:=caster o; let K(a:StampSet n x):=V (Pi.single a 1); let C:=ploy (AlphaY G); let T:=p.threshold; let A(i:Shx n x):= C (K (i 0)) (K (i 1)); have hp(u: Confab o): V u=∑ j: Frills o, u j • K j:=by
    rw [show V u=V (∑ j: Frills o,u j • Pi.single j 1) from ?_,map_sum]; simp only [map_smul]; rfl
    congr 1; ext1 j; simp [Finset.sum_apply,Pi.single_apply]
 have he(k:Shx n x):guc n x (Genre.gauge.coinB p h • G) k=(T^2/2) • A k:=by
    have ht:Genre.gauge.coinB p h=T^2:=by simp [Genre.coinB,Genre.orderB]; rfl -- maybe no goals
    rw [ht]; apply potB x P
 simp_rw [he]; rw [←symmet x w P v b t l,show cast_P o i=T • z from hI,show cast_P o j=T • y from g]
 change ∑ k:Fin 2→ Frills o, _ = (1/2:ℝ) • C (V _) (V _); rw [hp,hp, ← expandI (n:=n) w]; rw [Finset.smul_sum]; apply sum_congr rfl; intro k _; simp only [smul_smul,Pi.smul_apply,smul_eq_mul]; congr 1; unfold T; ring -- tune
omit w
open YM.GaugeFieldConstruction Phys
local notation "oX" => Θk n x
abbrev pitchX (i:Pen): Confab (Θk n x):=fun u=> ballG (Wasp n x u) i
abbrev pitchY (i:Pen): Confab (Θk n x):= fun u=> boilG (Wasp n x u) x i
def waxG (r:ℕ)(i:StampSet n x):= (YM.GaugeFieldConstruction.Wick.Yacht.tariff (1:ℝ) r:ℂ) • boon Phys.lace (YM.GaugeFieldConstruction.Wick.Yacht.pinG (Wasp n x i)) (Glint x (Wasp n x i)) r -- ambiguous
lemma wax_c (i:StampSet n x)(j:Pen): test j (waxG x 0 i)=(pitchX x j i:ℂ):= by rw [waxG,B0,map_smul]; rw [show (YM.GaugeFieldConstruction.Wick.Yacht.tariff (1:ℝ) 0:ℂ)=1 from (by simp [YM.GaugeFieldConstruction.Wick.Yacht.tariff]),one_smul]; exact seekP ..
lemma wax_h (i:StampSet n x)(j:Pen): test j (waxG x 1 i)=(pitchY x j i:ℂ):=by rw [waxG,map_smul]; rw [show (YM.GaugeFieldConstruction.Wick.Yacht.tariff (1:ℝ) 1:ℂ)=1 from (by simp [YM.GaugeFieldConstruction.Wick.Yacht.tariff]),one_smul]; exact topView ..
-- partial coeff of total Book (quasi series will prove uniqueness separately)
abbrev alignG (G:Paper n)(r s:ℕ): Cauchy.J GaugePair:=∑ i:Shx n x,guc n x G i • Cauchy.times' (waxG x r (i 0)) (waxG x s (i 1))
private lemma totals{i j: Pen}(G:Paper n)(a b: Confab (Θk n x))(r s:ℕ)(ha:∀ k, test i (waxG x r k)=(a k:ℂ))(hb:∀ k,test j (waxG x s k)=(b k:ℂ)): test (i,j) (alignG x G r s)=∑ k:Shx n x,(a (k 0)* b (k 1)) • guc n x G k:=by -- remove implicit A B
 unfold alignG; rw [map_sum]; apply sum_congr rfl; intro k _; rw [map_smul,tested, ha,hb]; simp only [smul_eq_mul,Complex.real_smul]; push_cast; ring
lemma sumOverview (x y:Phys.Pig): (inner ℝ (Phys.dye x) (Phys.dye y):ℂ)=if x=y then 1 else 0:=by
 by_cases e:x=y <;> simp [Phys.dye, e]
 simpa [dye] using Phys.dye.orthonormal.2 e
include w
lemma GaugeLeader (P:TrackD p (Pach (Θk n x)) h G c)(v:portable G)(b:p.power ≤3)(t:p.order≤6)(l:0<h)(i j:Pen)(W:Waves)(U:MetaB (Θk n x) M W (AlphaY G) p h): let Y:=Genre.gauge.coinB p h • G; let A:= if i.2=j.2 then (1/2:ℂ) else 0; test (i,j) (alignG x Y 0 0)=A * (bF4 W).val (E_G i.1) (E_G j.1) ∧ test (i,j) (alignG x Y 0 1)= A*bF5 W (E_G i.1) (E_D j.1) ∧ test (i,j) (alignG x Y 1 0)= A*bF5 W (E_G j.1) (E_D i.1):=by
 intro Y A; let Q:=sprig oX P b t v; let Z:=AlphaY G; let C':=ploy Z
 have hx (k e:Pen):ploy Z (gateC oX p.threshold (hem (E_G k.1) (dye k.2))) (gateC oX p.threshold (hem (E_G e.1) (dye e.2)))= (bF4 W).val (E_G k.1) (E_G e.1)*if k.2=e.2 then (1:ℂ) else 0:=by rw [←sumOverview,U.post]; exact formC_Ps (o:=Θk n x) Q l.le _ _ _ _
 have hy(k e:Pen):ploy Z (gateC oX p.threshold (hem (E_G k.1) (dye k.2))) (gateT oX p.threshold (loomH (E_D e.1) (dye e.2)))= bF5 W (E_G k.1) (E_D e.1)* if k.2=e.2 then (1:ℂ) else 0:=by rw [←sumOverview,U.mast]; exact formT_Ps (o:=Θk n x) Q l.le _ _ _ _
 let Gκ(k:Pen):=gateC oX p.threshold (hem (E_G k.1) (dye k.2)); let Dκ(k:Pen):=gateT oX p.threshold (loomH (E_D k.1) (dye k.2))
 have hT(k: Pen):cast_P oX (Gκ k)=p.threshold • pitchX x k:=funext fun i=> ΨK n x i k w _
 have hF(k: Pen):cast_P oX (Dκ k)=p.threshold • pitchY x k:=funext fun i=> ΨJ n x i k w _
 rw [totals x Y (pitchX x i) (pitchX x j) 0 0 (fun k=>wax_c x k i) (fun k=>wax_c x k j),totals x Y (pitchX x i) (pitchY x j) 0 1 (fun k=>wax_c x k i) (fun k=>wax_h x k j),totals x Y (pitchY x i) (pitchX x j) 1 0 (fun k=>wax_h x k i) (fun k=>wax_c x k j)]
 unfold Y; rw [leadQ x w P v b t l _ _ _ _ (hT i) (hT j),leadQ x w P v b t l _ _ _ _ (hT i) (hF j), leadQ x w P v b t l _ _ _ _ (hF i) (hT j)]
 rw [show C' _ _= _ from hx i j] -- tune
 rw [show ploy Z (Dκ i) (Gκ j)= _ from ploy_herm Q l.le _ _, show C' _ _=_ from hy j i, show C' _ _= _ from hy i j]; by_cases e:i.2=j.2; · simp [A,e,Complex.real_smul]
 simp [A,e,Ne.symm e,Complex.real_smul] -- tune
end YM.CF.XGarden.MastTin.ArtCart
end
