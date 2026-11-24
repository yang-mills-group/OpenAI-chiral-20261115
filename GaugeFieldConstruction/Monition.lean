import GaugeFieldConstruction.ManifestM
set_option autoImplicit false
set_option maxRecDepth 5500
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
namespace ArtCart
open Buffered Lifted Girt Skye Window Vale
variable {x y:Cover}{d:ℕ}{k:Side}
open TableF TableF.Lenten Layout Flot Moto Tap Bank ModuleB Haro Hove Fren Work.F03 Taxi
variable {F:Psu x 24}{p:BudgetPoint}{c v h:ℝ}(M: Male)
lemma hip_S (w:300<n.val)(r:300<k.val)(F:Psu x 24)(H:∀ i, LocalOn (cartO x 24) (F i))(V: Pane n)(W:Pane k)(u:Agrees (cartO x 24) (onC n V) (onC k W))(h:ℝ)(m:Views): streamF (cactusK n x) (orbitPH (AlphaY (pR n F) V)) h m= streamF (cactusK k x) (orbitPH (AlphaY (pR k F) W)) h m:=by
 rw [(bpu_T ..).1,(bpu_T ..).1,stream_M w,stream_M r]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; unfold AnteX κviews BarPhi; rw [H _ _ _ u, H _ _ _ u,pFκ x i (by omega) (lt_trans (by omega:100<300) r), pFκ x j (by omega) (lt_trans (by omega:100<300) r)]
lemma wing_S (w:300<n.val)(r:300<k.val)(F:Psu x 24)(H:∀ i, LocalOn (cartO x 24) (F i))(V: Pane n)(W:Pane k)(u:Agrees (cartO x 24) (onC n V) (onC k W))(h:ℝ): winJ (cactusK n x) M h (thrust (pR n F) V)= winJ (cactusK k x) M h (thrust (pR k F) W):=by
 rw [←(bpu_T ..).1,←(bpu_T ..).1]; refine ((tab (o:=cactusK n x) (h:=h) M _).equal (Eventually.of_forall (f:= _) fun v=> ?_ )).unique (tab (o:=cactusK k x) (h:=h) M _); unfold TabX; rw [hip_S w r F H V W u]
lemma life_S (w:300 <n.val)(F:Psu x 24)(U:Pane n): lifeH (AlphaY (pR n F)) U=F none (onC n U):=by rw [(bpu_T ..).2, show none=hereV n (none:jungle x 24) from rfl, pR_K n F (by omega) (none:jungle x 24),feeV]; simp
-- Pencil moves on $δ$ plane, card(cost) locks.
lemma lamp_cont_s (F: InkD n)(w:PressB p (Zhub (cactusK n x)) F h c)(u:0≤h): ContDiffAt ℝ ((↑(2:ℕ)): WithTop ℕ∞) (TableF.term F) 0 := (eraF _ _ w u 1 (ping_f p _)).paid.of_le (Nat.cast_le.mpr ((by decide:2≤6).trans p.order_ge))
lemma knob_start (k:Side): knob n x k 1=1:=funext fun i=> knob_E n x k 1 i
lemma lamp_agree (W:Pane k)(w:d<n.val):Agrees (cartO x d) (onC n (knob n x k W)) (onC k W):=fun i u v=> (cart_L w (onC k W) i u v).symm
lemma Ktrunc (W:tangD k) : knob n x k (increment 1 W)= increment 1 (knapp n x k W):=by
 have he:= Kturn n x k 1 1 W; change knob n x k (increment _ (1 • _))= increment (knob n x k _) (1 • _) at he; rw [knob_start,one_smul,one_smul] at he; exact he
lemma king_H (w:300<n.val)(h:300<k.val)(F:Psu x 24)(H:∀ i, LocalOn (cartO x 24) (F i)) : TableF.term (AlphaY (pR k F))= TableF.term (AlphaY (pR n F)) ∘ knapp n x k:=by
 funext i; unfold TableF.term; rw [Function.comp_apply,life_S h, life_S w,← Ktrunc]; exact (H none _ _ (lamp_agree _ (by omega))).symm
lemma king_P (w:300<n.val)(r:300<k.val)(F:Psu x 24)(H:∀ i, LocalOn (cartO x 24) (F i))(P:PressB p (Zhub (cactusK n x)) (AlphaY (pR n F)) h c)(s:0≤ h)(i j:tangD k) : let B:= AlphaY (pR n F); let V:=knapp n x k; ploy (AlphaY (pR k F)) i j=ploy B (V i) (V j):=by
 intro B V; have hp: ContDiffAt ℝ ((↑(2:ℕ)): WithTop ℕ∞) (TableF.term B) 0:= lamp_cont_s _ P s; let T:Fin 2→ tangD k:=![i,j]; rw [ploy_iter,ploy_iter, king_H w r F H, show ![V i,V j]=V ∘ T from (by ext1 i; fin_cases i<;> rfl)]; have he:iteratedFDeriv ℝ 2 (TableF.term B ∘ V) 0= ContinuousMultilinearMap.compContinuousLinearMap (iteratedFDeriv ℝ 2 (TableF.term B) 0) (fun _=> V):= Next.Foundations.jets_linear V hp; change iteratedFDeriv ℝ 2 (TableF.term B ∘ V) 0 T= _; rw [he]; rfl
lemma sailP (w:300<n.val)(r:300<k.val)(Z: Wheel Axis SU.group.Color)(a:ℝ): Agrees (knotX x 24 n) (knapp n x k (plot (cactusK k x) Z a)) (plot (cactusK n x) Z a):=by intro i p q; change a • Z i.2 (stem _ (wrap (More k) _))=a • Z i.2 _; rw [cart_acc _ (by omega:24<n.val) (by omega:24<k.val) _ p] -- tune
lemma scale_lamp (v:BudgetPoint)(w:300<n.val)(r:300<k.val)(z:ℝ)(x': ComG): Agrees (cartO x 24) (onC n (increment 1 (z • gateC (cactusK n x) v.threshold x'))) (onC k (increment 1 (z • gateC (cactusK k x) v.threshold x'))):=by
 let A:= gateC (cactusK n x) v.threshold x'; let Y:= gateC (cactusK k x) v.threshold x'; let L:= knapp n x k Y; have hp:=lamp_agree (x:=x) (increment 1 (z • Y)) (show 24<n.val by omega); rw [Ktrunc, map_smul] at hp; let U:= increment 1 (z • A); have he: Agrees (cartO x 24) (onC n U) (onC n (increment 1 (z • L))):=by
    apply Lifted.on_agree; rw [cart_T (show 24<n.val by omega)]; apply lift_pane _ _ A L; exact fun i u v'=> (sailP (x:=x) w r (formC x') v.threshold i u v').symm
 exact fun i u h=> (he i u h).trans (hp i u h)
lemma salon (w:300<n.val)(r:300<k.val)(F:Psu x 24)(H:∀ i, LocalOn (cartO x 24) (F i))(P:PressB p (Zhub (cactusK n x)) (AlphaY (pR n F)) h c)(Q:PressB p (Zhub (cactusK k x)) (AlphaY (pR k F)) h v)(W:Waves)(pF:MetaB (cactusK n x) M W (AlphaY (pR n F)) p h) (s:0≤h) : MetaB (cactusK k x) M W (AlphaY (pR k F)) p h:=by
 obtain ⟨u0,u1,u2,u3⟩:= pF; -- inspect order 
 let t:=p.threshold; let B:=AlphaY (pR k F); let A:=AlphaY (pR n F); let o:=cactusK n x; let T:=cactusK k x; let L:=knapp n x k
 let a:=AnalyticBridge.VerifiedReset.spike SU.group; let E:= gateC T t; let E':=gateT T t; let V:=gateC o t; let V':=gateT o t
 have hC(i:ComG):Agrees (Zhub o).val.2 (L (E i)) (V i):=sailP w r (formC i) t; have hT(i:ComT):Agrees (Zhub o).val.2 (L (E' i)) (V' i):=sailP w r (formT i) t
 constructor
 · rw [u0]; apply ContinuousLinearMap.ext; intro i; apply ContinuousLinearMap.ext; intro j; symm; exact (king_P w r F H P s (E (hem i a)) (E (hem j a))).trans (ploy_respect _ _ _ _ P s (hC _) (hC _))
 · rw [u1]; apply ContinuousLinearMap.ext; intro i; apply ContinuousLinearMap.ext; intro j; symm; exact (king_P w r F H P s (E (hem i a)) (E' (loomH j a))).trans (ploy_respect _ _ _ _ P s (hC _) (hT _))
 · rw [u2,(bpu_T ..).1,(bpu_T ..).1, wing_S M w r F H (1:Pane n) (1:Pane k)]; intro i _ _; rw [onC_spec,onC_spec]; rfl -- maybe solved
 rw [u3]; apply ContinuousLinearMap.ext; intro i; let U(m:Side)(x':ℝ):= increment (1:Pane m) (x' • gateC (cactusK m x) p.threshold i); let Y(m:Side)(t:ℝ):=sectorJ (orbitPH (AlphaY (pR m F) (U m t))) M (cactusK m x) h
 have he: Y n=Y k:=funext fun i'=> congrArg (fun z:PalOne=>z.1) (show winJ _ _ _ (orbitPH _) = winJ _ _ _ (orbitPH _) from ?_); swap
 · rw [(bpu_T ..).1,(bpu_T ..).1, wing_S M w r F H (U n i') (U k i') (scale_lamp p w r i' i)] -- implicit tuning
 exact (show HasDerivAt (Y n) _ 0 from landR M (o:=o) P i).unique (he.symm ▸ (show HasDerivAt (Y k) _ 0 from landR M (o:=T) Q i))
end ArtCart
end MastTin
end YM.CF.XGarden
end
