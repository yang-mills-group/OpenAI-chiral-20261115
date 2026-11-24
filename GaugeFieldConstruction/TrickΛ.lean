import GaugeFieldConstruction.Merise
set_option autoImplicit false
set_option maxHeartbeats 280000
set_option maxRecDepth 5500
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
-- Epoch hull as quadratures. standard cost coupons
open scoped Kronecker
open YM.GaugeFieldConstruction
variable (x:Cover)(w:300<n.val)
namespace BluffV
open Cauchy
-- plen capital: anchor unweighted.White v
local instance : AddCommGroup ↥P14:= PackP.G.toAddCommGroup
local instance : AddCommGroup ↥P25:= PackM.G.toAddCommGroup
local instance : Module ℂ ↥P14:= PackP.S.toModule
local instance : Module ℂ ↥P25:= PackM.S.toModule
local instance : AddCommGroup ↥G15:= PackS.G.toAddCommGroup
local instance : Module ℂ ↥G15:= PackS.S.toModule
local instance : AddCommGroup ↥G3:= PackG.G.toAddCommGroup
local instance : Module ℂ ↥G3:= PackG.S.toModule
open Phys Row TableF.Lenten.Loden
open Matter (FlavorIndex)
open Raw Calibration
local instance : AddCommGroup Gκ:= PackH.G.toAddCommGroup
local instance : Module ℂ Gκ:= PackH.S.toModule
namespace Fables
open Conj
variable (R:Signed)(b:Bool)(d:Floor)
lemma axesF{k:Type}[AddCommGroup k][Module ℂ k](X Y:k)(q:Bool)(p r:FlavorIndex) : pay q (Pi.single (rev R r) Y:Fragment k) p= if rev R p =r then pay q Y else 0:=by
 have hp:p=rev R r ↔ rev R p=r:=⟨fun v=>by rw [v,rev_rev],fun v=>by rw [←v,rev_rev]⟩
 cases q <;> by_cases e:rev R p=r<;> simp only [pay_true,pay_false,Pi.neg_apply,Pi.single_apply,hp,e,ite_true,ite_false,not_false_eq_true, ↓reduceIte, neg_zero] -- tune X dummy
private def Talp0 : ↥P03 →ₗ[ℂ] Waves:= offM.comp (LinearMap.inl ..) -- tune
lemma billΦ0(v:Waves)(q:FlavorIndex): Align R b (Calibration.matter d) ((symf3 (bV0 v)) (rev R q)) (symf3 (bV0 (pressA R b v)) q):=by
 let y:=rev R q; let p:= bV0 v; let x:=Talp0 p; let P:=pressA R b x; let W:= pressA R b v; let Q:↥P03→ₗ[ℂ]J Row.f:=(LinearMap.proj (R:=ℂ) y).comp symf3; let f(w:P03):J Row.f:=symf3 (bV0 (pressA R b (Talp0 w))) q; have ht:bV0 W= bV0 P:=by apply Subtype.ext; unfold P W; rw [κ0,κ0]; try rfl
 change Align R b _ (Q p) (symf3 (bV0 W) q); rw [ht]; apply moment R b Q f ?_ ?_ (Function.uncurry alloy) _ p (crests _)
 · intro a c; unfold f; rw [map_add,press_a]; let A:↥P03→ₗ[ℂ]J Row.f:= (LinearMap.proj (R:=ℂ) q).comp symf3; exact map_add A _ _
 · intro a c; unfold f; rw [map_smul,press_c]; let A:↥P03→ₗ[ℂ]J Row.f:= (LinearMap.proj (R:=ℂ) q).comp symf3; exact map_smul A _ _
 rintro ⟨a,u⟩; let T:= alloy a u; change Align R b (Calibration.matter d) (symf3 (alloy a u) y) (f (alloy a u)); unfold f; rw [allot0 R b _ a u rfl,payM,TΦ,TΦ]; let e:=f3Act.cost R a; let x':=Row.B a; let m:=Row.B (R.perm a)
 change Align R b _ ((Pi.single u x':Fragment (J Row.f)) y) ((pay e (Pi.single (rev R u) m:Fragment (J Row.f))) q); rw [axesF R x',Pi.single_apply]; by_cases c:y=u; · rw [if_pos (show rev R q=u from c), if_pos c]; exact align_γ R b x' m e (f3_tr a) (fun w t' v=>readingB.moving R w t' v a)
 rw [if_neg (show ¬ rev R q=u from c),if_neg c]; exact align_bot R b
private def Talp1 : ↥P14 →ₗ[ℂ] Waves:= offM.comp (LinearMap.prod 0 (LinearMap.prod LinearMap.id 0)) -- tune
lemma billΦ1(v:Waves)(q:FlavorIndex): Align R b (Calibration.matter d) ((symf4 (bV1 v)) (rev R q)) (symf4 (bV1 (pressA R b v)) q):=by
 let y:=rev R q; let p:= bV1 v; let x:=Talp1 p; let P:=pressA R b x; let W:= pressA R b v; let Q:↥P14→ₗ[ℂ]J Row.f:=(LinearMap.proj (R:=ℂ) y).comp symf4; let f(w:P14):J Row.f:=symf4 (bV1 (pressA R b (Talp1 w))) q; have ht:bV1 W= bV1 P:=by apply Subtype.ext; apply ContinuousLinearMap.ext; intro t; unfold P W; rw [κ1,κ1]; try rfl
 change Align R b _ (Q p) (symf4 (bV1 W) q); rw [ht]; apply moment R b Q f ?_ ?_ rayone _ p (revAir _)
 · intro a c; unfold f; rw [map_add,press_a]; let A:↥P14→ₗ[ℂ]J Row.f:= (LinearMap.proj (R:=ℂ) q).comp symf4; exact map_add A _ _
 · intro a c; unfold f; rw [map_smul,press_c]; let A:↥P14→ₗ[ℂ]J Row.f:= (LinearMap.proj (R:=ℂ) q).comp symf4; exact map_smul A _ _
 rintro ⟨s,a,u⟩; let T:= spikeV s (alloy a u); change Align R b (Calibration.matter d) (symf4 (spikeV s (alloy a u)) y) (f (spikeV s (alloy a u))); unfold f; rw [allot1 R b _ s a u rfl,payM,TΦs,TΦs]; let e:=(kΦs R s).xor (f3Act.cost R a); let x':=figV s (Row.B a); let m:=figV (pΦs R s) (Row.B (R.perm a))
 change Align R b _ ((Pi.single u x':Fragment (J Row.f)) y) ((pay e (Pi.single (rev R u) m:Fragment (J Row.f))) q); rw [axesF R x',Pi.single_apply]; by_cases c:y=u; · rw [if_pos (show rev R q=u from c), if_pos c]; exact align_γ R b x' m e (trans_Δ s _ (f3_tr a)) (fun w t' v=>ache_R R w t' v _ _ (f3Act.cost R a) (readingB.moving R w t' v a) s)
 rw [if_neg (show ¬ rev R q=u from c),if_neg c]; exact align_bot R b
private def Talp2 : ↥P25 →ₗ[ℂ] Waves:= offM.comp (LinearMap.prod 0 (LinearMap.prod 0 LinearMap.id)) -- tune
lemma billΦ2(v:Waves)(q:FlavorIndex): Align R b (Calibration.matter d) ((symf5 (bV2 v)) (rev R q)) (symf5 (bV2 (pressA R b v)) q):=by
 let y:=rev R q; let p:= bV2 v; let x:=Talp2 p; let P:=pressA R b x; let W:= pressA R b v; let Q:↥P25→ₗ[ℂ]J Row.f:=(LinearMap.proj (R:=ℂ) y).comp symf5; let f(w:P25):J Row.f:=symf5 (bV2 (pressA R b (Talp2 w))) q; have ht:bV2 W= bV2 P:=by apply Subtype.ext; apply ContinuousLinearMap.ext; intro t; apply ContinuousLinearMap.ext; intro m; unfold P W; rw [κ2,κ2]; try rfl
 change Align R b _ (Q p) (symf5 (bV2 W) q); rw [ht]; apply moment R b Q f ?_ ?_ raytwo _ p (reverb _)
 · intro a c; unfold f; rw [map_add,press_a]; let A:↥P25→ₗ[ℂ]J Row.f:= (LinearMap.proj (R:=ℂ) q).comp symf5; exact map_add A _ _
 · intro a c; unfold f; rw [map_smul,press_c]; let A:↥P25→ₗ[ℂ]J Row.f:= (LinearMap.proj (R:=ℂ) q).comp symf5; exact map_smul A _ _
 rintro ⟨s,t,a,u⟩; let T:= peakV s t (alloy a u); change Align R b (Calibration.matter d) (symf5 (peakV s t (alloy a u)) y) (f (peakV s t (alloy a u))); unfold f; rw [allot2 R b _ s t a u rfl,payM,TΦp,TΦp]; let e:=(kΦs R s).xor ((kΦs R t).xor (f3Act.cost R a)); let x':=figV s (figV t (Row.B a)); let m:=figV (pΦs R s) (figV (pΦs R t) (Row.B (R.perm a)))
 change Align R b _ ((Pi.single u x':Fragment (J Row.f)) y) ((pay e (Pi.single (rev R u) m:Fragment (J Row.f))) q); rw [axesF R x',Pi.single_apply]; by_cases c:y=u; · rw [if_pos (show rev R q=u from c), if_pos c]; exact align_γ R b x' m e (trans_Δ s _ (trans_Δ t _ (f3_tr a))) (fun w t' v=>ache_R R w t' v _ _ _ (ache_R R w t' v _ _ (f3Act.cost R a) (readingB.moving R w t' v a) t) s)
 rw [if_neg (show ¬ rev R q=u from c),if_neg c]; exact align_bot R b
private def Talp3 : ↥G15 →ₗ[ℂ] Waves:= LinearMap.prod 0 (LinearMap.prod 0 (LinearMap.prod 0 (LinearMap.prod 0 LinearMap.id))) -- tune
lemma billΦ3(v:Waves)(q:FlavorIndex): Align R b (Calibration.mixed d) ((task_M (bm5 v)) (rev R q)) (task_M (bm5 (pressA R b v)) q):=by
 let y:=rev R q; let p:= bm5 v; let x:=Talp3 p; let P:=pressA R b x; let W:= pressA R b v; let Q:↥G15→ₗ[ℂ]J Row.x:=(LinearMap.proj (R:=ℂ) y).comp task_M; let f(w:G15):J Row.x:=task_M (bm5 (pressA R b (Talp3 w))) q; have ht:bm5 W= bm5 P:=by apply grip_H; intro i j; unfold P W; rw [wind_V,wind_V]; try rfl
 change Align R b _ (Q p) (task_M (bm5 W) q); rw [ht]; apply moment R b Q f ?_ ?_ tallyΧ _ p (σshelfV _)
 · intro a c; unfold f; rw [map_add,press_a]; let A:↥G15→ₗ[ℂ]J Row.x:= (LinearMap.proj (R:=ℂ) q).comp task_M; exact map_add A _ _
 · intro a c; unfold f; rw [map_smul,press_c]; let A:↥G15→ₗ[ℂ]J Row.x:= (LinearMap.proj (R:=ℂ) q).comp task_M; exact map_smul A _ _
 rintro ⟨u,s,a⟩; let T:= affK u s a; change Align R b (Calibration.mixed d) (task_M (affK u s a) y) (f (affK u s a)); unfold f; rw [in_norm R b _ a s u rfl,payM,Tearn_X,Tearn_X]; let e:=x5Act.cost R (a,s); let x':=evalX (a,s); let m:=evalX (x5Act.move R (a,s))
 change Align R b _ ((Pi.single u x':Fragment (J Row.x)) y) ((pay e (Pi.single (rev R u) m:Fragment (J Row.x))) q); rw [axesF R x',Pi.single_apply]; by_cases c:y=u; · rw [if_pos (show rev R q=u from c), if_pos c]; exact align_γ R b x' m e (x5_tr (a,s)) (fun w t' v=>readingX.moving R w t' v (a,s))
 rw [if_neg (show ¬ rev R q=u from c),if_neg c]; exact align_bot R b
abbrev tiltΓ(v:UV d):UV d:=if (b.xor (detX R)) then shade d v else v
lemma spine_shift(v: Waves)(x:UV d)(h:SpineM v=shells d x): SpineM (pressA R b v)=shells d (spinFrame d R (tiltΓ R b d x)):=by
 set W:=pressA R b v
 apply Prod.ext
 · have ht:x.1=0:=(congrArg Prod.fst h).symm; change 0=_
   unfold tiltΓ; split; · change 0=bar x.1; rw [ht,map_zero]
   exact ht.symm
 apply Prod.ext
 · let K:=gauge d; have ht:Align R b K x.2.1.val (SpineM W).2.1:=by rw [show x.2.1.val=(SpineM v).2.1 from (congrArg (fun i:Shell=> i.2.1) h).symm,level_x, level_x]; exact align_add _ _ (bill_G R b d v) (bill_U R b d v)
   have hg:= align_v R b _ _ ht; unfold tiltΓ; split <;> rename_i hv
   · rw [if_pos hv] at hg; exact hg.symm
   rw [if_neg hv] at hg; exact hg.symm
 apply Prod.ext
 · ext1 i; let K:=Calibration.matter d; let y:=rev R i; let Z:=x.2.2.1 y; have ht:Align R b K Z.val ((SpineM W).2.2.1 i):=by rw [show Z.val= (SpineM v).2.2.1 y from (congrArg (fun x:Shell=> x.2.2.1 y) h).symm,EffortK,EffortK]; exact align_add _ _ (billΦ0 R b d v i) (align_add _ _ (billΦ1 R b d v i) (billΦ2 R b d v i))
   have hg:=align_v R b _ _ ht; unfold tiltΓ; split<;>rename_i hv
   · rw [if_pos hv] at hg; exact hg.symm
   rw [if_neg hv] at hg; exact hg.symm
 ext1 i; let y:=rev R i; let Z:=x.2.2.2 y; let K:=mixed d; have ht: Align R b K Z.val ((SpineM W).2.2.2 i):=by rw [show Z.val= (SpineM v).2.2.2 y from (congrArg (fun i:Shell=> i.2.2.2 y) h).symm,EffortK,EffortK]; exact billΦ3 R b d v i
 have hg:= align_v R b _ _ ht; unfold tiltΓ; split<;> rename_i hv
 · rw [if_pos hv] at hg; exact hg.symm
 rw [if_neg hv] at hg; exact hg.symm
lemma spin_wire (x:Sweep n)(v:Waves)(q:UV d)(u:SpineM v=shells d q): SpineM (Mason x v)= shells d (spinFrame d x.s⁻¹ (tiltΓ x.s⁻¹ x.charge d q)):=by rw [show Mason x v=pressA x.s⁻¹ x.charge v from (by unfold pressA Mason; rw [inv_inv])]; exact spine_shift _ _ _ _ _ u
lemma Floc_pays: Resonance=Floc:=by
 apply le_antisymm
 · apply Submodule.span_le.mpr; rintro v ⟨m,r,C,u,h⟩; have hp:C∈LinearMap.ker SpineM:= QuenchF.symm ▸ (show C∈ Floc from Submodule.subset_span (show _∈ {v|Looms v} from u)); rw [←QuenchF,h]; change SpineM _=0; rw [spin_wire Floor.five r C (0:UV Floor.five) (by rw [map_zero]; exact hp)]; unfold tiltΓ; rw [map_zero,ite_self,map_zero,map_zero]
 apply Submodule.span_le.mpr; intro x e; exact Submodule.subset_span (show Advects x from ⟨1,1,x,e,(lands_o x).symm⟩)
lemma sonic_K : Resonance=LinearMap.ker SpineM:= Floc_pays.trans QuenchF.symm
end Fables
end BluffV
end YM.CF.XGarden.MastTin.ArtCart
end
#print axioms YM.CF.XGarden.MastTin.ArtCart.BluffV.Fables.sonic_K
