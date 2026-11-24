import GaugeFieldConstruction.ExalterNX
import GaugeFieldConstruction.BlueMetaNX
import GaugeFieldConstruction.Plank
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 130000
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
namespace Spine
open Aria Set OS.Semigroup Ballad Six Glaze
open Papal FrameP Fock.Flux Gleam BProof.PricePort Gleam.Guide Gleam.clocks
open Lead Designs
-- actual Legend.T criterion ADDS no change in right hand ph pairing. path Mat.Coordinates in Gauge._
open XGarden XGarden.MastTin XGarden.Shield
open Scree.Ing.Ivey.ShoreQ
open AnalyticBridge VerifiedReset Taxi Push.Uniform Tap
open TableF TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
variable {n:Side}{N:ℕ}(A:BeaconNX N)(P:BudgetPoint)
abbrev WindLifeNX (n:Side):ℂ:= Lifted.winding n A.1.birth * Lifted.winding n A.1.death
abbrev RetB_NX (n:Side) : hart_X n:= fun i=> Lead.batonNX A.2.1 (wrap n A.1.birth, upSpin A.2.2.1) (wrap n A.1.death,dnSpin A.2.2.2) (A.1.laps i)
abbrev PureFNX(n:Side): Paper n:= XGarden.MastTin.plac (RetB_NX A n) true
abbrev BookBirthNX (n:Side): Paper n:= WindLifeNX A n • PureFNX A n
lemma chargeLegNX(n:Side):portable (BookBirthNX A n):=by
 apply port_m; apply port_pack; intro i g; unfold RetB_NX
 let B:= A.1; let x:=node (wrap n B.birth); let y:= node (wrap n B.death); let V:=g x* B.laps i*(g y)⁻¹
 have he: B.laps (GA g i)=V:=by unfold V x y; rw[B.laps_t]; unfold GA; rw [travel_gauge,B.laps_t,node_of,node_of, ← wrap_stop_cover,B.moves]
 exact (baton_mvNX A.2.1 _ _ (B.laps i) g).trans (congrArg (batonNX A.2.1 _ _) he.symm)
abbrev wordLegNX (n:Side)(i j:SU.Slot):Wa n:= some (true,Lifted.index n A.1.birth (upSpin A.2.2.1) i, Lifted.index n A.1.death (dnSpin A.2.2.2) j)
abbrev PinAmplNX (n:Side) (i j:SU.Slot)(x: Pane n):ℂ:= Lead.VLeadNX A.2.1 (A.1.laps x) i j
lemma alignsΦNX(n:Side) : PureFNX A n= ∑ y:SU.Slot×SU.Slot, XGarden.MastTin.isolate (wordLegNX A n y.1 y.2) (PinAmplNX A n y.1 y.2):=by
 funext i; rw [Finset.sum_apply]
 let S:=RetB_NX A n; let f(k:SU.Slot×SU.Slot):=wordLegNX A n k.1 k.2
 have he(y:SU.Slot ×SU.Slot): (PureFNX A n) (f y) = PinAmplNX A n y.1 y.2:=funext fun x=>by unfold PureFNX f wordLegNX XGarden.MastTin.plac RetB_NX; simp only[ite_true,Lifted.index,batonNX,Matrix.of_apply,and_self,true_and,↓reduceIte]
 by_cases h:i∈Set.range f
 · obtain ⟨k,rfl⟩:=h; rw [sum_eq_single k]; rw[he,XGarden.MastTin.isolate,Pi.single_eq_same]; intro u _ p; apply Pi.single_eq_of_ne (M:=fun _=> XGarden.MastTin.Lit n) ?_ -- tune binder
   intro x; let hv:= Option.some.inj x; exact p (Prod.ext (congrArg (fun p:(Bool×Single n×Single n)=>p.2.1.2) hv.symm) (congrArg (fun p=>(p:Bool× Single n×Single n).2.2.2) hv.symm))
   simp
 rw [sum_eq_zero (fun (j:SU.Slot × SU.Slot) _=> (show XGarden.MastTin.isolate (wordLegNX A n j.1 j.2) (PinAmplNX A n j.1 j.2) i=0 from (Pi.single_eq_of_ne (M:=fun _=>XGarden.MastTin.Lit n) (show i≠ f j from fun e=>h ⟨_,e.symm⟩) _)))]; rcases i with _|⟨i,j,k⟩; · rfl
 cases i; · rfl
 funext x; change (RetB_NX A n x) j k=0; unfold RetB_NX Lead.batonNX; rw[Matrix.of_apply,if_neg]; intro g; apply h; refine ⟨(j.2,k.2),congrArg some (Prod.ext rfl (Prod.ext ?_ ?_))⟩
 · exact Prod.ext g.1.symm rfl
 exact Prod.ext g.2.symm rfl
lemma bookGritNX (v:Fields n) : marketD (BookBirthNX A n) v.1=A.1.rollNX A.2.1 A.2.2.1 A.2.2.2 n v:=by
 unfold BookBirthNX; rw[conn_h, A.1.crestNX]
 change WindLifeNX A n • marketD (PureFNX A n) v.1= WindLifeNX A n • _
 refine congrArg (fun x:FC (Single n)=>WindLifeNX A n • x) (show marketD (PureFNX A n) v.1=_ from ?_); unfold PureFNX XGarden.MastTin.plac marketD; rw [Fintype.sum_option]; let L:= A.2.2; let B(i:Pane n):= RetB_NX A n i
 change (0:ℂ) • (1:FC (Single n))+_= _; rw [zero_smul,zero_add,Fintype.sum_prod_type,sum_eq_single true]; · rw [Fintype.sum_prod_type]; rfl
 · intro b _ p; cases b; · apply sum_eq_zero; intro i _; exact zero_smul ℂ _
   contradiction
 simp
-- uniform
section
private def LireH_NX(i j:SU.Slot)(g:VFlavorNX):Pal→L[ℝ]ℂ:= LinearMap.toContinuousLinearMap ⟨⟨fun p=>∑ k:SU.Slot,bookColorNX g i k*p ((0:SpinIdx),k) ((0:SpinIdx),j), fun x y=>by simp only [Matrix.add_apply, mul_add,sum_add_distrib]⟩,fun a b=>by simp only [Matrix.smul_apply]; rw [Finset.smul_sum]; apply sum_congr rfl; intro i _; rw [Algebra.mul_smul_comm]; rfl⟩
lemma AmplometerNX (i j:SU.Slot)(q:SU.E)(g:VFlavorNX): LireH_NX i j g (KinX q)= Lead.VLeadNX g q i j:=by
 unfold LireH_NX Lead.VLeadNX; rw[Matrix.mul_apply]; change ∑ k : SU.Slot,bookColorNX g i k* KinX q (0,k) (0,j)=_; apply sum_congr rfl; intro l _; rw [KinX,Matrix.kronecker_apply,Matrix.one_apply_eq,one_mul]
lemma feeLifeNX(n:Side): ‖WindLifeNX A n‖=1:=by
 let v:=WindLifeNX A n; have h:v*v=1:=by unfold v WindLifeNX; rw[show ∀ a b:ℂ,a*b*(a*b)=a*a*(b*b) from fun a b=>by ring, show Lifted.winding n A.1.birth*Lifted.winding n A.1.birth= 1 from fee_one (Rush.periods n A.1.birth),show Lifted.winding n A.1.death*Lifted.winding n A.1.death=1 from fee_one (Rush.periods n A.1.death),mul_one]
 change ‖v‖=1; have hb:=congrArg norm h; rw [norm_mul,norm_one] at hb; nlinarith [norm_nonneg v]
lemma accountPinNX : ∃ c:SU.Slot×SU.Slot→ℝ,∀ (n:Side)(P:BudgetPoint)(o:Skye.Seat n)(x:Support (More n)),P.order ≤ 6→ (A.1.patio.image (wrap (More n))) ⊆ x → ∀ i:SU.Slot × SU.Slot,MicroShipNX P x (PinAmplNX A n i.1 i.2) (c i):=by
 obtain ⟨C,h,H⟩:= Kin_1 6 (2*N); let f(i:SU.Slot×SU.Slot):Pal→L[ℝ]ℂ:=LireH_NX i.1 i.2 A.2.1
 refine ⟨fun i=> ‖f i‖*C,fun n P o x p t i=>?_⟩
 let g:= A.1.laps (N:=n); let u:= wrap (More n) (nodeC A.1.birth); let K:= A.1.traceV; have he(W:Pane n): g W=travel W u K:=by rw [show g W=_ from A.1.laps_t W]; rw [node_of]
 let V:=PinAmplNX A n i.1 i.2; have hv: V=(f i) ∘ KinX∘g:=funext fun w=>(AmplometerNX ..).symm
 rw [show PinAmplNX A n i.1 i.2=(f i) ∘ KinX∘g from hv]
 refine ⟨mul_nonneg (norm_nonneg _) (zero_le_one.trans h),Env.compact (Continuous.comp (f i).continuous (Continuous.comp KinC ?_)),?_,?_⟩
 · unfold g laps; exact (Cube.travel_cont _ _).comp (on_cont n)
 · intro U W q; refine congrArg (fun y=>(f i) (KinX y)) (show g U=g W from ?_); rw[he,he]; apply travel_local u K U W; apply agrees_mono q; intro y v
   -- membership.tune
   apply t
   let f:=wrap (More n); have he(k:Walk)(v:Cover): (visits v k).map f=visits (f v) k:=by
      induction k generalizing v with
      | nil=> rfl
      | cons i l h=> unfold visits; rw[List.map_cons,h]; unfold f; rw [map_add, wrap_vec] -- tune
   have hv:y∈(visits (nodeC A.1.birth) K).map f:=by rw[he]; exact v
   obtain ⟨x,h,rfl⟩:=List.mem_map.mp hv; exact mem_image.mpr ⟨x,List.mem_toFinset.mpr h,rfl⟩
 intro W
 have hp:= (H (More n) u W K A.1.costs.le).order p
 let L:= P.threshold • (ContinuousLinearMap.id ℝ (tangD n))
 have hw: ‖L‖≤1:= by unfold L; rw [norm_smul,Real.norm_of_nonneg P.threshold_pos.le]; exact mul_le_one₀ P.threshold_le (norm_nonneg _) ContinuousLinearMap.norm_id_le
 apply Jet.Allows.linear (f i) (f:=(KinX∘g)∘Shield.solo P.threshold W) _ le_rfl
 let Z(a:tangD n):= KinX (travel (RG.increment W a) u K)
 have ht:Jet.Allows P.order Z (0:tangD n) C :=⟨hp.analytic.of_le le_top,hp.norm_le⟩
 have hx:(KinX∘g)∘Shield.solo P.threshold W= Z ∘ L :=funext (fun v=>by simp only[Function.comp_apply,he]; rfl)
 rw [hx]; exact XGarden.comps L (by rw[L.map_zero]; exact ht) hw
#print axioms accountPinNX

end
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
