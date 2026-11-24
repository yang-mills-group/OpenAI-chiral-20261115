import YM.CF.Oise.Flow
import YM.CF.Stake.Loom
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oise
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
section
open Scroll Yaw Phase Acorn Spire Eire
variable {ι U':Type}[MeasurableSpace ι]
lemma project_x {T V:Type}[MeasurableSpace V][Countable T](X:T→ Set ι)(p:∀ i,MeasurableSet (X i))(h: ∀ i:ι,∃ y,i∈X y){F:ι→ V} (g:∀ i,Measurable fun x:↥(X i)=> F x.val):Measurable F:=by
 intro s v; let Y(j:T):Set ι:= (fun x:↥(X j)=>x.val) '' ((fun x: ↥(X j)=> F x.val) ⁻¹' s); rw [show F⁻¹' s= ⋃ i,Y i from ?_]; exact MeasurableSet.iUnion fun i=> (MeasurableEmbedding.subtype_coe (p i)).measurableSet_image.mpr (g i v)
 ext i; constructor; intro hp; obtain ⟨u,t⟩:=h i; exact Set.mem_iUnion.mpr ⟨u,⟨i,t⟩,hp,rfl⟩; intro hp; obtain ⟨u,w,g,rfl⟩:= Set.mem_iUnion.mp hp; exact g
lemma finM {T:Type}[Countable T][MeasurableSpace T][MeasurableSingletonClass T]{F:Type}[MeasurableSpace F](g:ι→T)(W:ι→F)(p:Measurable g)(u:∀ v:T,Measurable (fun x: {i:ι//g i=v}=> W x.val)): Measurable W:= project_x (fun v=>{i|g i=v}) (fun v=>p (measurableSet_singleton v)) (fun i=>⟨_,rfl⟩) u
lemma mask_m {T:Type}[MeasurableSpace T][Zero T](F:ι→T)(u:Set ι)(hu:MeasurableSet u) (p: Measurable (fun x:↥u=> F x.val)): Measurable (u.indicator F):=by
 refine measurable_of_restrict_of_restrict_compl hu ?_ ?_
 · rw [show Set.restrict u (u.indicator F)= (fun x:↥u=> F x.val) from funext fun i=> Set.indicator_of_mem i.property _]; exact p
 rw [show Set.restrict uᶜ (u.indicator F)=(fun _=>0) from funext fun i=> Set.indicator_of_notMem i.property _]; exact measurable_const
lemma atlas_m {T:Type}[MeasurableSpace T][Countable T][MeasurableSingletonClass T]{P:Type}[MeasurableSpace P](U:ι→T)(Q:ι→ T→P)(p:Measurable U)(u:∀ i,Measurable (fun x=> Q x i)) : Measurable fun i=> Q i (U i):=by
 apply finM U _ p; intro w;  simp_rw [show ∀ (i:{j//U j=w}),U i.val=w from fun i=>i.property]; exact (u w).comp measurable_subtype_coe
local instance (I:Type)[Fintype I][DecidableEq I]:MeasurableSpace (Op I):=borel _
local instance (I:Type)[Fintype I][DecidableEq I]:BorelSpace (Op I):=⟨rfl⟩
variable {N P B L:Side}{k j r:ℕ}{e D a b c d t w:ℝ}{J:Pride (mid P B)}{Y:Tints P B e}{ho: Odd L.val}{A':Pricing j L ho (Thread j)}{P':Grasp A' B e}{U:∀ S:Support (Domain P B),Lend P B e S}{Z:Aim (mid P B)}{Z0:Male}
local notation "ϰ"=> (mid P B)
abbrev gau(n:Side):= Skye.Seat n→ SU.E
abbrev letT(s:Sweep N)(g:gau N):Ids N:= fun i=> (0,s,g i)
variable {n:Side}
lemma chip_m(X:Support (More n)): Measurable (Hive.chip X):=by -- elaboration tune
 unfold Hive.chip; exact atlas_m _ (fun (V:Ids n) i=> (V i).2.1) ((mastM X).comp (measurable_pi_lambda _ fun i=> (measurable_pi_apply _).fst)) (fun i=> (measurable_pi_apply i).snd.fst)
private lemma oceane {G:Type}[TopologicalSpace G]{X:Type}[LinearOrder X][Fintype X](U:G→UNI X)(p:Continuous (fun i=>(U i).val)): Continuous fun i:G × FC X=> lotB false false (U i.1) i.2:=by
 let N(i:G × FC X): FC X:= Fock.quant (U i.1).val; rw [show (fun i:G × FC X=> lotB false false (U i.1) i.2)=(fun i:G × FC X=> CF.twist (quantU (U i.1)) i.2) from rfl]; simp_rw [twist_formula]; have hz:Continuous N:= Fock.quant_cont.comp (p.comp (@continuous_fst G (FC X) _ _))
 have ht: Continuous (fun i:G × FC X=> N i * i.2):=Continuous.mul (f:=N) (g:=Prod.snd) hz continuous_snd; have he: Continuous (fun i:G × FC X=>star (N i)):=continuous_star.comp hz; exact (ht.mul he:Continuous (fun i:G × FC X=> (N i*i.2) * (star (N i))))
private lemma haze_c : Continuous fun i:gau n × FC (Single n)=> Hive.Gaze i.1 i.2:=by
 let U(g:gau n):= tradew n g; have hu: Continuous (fun g:gau n=>(U g).val):=by
    refine continuous_pi fun i=> continuous_pi fun j=>?_ ; unfold U tradew; simp only [jump_apply]; split; exact (SU.matter_cont.comp (show Continuous (fun t:gau n=> t (node i.1.1)) from continuous_apply _)).matrix_elem _ _; exact continuous_const
 exact oceane U hu
variable{S: StepData (Domain N B) (Domain P B)}(X:Hos S r)
local notation "R'"=> (danceL S X.val r)
local notation "ψ"=> gau (mid P B) × Castle P B e (danceL S X.val r)
variable (v:Dyes D e J k Y a b)(p:Vista P' Z0 Z U k t d c w)
include v p
lemma lawn_c(s:Sweep ϰ)(i:Support (Domain P B)×Support (Domain P B)): Continuous (fun j:ψ=> Scion.stock e R' Y U j.2 (letT s j.1) i):=by
 have hy(g:gau ϰ): Hive.chip R' (letT s g)=s:=rfl
 have ht(j:ψ): strideH R' (letT s j.1) j.2 = moveD s (letT s j.1) j.2:=rfl; let K':= fun j:ψ=> moveD s (letT s j.1) j.2; have hv:Continuous K':=by
    apply continuous_induced_rng.mpr; change Continuous (fun v:ψ=> (K' v).val)
    apply continuous_pi; intro i; refine (revM s).comp (f:=fun v:ψ=> Lattice.gauge v.1 (v.2.val i)) ?_ -- tune
    refine (continuous_pi fun k=>?_ : Continuous (fun v:ψ=> Lattice.gauge (v.1) (v.2.val i))); have hy(i:Seat (mid P B)):Continuous (fun z:ψ=> z.1 i):=(continuous_apply _).comp continuous_fst; exact ((hy _).mul ((continuous_apply k).comp ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)))).mul (hy _).inv
 have hx:= dance_g S X; have hp:= p.carry _ (grove_t _ s hx); obtain ⟨V,h⟩:= v.arch _ (grove_t _ s hx)
 unfold Scion.stock; refine Continuous.smul (f:=fun j:ψ=> strokeC e _ i.1 Y (letT s j.1) j.2) ?_ (show Continuous (fun j:ψ=>hula U R' j.2 (letT s j.1) {i.2}) from ?_)
 · have he(b:Bool):Continuous (cSignX b):= by cases b; exact continuous_id; exact continuous_star
   change Continuous (fun j:ψ=> cSignX (Hive.χ s) (Y _ (actS s i.1) (K' j))); exact (he (Hive.χ s)).comp ((h.1 (actS s i.1)).1.cont.comp hv)
 simp_rw [viewX]; let Xζ(j:ψ):= cozen U _ (turnZ s {i.2}) (K' j); have hX:Continuous Xζ:=by
    unfold Xζ cozen; apply continuous_finsetSum; intro i v; split; unfold Hive.vowC; exact ((hp.1 i).2.2.2.2.cont.comp hv).smul continuous_const; exact continuous_const
 have ht1:Continuous (Hive.teen s⁻¹):=Scree.tour_c ..
 change Continuous (fun i:ψ => Hive.Gaze i.1⁻¹ (Hive.teen s⁻¹ (Xζ i))); exact Continuous.comp (g:=fun i=> Hive.Gaze i.1 i.2) (f:=fun i=>(i.1⁻¹,Hive.teen s⁻¹ (Xζ i))) haze_c ((continuous_fst.inv).prodMk (ht1.comp hX))
lemma sock_u (i:Support (Domain P B)×Support (Domain P B))(j:Ids ϰ)(W: Castle P B e R') : Scion.stock e R' Y U W j i= Scion.stock e R' Y U W (letT (Hive.chip R' j) (Skye.frameP j)) i:=rfl
-- arbitrary family.T
include p v
lemma lawn_m (C:ι→ Castle P B e R')(T:ι→ Ids ϰ)(i:Support (Domain P B) × Support (Domain P B))(hp:∀ j:Bool,∀ k:Bond (Domain P B),Skye.ends k⊆i.1∪ i.2→Measurable (fun x=> (C x).val j k))(hT:Measurable T) : Measurable fun x=> Scion.stock e R' Y U (C x) (T x) i:=by
 let g(x:ι):=Skye.frameP (T x); let U0(x:ι):=(g x,C x)
 let V(s:Sweep ϰ)(y:ψ):=Scion.stock e R' Y U y.2 (letT s y.1) i
 let t(x:ι):= Hive.chip R' (T x)
 have hs: (fun x=> Scion.stock e R' Y U (C x) (T x) i)=(fun x=> V (t x) (U0 x)):=rfl
 rw [hs]; refine atlas_m t (fun x j=> V j (U0 x)) ((chip_m _).comp hT) (fun j=>?_); let Z:= {k:Bond (Domain P B)//Skye.ends k⊆ i.1 ∪ i.2}; let Ps(x:ψ): gau (mid P B) × (Bool→Z→SU.E):= (x.1,fun i j=>x.2.val i j.val); have ht:Continuous Ps:=by unfold Ps; apply continuous_fst.prodMk; apply continuous_pi; intro i; apply continuous_pi; intro k; exact (continuous_apply _).comp ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd))
 refine project_meas Ps (V j) U0 ht (lawn_c X v p j i) (fun u y ht=> ?_) (Measurable.prodMk (measurable_pi_lambda _ fun k=>((measurable_pi_apply k).comp hT).snd.snd) (measurable_pi_lambda _ fun y=>measurable_pi_lambda _ fun z=>hp y z.val z.property))
 exact Eire.lit_i S U Y (X,i) p J v u.2 y.2 _ _ (fun x _=>congrArg (fun z:gau (mid _ _)=>letT j z x) (show (Ps u).1=(Ps y).1 from congrArg Prod.fst ht)) (fun b k v h=>congrFun (congrFun (congrArg Prod.snd ht) b) (⟨k,insert_subset v (singleton_subset_iff.mpr h)⟩:Z))
end
end YM.CF.Oise
