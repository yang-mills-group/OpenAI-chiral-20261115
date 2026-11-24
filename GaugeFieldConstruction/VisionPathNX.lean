import GaugeFieldConstruction.HuskyChordNX
-- injectable telescopes.Maintain regulator paths for sewage.
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3800
set_option linter.unusedSectionVars false
set_option maxHeartbeats 90000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Ballad
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Lifted Bilinear Window Skye
open MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker InnerProductSpace Topology Classical
attribute [local instance] opCStarAlgebra
variable {R:ℕ}{B N:Side}
open YM.CF.Lamour.Bridge.Celeste
open Py.Rate.LocalLimit.Papal (Weaver household)
open Kea
open Flare
open Py.Rate.LocalLimit.Papal
open Afterglow
open FrameP Fock.Flux
namespace Lead
variable (A:Lead R)(k:VFlavorNX)(j w:Fin 2)(S:Support (More N))(p:Satin.region A.patio N⊆ S)
variable (N) (v:SU.Slot × SU.Slot)(u:ℂ)(U:SU.E)
abbrev aimπNX(v:SU.Slot): Single N:= Lifted.index N A.birth (upSpin j) v
abbrev aimθNX(w:Fin 2)(v:SU.Slot): Single N:= Lifted.index N A.death (dnSpin w) v
abbrev spliceNX : Rope N := ((u* (Lifted.winding N A.birth*Lifted.winding N A.death),[(false,A.aimπNX N j v.1),(true,A.aimθNX N w v.2)]),[])
abbrev railNX (x:SU.E):Ropes N:= (univ:Finset (SU.Slot × SU.Slot)).toList.map (fun v=>A.spliceNX N j w v (VLeadNX k x v.1 v.2)) -- implicit w not used in syntax in splice? included
lemma exhibitsPNX : motionF (A.spliceNX N j w v u).1=u • (create (A.highlightNX j N v.1) * Fock.remove (A.lowlightNX w N v.2)):=by
 let X:=A.aimπNX N j v.1; let Y:=A.aimθNX N w v.2
 have hp:rollC RootBay (A.spliceNX N j w v u).1.2=Fock.put X* Fock.takeF Y:=by change RootBay _*(RootBay (true,Y)*1)=_; rw[mul_one]; exact congrArg₂ (· * ·) (Fock.create_put ..) (Fock.remove_take ..)
 unfold motionF; rw[hp]; unfold highlightNX lowlightNX basisC Fock.remove; rw [map_smul,map_smul,star_smul, create_put,create_put,Matrix.smul_mul,Matrix.mul_smul,show star (Lifted.winding N A.death)=_ from fee_real _,smul_smul,smul_smul]; unfold spliceNX; refine congrArg (· • (Fock.put X*Fock.takeF Y)) ?_; unfold Lifted.winding; change u*(_*_)=_; ring
variable {N}
include p
lemma rubricSpNX : Rubric S 0 2 (A.spliceNX N j w v u):=by
 refine ⟨fun i e=>?_,Nat.zero_le 2,nofun⟩
 rw[List.mem_singleton.mp e]; refine ⟨even_two,Nat.le_refl 2,fun i t=>?_⟩
 have he(x:Cover)(i:SpinIdx)(b:SU.Slot)(t:nodeC x∈ A.patio):Lifted.index N x i b∈ onPage N S:=by
    apply mem_filter.mpr; refine ⟨mem_univ _,?_⟩; change node (wrap N x) ∈ S; rw [node_of]; exact p (mem_image_of_mem _ t)
 rcases (List.mem_cons.mp t) with rfl|q; exact he _ _ _ (porchBorn A)
 rw[List.mem_singleton] at q; rw [q]; exact he _ _ _ (porchGone A)
lemma pressedSpNX : pressedF (onPage N S) 2 ‖u‖ (u • (create (A.highlightNX j N v.1) * Fock.remove (A.lowlightNX w N v.2))):=by
 let X:= A.spliceNX N j w v u
 refine ⟨[X.1],(A.rubricSpNX j w S p v u).1,le_of_eq ?_, ?_⟩
 · simp [X,spliceNX,meterK, Lifted.winding,fee_norm]
 unfold orchestrate; simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]; exact A.exhibitsPNX N j w v u
omit p
abbrev FrontTagNX (z:Pane N):FC (Single N):= A.rollNX k j w N (z,1)
lemma seedRoleNX (V: Pane N){f}: dawn (A.railNX N k j w (A.laps V)) f= A.FrontTagNX k j w V:=by
 unfold FrameP.dawn railNX; rw [List.map_map, Finset.sum_map_toList,Fintype.sum_prod_type]; apply sum_congr rfl; intro x _; apply sum_congr rfl; intro y _; rw [Function.comp_apply]; unfold done; rw [A.exhibitsPNX,show Gleam.Guide.Hood.factorV (A.spliceNX N j w (x,y) (VLeadNX k (A.laps V) x y)).2 f=1 from rfl,Complex.ofReal_one,one_smul]
lemma lapsUnitNX: A.laps (1:Pane N)=1:= by
 rw[laps_t]; generalize A.traceV=L; generalize node _=x
 induction L generalizing x with
 | nil=>rfl
 | cons i L ih=>
   obtain ⟨i,b⟩:=i
   rw [travel,ih]
   cases b <;> first|rfl | (change ((1:SU.E)⁻¹*1= _);simp)|(change (1:SU.E)*1=_;simp)
abbrev majorPNX(k:VFlavorNX):ℝ:=∑ _i:SU.Slot,∑ _j:SU.Slot,‖bookColorNX k‖
lemma upfrontNX (U:SU.E)(v:SU.Slot×SU.Slot): ‖VLeadNX k U v.1 v.2‖ ≤ ‖bookColorNX k‖:=
   (norm_entry ..).trans_eq (CStarRing.norm_mul_coe_unitary ..) -- tune
-- measurable
local instance localGleNNX(a:Side) : MeasurableSpace (FC (Single a)):=borel _
local instance localGleIFNX(a:Side):BorelSpace (FC (Single a)):=⟨rfl⟩
open Girt Push.SectorMeasure CF.XGarden.MastTin.ArtCart.Zpress
include p
lemma uptonPNX : Upright N S (majorPNX k) 2 (A.FrontTagNX k j w):=by
 constructor
 · apply Env.compact; unfold FrontTagNX rollNX; refine continuous_finsetSum _ fun i _=> continuous_finsetSum _ (fun l _=> Continuous.smul (f:=fun z:Pane N=> Lead.VLeadNX k (A.laps z) i l) ?_ continuous_const); unfold VLeadNX; exact (continuous_const (y:=bookColorNX k)|>.mul (matter_cont.comp ((Cube.travel_cont _ _).comp (on_cont N)))).matrix_elem i l
 · intro x V; exact A.lawNX k j w V (x,1)
 intro V; change pressedF _ _ (∑ i:SU.Slot,∑ l:SU.Slot,‖bookColorNX k‖) (∑ i:SU.Slot,∑ l:SU.Slot,VLeadNX k (A.laps V) i l • (create (highlightNX A j N i)*Fock.remove (lowlightNX A w N l))); apply sum_C; intro i _; apply sum_C; intro z _ 
 exact lift_C (A.pressedSpNX j w S p (i,z) (VLeadNX k (A.laps V) i z)) (upfrontNX k (A.laps V) (i,z)) le_rfl (Subset.refl _)
lemma straightNX_U (U:SU.E) : Reeds (A.railNX N k j w U) 0 2 S (majorPNX k):=by
 refine ⟨fun v hp=>?_,?_⟩
 · obtain ⟨q,v,rfl⟩:= List.mem_map.mp hp; exact A.rubricSpNX j w S p q _
 unfold railNX meterK
 rw [List.map_map,List.map_map,sum_map_toList,Fintype.sum_prod_type]
 refine sum_le_sum fun i _=> sum_le_sum fun b _=>?_; dsimp only [Function.comp_apply,spliceNX]; simp only [norm_mul,Lifted.winding, fee_norm,mul_one]; exact upfrontNX k U (i,b) -- tune
-- cost
variable (a d t h C:ℝ)(r:0≤d)(hp:0≤C)(he:∀ U:SU.E, ‖(matter U).val-1‖≤ C* group.chord U)
-- text uses supports any; pins native meter.
include r hp he
lemma conductPNX (V:Pane N)(g:chordK S V d)(l v:SU.Slot) : ‖VLeadNX k (A.laps V) l v-VLeadNX k 1 l v‖≤ ‖bookColorNX k‖ * C * (2*R:ℕ)*d:=by
 have hx:=walkingFNX g p _ A.traceV (porchBorn A) (fun j i=>List.mem_toFinset.mpr i); rw [A.costs] at hx
 let X:= A.laps V; have hh:=he X
 apply (norm_entry (VLeadNX k X - VLeadNX k 1) l v).trans; unfold VLeadNX; rw [←mul_sub]; rw [map_one]; exact (norm_mul_le ..).trans ((mul_le_mul_of_nonneg_left (hh.trans (mul_le_mul_of_nonneg_left hx hp)) (norm_nonneg _)).trans_eq (by ring))
lemma BraceTaxNX: Telescope (A.FrontTagNX k j w) S (majorPNX k) (majorPNX k) 0 2 t a d (majorPNX k*C*(2*R:ℕ)*d) (A.railNX N k j w 1):=by
 refine ⟨A.uptonPNX k j w S p,A.straightNX_U k j w S p _,fun V _P_X hK => ?_⟩
 unfold propSeed; rw [←lapsUnitNX (A:=A) (N:=N),seedRoleNX]
 unfold FrontTagNX rollNX; simp only [lapsUnitNX]
 rw [←sum_sub_distrib]; simp_rw[←sum_sub_distrib, ← sub_smul]
 unfold majorPNX; simp_rw [sum_mul]
 refine ?_; -- sum_C
 apply sum_C; intro i _; apply sum_C; intro l _; exact lift_C (A.pressedSpNX j w S p (i,l) (VLeadNX k (A.laps V) i l-VLeadNX k 1 i l)) (A.conductPNX k S p d C r hp he V hK i l) le_rfl (Subset.refl _) -- helpers
#print axioms BraceTaxNX
end Lead
end YM.CF.Buffered.Ballad
end
