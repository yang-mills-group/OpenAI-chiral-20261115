import YM.SU5.Celeste.Banquet
import YM.SU5.Celeste.Stanzas
/-! # Flat comparisons BEFORE pruning. tools. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 200000
noncomputable section
namespace YM.CF.Lamour.Bridge.Celeste
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Pannier.Chancel Brace Velvet Hours Flare Cliplet RG Reed
open Py.Rate.Pannier
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
open Py Py.Rate Py.Rate.LocalLimit
open Py.Rate.LocalLimit.Papal (Weaver household)
open Signal.Interval (separationCost)
open Buffered.Afterglow
open Buffered.Lifted Ballad Window
open Pannier.Chancel Push.SectorMeasure
variable {N:Side}{S:Finset Cover}{ζ:ℝ}
lemma tilreal {X:Pane N}(p:Rightful (dBook N S) X 1 ζ)(i:Axis)(x:Cover)(v:x∈ S)(t:x+step i∈ S): ‖brand (onC N X (x,i))-brand (onC N 1 (x,i))‖≤ζ:=by
 rw [onC_spec,onC_spec]; apply (riotPort ..|>.1 p) (wrap _ x,i) (mem_filter.mpr ⟨mem_univ _,mem_image_of_mem _ v,?_⟩); have h:= mem_image_of_mem (wrap (More N)) t; rw [map_add,wrap_step] at h; exact h
lemma turnreal {X:Pane N}(p:Rightful (dBook N S) X 1 ζ)(i:Lattice.Step)(x:Cover)(u:x∈ S)(t:x+i.vec∈ S): ‖brand (i.read (onC N X) x)-brand (i.read (onC N 1) x)‖≤ ζ:=by
 rcases i with ⟨i,b⟩; cases b; exact tilreal p i x u t; change ‖brand (onC N X _)⁻¹-brand (onC N 1 _)⁻¹‖ ≤_; rw [brand_inv,brand_inv,←star_sub,norm_star]; exact tilreal p i _ (by simpa [sub_eq_add_neg,Step.vec] using t) (by rw [sub_add_cancel]; exact u)
lemma travelD {X:Pane N}(h:Rightful (dBook N S) X 1 ζ)(p:0≤ζ)(x:Cover)(w:Walk)(q:∀ i∈ visits x w,i∈ S) :
    ‖brand (travel (onC N X) x w)-brand (travel (onC N 1) x w)‖≤ w.length*ζ:=by
 induction w generalizing x with
 | nil=> simp [travel]
 | cons i W ih=>
    have he:x ∈ S:= q _ (by simp [visits]); have hh:∀ y∈visits (x+i.vec) W, y∈S:=fun y t=> q y (by simp [visits,t]); -- tune
    have hp:x+i.vec∈S:=hh _ (by cases W <;> simp [visits]); let d:=x+i.vec
    let A:=brand (i.read (onC N X) x); let V:=brand (i.read (onC N 1) x); let U:= brand (travel (onC N X) d W); let P:=brand (travel (onC N 1) d W)
    rw [travel,travel,brand_mul,brand_mul]; change ‖A*U-V*P‖≤_; rw [show A*U-V*P=A*(U-P)+(A-V)*P from (by simp only [sub_mul,mul_sub]; abel)]; refine (norm_add_le ..).trans ((add_le_add (norm_mul_le ..) (norm_mul_le ..)).trans ?_); rw [show ‖A‖=_ from brand_norm _,show ‖P‖=_ from brand_norm _,one_mul,mul_one]; push_cast[List.length_cons]; rw [add_mul,one_mul]; exact add_le_add (ih d hh) (turnreal h i x he hp)
variable {R:ℕ}
variable (A:Lead R)(W:Lead.Clan)
local notation "O" => A.patio
def coilFlag (i j: SU.Slot)(U:LinksC):ℂ:= (matter (travel U (nodeC A.birth) A.traceV)).val i j
def coilC (i j:SU.Slot): Weaver:=fun N X=> coilFlag A i j (onC N X.1) • (1: FC _)
lemma coil_paid (i j:SU.Slot): Coeff false O (coilFlag A i j∘Prod.fst):= Coeff.fromC _ _ ((matter_cont.comp (Wilson.continuous_travel _ _)).matrix_elem i j) (fun X Y h=>congrArg (fun t:SU.E=> (matter t).val i j) (travel_local _ _ X Y (fun e u v=> h e (List.mem_toFinset.mpr u) (List.mem_toFinset.mpr v))))
lemma rho_near(i j:SU.Slot)(x:Fields N)(h:Rightful (dBook N O) x.1 1 ζ)(w:0≤ζ) : ‖coilC A i j N x - coilC A i j N (1,1)‖≤ A.traceV.length*ζ:=by
 let X:= travel (onC N x.1) (nodeC A.birth) A.traceV; let Y:=travel (onC N 1) (nodeC A.birth) A.traceV; unfold coilC; rw [←sub_smul,norm_smul,norm_one,mul_one]; let Z:=brand X-brand Y
 change ‖Z.1 i j‖≤_; exact ((norm_entry ..).trans (norm_fst_le Z)).trans (travelD h w _ A.traceV (fun i t=> List.mem_toFinset.mpr t)) -- norm_fst_le?
lemma coil_pass (i j:SU.Slot) : Passion (coilC A i j) O false:=by
 refine ⟨⟨1,zero_le_one,fun N X=>?_⟩,?_,?_,fun _=> InTest.seed (coil_paid ..)⟩
 · unfold coilC coilFlag; rw [norm_smul,norm_one,mul_one]; exact (norm_entry ..).trans (CStarRing.norm_of_mem_unitary (matter _).property).le
 · intro ε h; filter_upwards [self_mem_nhdsWithin,eventually_nhdsWithin_of_eventually_nhds (ge_mem_nhds (show (0:ℝ) < ε/(A.traceV.length+1) from (by positivity)))] with x v p N k t _; change 0 < x at v; exact (rho_near A i j _ t v.le).trans (by have ht:x*((A.traceV.length:ℝ)+1) ≤ ε:= (le_div_iff₀ (by positivity : 0<(A.traceV.length:ℝ)+1)).1 p; linarith only [ht,v])
 intro N; refine ⟨Env.compact ?_,?_,fun _=> Reed.Fine.one.scale _⟩
 · let f:=fun V: LinksC=> coilFlag A i j V; have he:Continuous f:= (matter_cont.comp (Wilson.continuous_travel _ _)).matrix_elem i j; exact ((he.comp (on_cont _)).comp continuous_fst).smul continuous_const
 intro x y u v; apply congrArg (fun t:ℂ=>t • (1:FC (Single _))); exact (coil_paid ..).locus (Prod.map (onC N) (onC N) x) (Prod.map (onC N) (onC N) y) (on_agree _ u) (on_agree _ v)
def trailC (i j:SU.Slot): Weaver := fun N _=> (Fock.remove (A.lower N j)*create (A.upper N i))
lemma stanza_book (i j:SU.Slot)(K:Calibration): household K (coilC A i j*trailC A i j)=scalar K ((coilFlag A i j)∘Prod.fst)*(removal K A.death (dnSpin A.slot) j* creation K A.birth (upSpin A.slot) i):=rfl
lemma porchBorn(A:Lead R):nodeC A.birth∈A.patio:=by unfold Lead.patio; cases A.traceV<;> simp [visits]
lemma porchGone(A:Lead R):nodeC A.death∈ A.patio:= by
 unfold Lead.patio; apply List.mem_toFinset.mpr; rw [← A.moves]; apply show ∀ s:Cover,∀ l:Walk,stop s l∈visits s l from ?_; intro s l; induction l generalizing s<;> simp_all [visits,stop]
lemma trail_pass (i j:SU.Slot): Passion (trailC A i j) O false:=by
 refine ⟨⟨1,zero_le_one,fun N _=>?_⟩,fun a h=> Eventually.of_forall (fun v _ _ _ _=>by simpa [trailC] using h.le),?_,fun K=> .mul (.remover j (dn_half _) (porchGone A)) (.creator i (up_half _) (porchBorn A))⟩
 · have h(x:Cover)(i:SpinIdx)(j:SU.Slot): ‖basisC N x i j‖=1:=by unfold basisC Lifted.winding; rw [norm_smul,Rush.fee_norm]; simp
   exact (norm_mul_le ..).trans (mul_le_one₀ ((cost_pe true _).trans_eq (h ..)) (norm_nonneg _) ((cost_pe false _).trans_eq (h ..)))
 intro N; have hp(x:Cover)(i:SpinIdx)(b:SU.Slot)(v:nodeC x∈O): withinM (modesIn N (dBook N O)) (basisC N x i b):= by
    unfold withinM basisC; rw [map_smul,within_basis _ (Lifted.index N x i b)]; rw [modes_at]; change node (wrap N x)∈ dBook N O; rw [node_of]; exact mem_image_of_mem _ v
 refine ⟨ Env.compact continuous_const, fun _ _ _ _=>rfl,fun _=> (fine_remove (A.lower N j) ?_ (hp _ _ _ (porchGone _))).grow (fine_create (A.upper N i) ?_ (hp _ _ _ (porchBorn _)))⟩
 · unfold Lead.lower basisC withinM; rw [map_smul,within_basis _ (Lifted.index _ _ _ _) (mem_compl.mpr fun h=> dn_half A.slot ((mem_Tset ..).1 h))]
 unfold Lead.upper basisC withinM; rw [map_smul,within_basis _ (Lifted.index _ _ _ _) ((mem_Tset ..).2 (up_half _))]
lemma banner_sum: A.groundWord W=Lead.sing R A.wave • ∑ i∈colors W,∑ j∈colors W,coilC A i j*trailC A i j:=by
 funext N X; rw [Lead.groundWord]; simp_rw [Pi.smul_apply,Finset.sum_apply,Pi.mul_apply,coilC,trailC,Algebra.smul_mul_assoc,one_mul]; rfl
lemma flourish: Voice (A.groundWord W) O:= by refine ⟨?_,fun _=> A.groundWord_cov W⟩; rw [banner_sum]; exact (Passion.weaveSum _ _ (fun i _=> Passion.weaveSum _ _ (fun j _=> (coil_pass A i j).spun (trail_pass A i j)))).haze _
lemma shinesFil (u:0<R)(K:Calibration) : household K (A.groundWord W)∈Pannier.Chancel.Filigree K W (fun _:Fin 1=> A.death) O:=by
 have he: household K (A.groundWord W)= Lead.sing R A.wave • ∑ i∈colors W,∑ j∈colors W,household K (coilC A i j * trailC A i j):=by rw [banner_sum]; unfold household; funext m; simp_rw [Pi.smul_apply,Finset.sum_apply]
 rw [he]; refine Submodule.smul_mem _ _ (Submodule.sum_mem _ (fun i p=> Submodule.sum_mem _ (fun j q=> Submodule.subset_span (show household K _ ∈ _ from ?_)))) -- elaborate
 let h:= removal K A.death (dnSpin A.slot) j* creation K A.birth (upSpin A.slot) i; refine ⟨h,_,Submodule.subset_span (show h∈ _ from ?_),coil_paid A i j,stanza_book ..⟩
 have hv:A.birth≠ A.death:=by intro x; have h:= A.aligns; rw [←x] at h; have hp:=congr_fun h 3; simp [direction] at hp; cases e:A.wave <;> simp [Ballad.sail,e] at hp <;> omega
 refine ⟨[0],List.cons_ne_nil _ _, List.nodup_singleton _,?_⟩; nth_rw 1 [←mul_one h]; exact CRow.pair 0 A.birth _ _ _ _ (mem_filter.mp q).2 (mem_filter.mp p).2 (dn_half _) (up_half _) (porchBorn A) (porchGone A) (fun _=>hv) CRow.gave
end YM.CF.Lamour.Bridge.Celeste
#print axioms YM.CF.Lamour.Bridge.Celeste.flourish
#print axioms YM.CF.Lamour.Bridge.Celeste.shinesFil
