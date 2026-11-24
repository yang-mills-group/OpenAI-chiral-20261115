import YM.SU5.Diva.Revue
import YM.CF.Buffered.Duet
import YM.CF.Buffered.Flute
/-!
# Bilocal bilinear word tool
Generalize `Banquet`, `Nuptials` proofs. For compounds of varying arity on the same support.
-/
set_option autoImplicit false
set_option maxHeartbeats 470000
noncomputable section
namespace YM.CF.Buffered.Ballad
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Lifted Bilinear Window Skye
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
variable {R:ℕ}{B N:Side}
open YM.CF.Lamour.Bridge.Celeste
open Py.Rate.LocalLimit.Papal (Weaver household)
open Kea
open Flare

/-- path from birth to death over doubled grid; distinct-spin purchase allowed. -/
structure Twah where
 birth : Cover
 death : Cover
 up : Fin 2
 low : Fin 2
 traceV : Walk
 moves : Lattice.stop (nodeC birth) traceV=nodeC death

namespace Twah
open Lead (Clan clanOp clanMatrix clan_law)
variable (A: Twah)
def laps (V:Pane N) := Lattice.travel (onC N V) (nodeC A.birth) A.traceV
def coil (V:Pane N)(p q: SU.Slot):ℂ:= (matter (A.laps V)).val p q
def upper (N:Side)(p:SU.Slot) := basisC N A.birth (upSpin A.up) p
def lower (N:Side)(p:SU.Slot):= basisC N A.death (dnSpin A.low) p
def gold (R:ℕ):ℂ:= -(R:ℂ)^3
lemma laps_t (V:Pane N): A.laps V= Lattice.travel V (node (wrap N A.birth)) A.traceV:=by rw [laps,onC,travel_at,add_zero,node_of]
def groundWord (A:Twah)(R:ℕ)(s:Clan): Weaver:= fun N X=> gold R • ∑ p∈ colors s, ∑ q∈ colors s,(A.coil X.1 p q) • (Fock.remove (A.lower N q) * Fock.create (A.upper N p))
def patio(A:Twah):= (visits (nodeC A.birth) A.traceV).toFinset

variable (U:Clan)
local notation "Λu"=> cutM (colors U)
private lemma clan_index (V : SU.E) (x y : SU.Slot) : clanMatrix U V x y = if x∈ (colors U) ∧ y∈ (colors U) then (matter V).val x y else 0 := by by_cases h:x∈ (colors U)<;> by_cases k:y∈ (colors U)<;> simp [clanMatrix,cutM,Matrix.mul_diagonal,Matrix.diagonal_mul,h,k]
private lemma clan_dyad (x y : Site N × SpinIdx) (V : SU.E) : dg (clanOp U x y V)=∑ i∈(colors U), ∑ j∈ (colors U),(matter V).val i j • (put (x,i)*takeF (y,j)) := by
 let f(i j:Single N):= (clanOp U x y V) i j • (put i * takeF j)
 change ∑ i,∑ j, f i j=_
 have hp (a : Site N × SpinIdx) (i : SU.Slot) : ∑ t : Single N, f (a,i) t= ∑ j:SU.Slot, f (a,i) (y,j):=by
    rw [show (∑ t : Single N, f (a,i) t)=_ from Fintype.sum_prod_type (fun k : (Site N × SpinIdx) × SU.Slot=> f (a,i) k), sum_eq_single y]
    · intro i hi k; apply sum_eq_zero; intro j _; unfold f clanOp; rw [Matrix.of_apply,if_neg (fun z=>k z.2),zero_smul]
    simp
 rw [show (∑ i,∑ j,f i j)=_ from Fintype.sum_prod_type (fun k : (Site N × SpinIdx) × SU.Slot=> ∑ j, f k j)]; simp_rw [hp]
 rw [sum_eq_single x]; swap; · intro a _ t; apply sum_eq_zero; intro i _; apply sum_eq_zero; intro j _; unfold f clanOp; rw [Matrix.of_apply,if_neg (fun z=>t z.1),zero_smul]
 swap; · simp
 symm; let Z:= colors U;
 have hf(i j:Slot) : f (x,i) (y,j)=clanMatrix U V i j • (put (x,i)*takeF (y,j)):=by unfold f clanOp; rw [Matrix.of_apply,if_pos (show x=x∧ y=y from ⟨rfl,rfl⟩)];
 refine Eq.trans ?_ (sum_subset (f:=fun i=> ∑ j, f (x,i) (y,j)) (subset_univ (colors U)) ?_)
 · apply sum_congr rfl; intro i ti; refine Eq.trans ?_ (sum_subset (f:=fun j=> f (x,i) (y,j)) (subset_univ (colors U)) ?_)
   · apply sum_congr rfl; intro j tj; rw [hf,clan_index,if_pos ⟨ti,tj⟩]
   intro j _ t; rw [hf,clan_index,if_neg (fun w=>t w.2),zero_smul] -- indent
 intro i _ t; apply sum_eq_zero; intro j _; rw [hf,clan_index,if_neg (fun w=>t w.1),zero_smul]
lemma dgGround (V:Pane N) : let W:ℂ:= -gold R*Lifted.winding N A.birth * Lifted.winding N A.death; groundWord A R U N (V,1)=W • dg (clanOp U (wrap N A.birth,upSpin A.up) (wrap N A.death,dnSpin A.low) (A.laps V)) := by
 intro W; let P:Site N × SpinIdx:=(wrap N A.birth,upSpin A.up); let Q:Site N×SpinIdx:= (wrap N A.death,dnSpin A.low)
 rw [clan_dyad,groundWord]; simp_rw [smul_sum]; refine sum_congr rfl fun i _=> sum_congr rfl fun j _=>?_
 unfold lower upper basisC Fock.remove; rw [map_smul,map_smul,star_smul, create_put,create_put,Lifted.index, Lifted.index, Matrix.smul_mul, Matrix.mul_smul,show star (Lifted.winding N A.death)=_ from fee_real (Rush.periods N _)] -- tune
 let U₀:=put (P,i); let D:=takeF (Q,j); let c:=A.coil V i j; change _ • (c • (_ • (_ • (D*U₀))))= _ • (c • (U₀*D)); rw [show D*U₀=-(U₀*D) from (eq_neg_of_add_eq_zero_left ((mixed (Q,j) (P,i)).trans (if_neg ?_)))]; swap
 · intro v; exact dn_half A.low (by rw [show dnSpin A.low=upSpin A.up from congrArg (fun t:Single N=> t.1.2) v]; exact up_half _)
 simp only [smul_smul,smul_neg,W,neg_mul,neg_smul]; congr 2; unfold Lifted.winding; ring -- tune
lemma groundWord_cov : covariant (A.groundWord R U N) := by
 intro g u; change A.groundWord R U N (gauge g u.1,1) = twist _ (A.groundWord R U N (u.1,1)); rw [dgGround,dgGround,twist_scalar,dg_cov,clan_law,laps_t,laps_t,travel_gauge,node_of,node_of, ← wrap_stop_cover, A.moves] -- tune .reduce projecting pairs

end Twah
end YM.CF.Buffered.Ballad
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
namespace Gemini
variable {R:ℕ}
variable (A:Twah)(W:Lead.Clan)
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
lemma stanza_book (i j:SU.Slot)(K:Calibration): household K (coilC A i j*trailC A i j)=scalar K ((coilFlag A i j)∘Prod.fst)*(removal K A.death (dnSpin A.low) j* creation K A.birth (upSpin A.up) i):=rfl
lemma porchBorn(A:Twah):nodeC A.birth∈A.patio:=by unfold Twah.patio; cases A.traceV<;> simp [visits]
lemma porchGone(A:Twah):nodeC A.death∈ A.patio:= by
 unfold Twah.patio; apply List.mem_toFinset.mpr; rw [← A.moves]; apply show ∀ s:Cover,∀ l:Walk,stop s l∈visits s l from ?_; intro s l; induction l generalizing s<;> simp_all [visits,stop]
lemma trail_pass (i j:SU.Slot): Passion (trailC A i j) O false:=by
 refine ⟨⟨1,zero_le_one,fun N _=>?_⟩,fun a h=> Eventually.of_forall (fun v _ _ _ _=>by simpa [trailC] using h.le),?_,fun K=> .mul (.remover j (dn_half _) (porchGone A)) (.creator i (up_half _) (porchBorn A))⟩
 · have h(x:Cover)(i:SpinIdx)(j:SU.Slot): ‖basisC N x i j‖=1:=by unfold basisC Lifted.winding; rw [norm_smul,Rush.fee_norm]; simp
   exact (norm_mul_le ..).trans (mul_le_one₀ ((cost_pe true _).trans_eq (h ..)) (norm_nonneg _) ((cost_pe false _).trans_eq (h ..)))
 intro N; have hp(x:Cover)(i:SpinIdx)(b:SU.Slot)(v:nodeC x∈O): withinM (modesIn N (dBook N O)) (basisC N x i b):= by
    unfold withinM basisC; rw [map_smul,within_basis _ (Lifted.index N x i b)]; rw [modes_at]; change node (wrap N x)∈ dBook N O; rw [node_of]; exact mem_image_of_mem _ v
 refine ⟨ Env.compact continuous_const, fun _ _ _ _=>rfl,fun _=> (fine_remove (A.lower N j) ?_ (hp _ _ _ (porchGone _))).grow (fine_create (A.upper N i) ?_ (hp _ _ _ (porchBorn _)))⟩
 · unfold Twah.lower basisC withinM; rw [map_smul,within_basis _ (Lifted.index _ _ _ _) (mem_compl.mpr fun h=> dn_half A.low ((mem_Tset ..).1 h))]
 unfold Twah.upper basisC withinM; rw [map_smul,within_basis _ (Lifted.index _ _ _ _) ((mem_Tset ..).2 (up_half _))]
lemma banner_sum: A.groundWord R W=Twah.gold R • ∑ i∈colors W,∑ j∈colors W,coilC A i j*trailC A i j:=by
 funext N X; rw [Twah.groundWord]; simp_rw [Pi.smul_apply,Finset.sum_apply,Pi.mul_apply,coilC,trailC,Algebra.smul_mul_assoc,one_mul]; rfl
lemma flourish: Voice (A.groundWord R W) O:= by refine ⟨?_,fun _=> A.groundWord_cov W⟩; rw [banner_sum]; exact (Passion.weaveSum _ _ (fun i _=> Passion.weaveSum _ _ (fun j _=> (coil_pass A i j).spun (trail_pass A i j)))).haze _
end Gemini
end YM.CF.Lamour.Bridge.Celeste
#print axioms YM.CF.Lamour.Bridge.Celeste.Gemini.flourish
