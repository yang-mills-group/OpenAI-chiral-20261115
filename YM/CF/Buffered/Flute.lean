import YM.CF.Buffered.Congress
import YM.CF.Mint.Stop
/-! Uniform tickets in the toron interval for these true-link marks. -/
set_option autoImplicit false
set_option maxHeartbeats 620000
set_option synthInstance.maxSize 18000
noncomputable section
namespace YM.CF.Buffered.Ballad
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Lifted Bilinear Window Skye Emu Onyx Kea Flare Dial Gall RG Scree Tenant Paige Vault Brace
open Cache Glaze
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
variable {R:ℕ}{B N : Side}{I : Type*}{C e v a b:ℝ}
namespace Lead
variable (A:Lead R)
lemma chant_c : Continuous (A.chant (N:=N)):=by
 apply Continuous.comp (g:=A.birthOp); swap; · exact continuous_fst
 unfold Lead.birthOp
 refine (continuous_const (y:=sing R A.wave)).smul (continuous_finsetSum _ fun i _=> continuous_finsetSum _ fun j _=> Continuous.smul (f:=fun x:Pane N=> A.coil x i j) ?_ (continuous_const (y:=(Fock.remove (A.lower N j) * create (A.upper N i)))))
 exact ((matter_cont.comp ((Cube.travel_cont _ _).comp (on_cont N))).matrix_elem i j)
private lemma internal_index (V : SU.E) (x y : SU.Slot) : internal V x y = if x∈ five ∧ y∈ five then (matter V).val x y else 0 := by by_cases h:x∈ five<;> by_cases k:y∈ five<;> simp [internal,cutM,Matrix.mul_diagonal,Matrix.diagonal_mul,h,k]
private lemma gDyad (x y : Site N × SpinIdx) (V : SU.E) : dg (matrix5 x y V)=∑ i∈five, ∑ j∈ five,(matter V).val i j • (put (x,i)*takeF (y,j)) := by
 let f(i j:Single N):= (matrix5 x y V) i j • (put i * takeF j)
 change ∑ i,∑ j, f i j=_
 have hp (a : Site N × SpinIdx) (i : SU.Slot) : ∑ t : Single N, f (a,i) t= ∑ j:SU.Slot, f (a,i) (y,j):=by
    rw [show (∑ t : Single N, f (a,i) t)=_ from Fintype.sum_prod_type (fun k : (Site N × SpinIdx) × SU.Slot=> f (a,i) k), sum_eq_single y]
    all_goals simp_all [f,matrix5]
 rw [show (∑ i,∑ j,f i j)=_ from Fintype.sum_prod_type (fun k : (Site N × SpinIdx) × SU.Slot=> ∑ j, f k j)]; simp_rw [hp]
 rw [sum_eq_single x]; simp [f,matrix5,five,internal_index, colors, ite_smul, ite_and,sum_filter]; all_goals simp_all [f,matrix5]
lemma dgLead (V:Pane N) : let W:ℂ:= -sing R A.wave*Lifted.winding N A.birth * Lifted.winding N A.death; birthOp A V=W • dg (matrix5 (wrap N A.birth,upSpin A.slot) (wrap N A.death,dnSpin A.slot) (A.laps V)) := by
 intro W; let P:Site N × SpinIdx:=(wrap N A.birth,upSpin A.slot); let Q:Site N×SpinIdx:= (wrap N A.death,dnSpin A.slot)
 rw [gDyad,birthOp]; simp_rw [smul_sum]; refine sum_congr rfl fun i _=> sum_congr rfl fun j _=>?_
 unfold lower upper basisC Fock.remove; rw [map_smul,map_smul,star_smul, create_put,create_put,Lifted.index, Lifted.index, Matrix.smul_mul, Matrix.mul_smul,show star (Lifted.winding N A.death)=_ from fee_real (Rush.periods N _)] -- tune
 let U:=put (P,i); let D:=takeF (Q,j); let c:=A.coil V i j; change _ • (c • (_ • (_ • (D*U))))= _ • (c • (U*D)); rw [show D*U=-(U*D) from (eq_neg_of_add_eq_zero_left ((mixed (Q,j) (P,i)).trans (if_neg ?_)))]; swap
 · intro v; exact dn_half A.slot (by rw [show dnSpin A.slot=upSpin A.slot from congrArg (fun t:Single N=> t.1.2) v]; exact up_half _)
 simp only [smul_smul,smul_neg,W,neg_mul,neg_smul]; congr 2; unfold Lifted.winding; ring -- tune
lemma chant_cov : covariant (A.chant (N:=N)) := by
 intro g u; change A.birthOp (gauge g u.1) = twist _ (A.birthOp _); rw [dgLead,dgLead,twist_scalar,dg_cov,matrix5_law,laps_t,laps_t,travel_gauge,node_of,node_of, ← wrap_stop_cover, A.moves] -- tune .reduce projecting pairs
end Lead
namespace Melody
variable (P:I→Melody B R)(b:Bool)(L:List I)
lemma goal_cont (A: Melody B R) : Continuous (A.goal b (N:=N)):=by unfold goal; apply Continuous.sub; split_ifs; exact (A.first.chant_c).mul A.last.chant_c; exact A.first.chant_c; exact (show Continuous fun _ : Fields N=> compare b • (1:FC (Single N)) from continuous_const)

def festival {N:Side}: Mark N:= fun V=> rollC (fun i=> (P i).goal b V) L
lemma goal_cov (A:Melody B R) : covariant (A.goal b (N:=N)):=by intro g x; unfold goal; split_ifs <;> rw [Pi.sub_apply,Pi.sub_apply,map_sub,Pi.smul_apply, Pi.smul_apply,twist_scalar,show (1:Mark N) x=(1:Op (Finset (Single N))) from rfl,map_one]; rw [Pi.mul_apply,Pi.mul_apply,A.first.chant_cov g x,A.last.chant_cov g x,map_mul]; rfl; rw [A.first.chant_cov g x]; rfl
lemma festival_cont : Continuous (festival P b L (N:=N)):=by induction L with| nil => exact continuous_const| cons i L ih=> exact (goal_cont b _).mul ih
lemma festival_cov : covariant (festival P b L (N:=N)):=by
 intro g x; induction L with| nil=>change (1:Op (Finset (Single N))) = (twist _) 1; rw [map_one]| cons i L ih=> rw [show ∀ v:Fields N,festival P b (i::L) v=(P i).goal b v * festival P b L v from fun i=>rfl]; rw [show festival P b (_::_) x=(P i).goal b x * festival P b L x from rfl, map_mul]; exact congrArg₂ (·*·) ((goal_cov b _) _ _) ih

lemma festival_norm (u:Fields N) : ‖festival P b L u‖ ≤ (cuts R 0)^L.length := by
 induction L with
 | nil=> exact (norm_one (α:=FC _)).trans_le (pow_zero _).ge -- tune
 | cons i L ih=>
   refine (norm_mul_le ..).trans ?_ -- doesn't unfold festival
   have hv:Billow 0 (0:Op (Single N)):=outlet _ (norm_zero.le)
   have ht:‖(P i).goal b u‖ ≤ cuts R 0:= by rw [← (P i).gol_v]; exact note_n (P i) _ _ hv le_rfl
   exact (mul_le_mul ht ih (norm_nonneg _) ((norm_nonneg _).trans ht)).trans_eq (pow_succ' ..).symm
end Melody
end YM.CF.Buffered.Ballad
