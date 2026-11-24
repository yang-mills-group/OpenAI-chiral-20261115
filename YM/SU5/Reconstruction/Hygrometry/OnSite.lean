import YM.SU5.Reconstruction.Hygrometry.Flourish
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 30000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Hygrometry
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Tulip Phase
open Laurent Next.Free Bloch Fir Ember Jill Kea Sods Flare Emu Onyx Dial
open Filter Topology
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open YM.CF.Buffered YM.CF.Window
open YM.Stationary (Gaia)
/-! Authentic Gauge-Singlet Fock bilinear leg costs for occupation. Any Wing, spin-labeled, onsite cases. -/
open Mir Reflect Buffered.Lifted Buffered.Afterglow.Tower.Tilted
open PriceCliff
variable {N:Side} (x:Window.Family)(i k:Fin 2)
namespace Locomotive
noncomputable abbrev payRoll (N:Side)(U:Cover)(r:ℝ): Mark N:= (-((star (Emu.gain r)*Emu.gain r):ℂ)) • toMark (Window.current N x (wrap N U) (upSpin i) (dnSpin k))
abbrev boundTag (V:↥(Window.colors x)) (r:Bool) : Personality := if r then Personality.pureV true V.val (dnSpin k) (mem_compl.mpr (Window.dn_half k)) else Personality.pureV false V.val (upSpin i) (up_half i) -- Track signs
-- x.consistency with explicit names. `Bool true` surname*M.
def selfT {α:Type*}(s:α):List (α×Bool):= [(s,false),(s,true)]
lemma duo_price (V:Fields N) {U:Cover}(r:ℝ) (q:↥(Window.colors x)) : literal (fun _:↥(Window.colors x)×Bool=> U) (uncurry (boundTag x i k)) N r (selfT q) = (- (star (Emu.gain r)* Emu.gain r)) • (put ((wrap N U,upSpin i),q.val)*takeF ((wrap N U,dnSpin k),q.val)):= by
 unfold literal rollC; simp only [selfT,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil, mul_one]; let a:=pitch N U r q.val; change create (a (basisKet (upSpin i))) *remove (-(a (basisKet (dnSpin k)))) =_; unfold a pitch; rw [canto, canto]; simp only [basisC,map_smul,create_put,remove,star_smul,map_neg,star_neg]; simp only [mul_neg,Matrix.smul_mul, Matrix.mul_smul, smul_smul]; let f:=Emu.gain r; let u:=winding N U; change -((star f * star u*(f*u)) • _) = _; rw [neg_smul]; congr 2; have hp:=Rush.fee_one (Rush.periods N U); have ht:star u=u:=Rush.fee_real _; rw [ht]; change u*u=1 at hp; linear_combination (f*star f)*hp -- check formula donne
lemma spent (V:Fields N) (U:Cover) (r:ℝ) : payRoll x i k N U r V=utter (fun _:↥(Window.colors x)×Bool=> U) (uncurry (boundTag x i k)) N r selfT (fun _=>1) := by
 unfold utter payRoll; change (-((star (Emu.gain r)*Emu.gain r):ℂ)) • Window.current _ _ _ _ _ V.1= _; rw [current_words]; simp_rw [duo_price x i k V,one_smul, Finset.smul_sum]; exact (show _=_ from (Finset.sum_coe_sort ..).symm) -- name
lemma used (U:Cover) (r:ℝ): AtSupport false {wrap (More N) (nodeC U)} (payRoll x i k N U r) ∧ covariant (payRoll x i k N U r) ∧ Continuous (payRoll x i k N U r):= by
 let f:= current N x (wrap N U) (upSpin i) (dnSpin k); obtain ⟨cf,p,q,t⟩:= current_local (N:=N) x (wrap N U) _ _ (up_half i) (dn_half k); let v:=wrap (More N) (nodeC U)
 have he: AtSupport false {v} (toMark f):=by
    have hy : RG.Envelope f:= by refine ⟨cf.measurable,?_⟩; obtain ⟨w,d⟩:= (isCompact_range (f:=fun x=>‖f x‖) cf.norm).bddAbove; exact ⟨w,fun x=>d (Set.mem_range_self x)⟩
    apply AtSupport.fromEval _ hy (fun _ _ _=> rfl); intro V; apply fine_enlarge _ (q V); intro k e; rw [mem_matterSet] at e; simp [modesIn]; rw [mem_singleton] at e; rw [mem_matterSet,e]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_singleton.mpr (node_of ..)⟩ -- tune
 refine ⟨he.smulM _,fun g w=>?_,?_⟩
 · rw [payRoll, Pi.smul_apply,Pi.smul_apply, twist_scalar]; exact congrArg (fun t:FC (Single N)=> _ • t) (t g _)
 apply Continuous.smul continuous_const; exact cf.comp continuous_fst
end Locomotive
end YM.CF.Hygrometry
