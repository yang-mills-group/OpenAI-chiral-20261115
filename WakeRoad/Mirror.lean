import WakeRoad.Dinner
/-! # Theta on actual mixed test. -/
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 250000
noncomputable section
namespace YM.CF.Buffered.EmberWind
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric Mir
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Precision Tree Push.SectorMeasure Fock
attribute [local instance] opCStarAlgebra
open Ballad Hiro
open Py.Rate.LocalLimit.Papal
open Py.Rate.LocalLimit.Preparation.Yoke.Shuttle
variable {N:Side}
lemma ping_move {S:Support (More N)}(α:Signed)(z:Seat N)(U:Pane N)(t:ℝ):
    pingS t S (Lattice.pull α z U) ↔ pingS t (S.image (affine α z)) U := by
 let m:= affine α z
 have hi:Injective m:=by
    intro i j h; apply (α.actEquiv (R:=Per (More N))).injective; exact add_right_cancel h
 have h(i:Face (Per (More N))): SU.group.chord (faceValue (Lattice.pull α z U) i)=SU.group.chord (faceValue U (Face.send α z i)):=Face.send_price U i α z _ SU.group.chord_inv (fun _ u => SU.group.chord_conj u _)
 have hp(i:Face (Per (More N))): Disjoint (S.image m) (touched (Face.send α z i)) ↔ Disjoint S (touched i):= by
    let f:Seat N ↪ Seat N:=⟨m,hi⟩
    rw [Work.H03.touched_send]; change Disjoint (S.image (f:Seat N → Seat N)) ((touched i).image f) ↔ Disjoint _ _
    rw [← Finset.map_eq_image,← Finset.map_eq_image,Finset.disjoint_map]
 constructor
 · intro e i g; obtain ⟨y,rfl⟩:= Finite.injective_iff_surjective.mp (Face.injective_send α z) i
   exact (h y).symm.trans_lt (e y (mt (hp y).mpr g))
 intro e i g; exact (h i).trans_lt (e _ (mt (hp i).mp g))

open Afterglow.Tower.VacuumSelection.GramSignal
local notation "m3"=> Signed.mirror 3
local notation "z3" z:max N:max=> wrap (More N) (2 • (z • step (3:Axis)))
local notation "s3" z:max=>plane 3 z
lemma node_aff (z:ℤ)(u:Cover):affine m3 (z3 z N) (wrap (More N) (nodeC u))=wrap (More N) (nodeC ((s3 z).flee u)):=by
 let T:=plane 3 z
 change T.anon N _=_; rw [T.anno,nodeC,T.mote]; rfl
lemma ping_spin (z:ℤ)(u:Cover)(r:ℕ)(t:ℝ)(U:Pane N): pingS t (halo r {wrap (More N) (nodeC u)}) (fling 3 z N U) ↔ pingS t (halo r {wrap (More N) (nodeC ((s3 z).flee u))}) U:=by
 rw [fling_eq,ping_move,← Tye.dignify,image_singleton,node_aff z u]
lemma sqlink (f:PlaqAxes) (h:f.val.1≠(3:Axis))(p:f.val.2≠(3:Axis)): (square f.val.1 f.val.2).map (fun i=> i.rotate m3)=square f.val.1 f.val.2:=by
 simp [Signed.mirror,Step.rotate,square,posDir,negDir,Ne.symm h,Ne.symm p]
lemma gamma3 (j: SpinIdx) : pin 3 j 0=(if j=(2:SpinIdx) then 1 else 0) ∧ pin 3 j 2=(if j=0 then -1 else 0):=by
 fin_cases j
 · simp only [pin,Matrix.mul_apply,SpinIdx,Fin.sum_univ_succ,Fintype.sum_empty] 
   change ((0*(1)+ (0*(0) + (1*(0) + (0*(0) + 0)))) :ℂ)=0 ∧ ((0*(0)+ (0*(0) + (1*(-1) + (0*(0) + 0)))) :ℂ)= -1; norm_num
 · simp only [pin,Matrix.mul_apply,SpinIdx,Fin.sum_univ_succ,Fintype.sum_empty] 
   change ((0*(1)+ (0*(0) + (0*(0) + (1*(0) + 0)))) :ℂ)=0 ∧ ((0*(0)+ (0*(0) + (0*(-1) + (1*(0) + 0)))) :ℂ)=0; norm_num
 · simp only [pin,Matrix.mul_apply,SpinIdx,Fin.sum_univ_succ,Fintype.sum_empty] 
   change ((1*(1)+ (0*(0) + (0*(0) + (0*(0) + 0)))) :ℂ)=1 ∧ ((1*(0)+ (0*(0) + (0*(-1) + (0*(0) + 0)))) :ℂ)=0; norm_num
 · simp only [pin,Matrix.mul_apply,SpinIdx,Fin.sum_univ_succ,Fintype.sum_empty] 
   change ((0*(1)+ (1*(0) + (0*(0) + (0*(0) + 0)))) :ℂ)=0 ∧ ((0*(0)+ (1*(0) + (0*(-1) + (0*(0) + 0)))) :ℂ)=0; norm_num
private lemma theta3_s (z:ℤ)(u:Cover)(b c: SU.Slot): theta (carR 3 z N) (create (basisC N u 0 b)*remove (basisC N u 2 c))=
    (create (basisC N ((s3 z).flee u) 0 c)*remove (basisC N ((s3 z).flee u) 2 b)):=by
 rw [theta_mul, (Lifted.flips_basisC 3 z N u 0 b).1,(Lifted.flips_basisC 3 z N u 2 c).2]
 simp_rw [(gamma3 _).1,(gamma3 _).2,ite_smul,zero_smul,sum_ite_eq',mem_univ,ite_true,one_smul,neg_one_smul]; rw [map_neg]
 let v:= (s3 z).flee u; let f:=basisC N v 2 b; let g:=basisC N v 0 c; change (-Complex.I • Fock.remove f)*(Complex.I • -create g)= _
 have h: Fock.remove f * create g= -(create g * Fock.remove f):=SitSpin.cr_swap 0 0 v v b c
 rw [smul_neg, mul_neg,Matrix.smul_mul,Matrix.mul_smul,smul_smul,neg_mul,Complex.I_mul_I,neg_neg,one_smul,h, neg_neg]

private lemma pearl3 (u:Cover)(f:PlaqAxes)(h:f.val.1≠3)(p:f.val.2≠3)(ρ:ℝ)(r:ℕ)(t:ℝ)(U:Pane N)(z:ℤ):
    Staff.pearl (localStaff u 0 f) ρ N r t (fling 3 z N U)=Staff.pearl (localStaff ((s3 z).flee u) 0 f) ρ N r t U:=by
 unfold Staff.pearl
 change (if pingS t (halo r {wrap (More N) (nodeC u)}) (fling 3 z N U) then _ else _)=(if pingS t (halo r {wrap (More N) (nodeC _)}) U then _ else _)
 rw [ping_spin]; unfold Staff.edgeBudget
 let v:=wrap (More N); change (if _ then SU.group.adjoint (travel _ _ []) (ρ • SU.group.curvature (faceValue _ (v _,f))) else _)=(if _ then SU.group.adjoint (travel _ _ []) (ρ • SU.group.curvature (faceValue _ (v _,f))) else _)
 simp only [travel,faceValue,fling_eq,travel_pull,sqlink f h p, v,localStaff,node_aff z u]

lemma local3 (u:Cover)(f:PlaqAxes)(h:f.val.1≠3)(p:f.val.2≠3)(ρ:ℝ)(r:ℕ)(t:ℝ)(z:ℤ):
    reflMark 3 z (Staff.rungWeave (localStaff u 0 f) ρ r t N)=Staff.rungWeave (localStaff ((s3 z).flee u) 0 f) ρ r t N:=by
 funext X
 let v:= (s3 z).flee u; let A:= localStaff u 0 f; let B:=localStaff v 0 f
 unfold reflMark; rw [Staff.spear,Staff.spear,theta_sum]
 erw [pearl3 u f h p ρ r t X.1 z] -- reflFields projects to fling
 let α:=B.pearl ρ N r t X.1
 change _ = ∑ b:SU.Slot,∑ c:SU.Slot, (walkC α) b c • (create (basisC N v 0 b)*Fock.remove (basisC N v 2 c))
 rw [sum_comm]
 refine sum_congr rfl fun b _=> ?_; rw [theta_sum]; refine sum_congr rfl fun c _=> ?_; rw [theta_smul]
 change star ((walkC α) b c) • theta (carR 3 z N) (create (basisC N u 0 b)*Fock.remove (basisC N u 2 c))= _
 rw [theta3_s]; exact congrArg (fun a:ℂ=> a • (create (basisC N v 0 c)*Fock.remove (basisC N v 2 b))) (Matrix.ext_iff.mpr (walk_star α) c b)
#print axioms local3
end YM.CF.Buffered.EmberWind
