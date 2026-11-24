import YM.SU5.LoomForce.AppointmentBooks

/-! # Move actual appointments and stamps. Negative-time & reflection products. Do not commute
across data of both positive-time readings in paying a regulator price; keep the
same tests. All proof on chosen b=01 & (00) Polar at both sectors, not claiming
full orientation grants of the regulator's P.E at this budget. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 320000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.LoomForce.Palette
open Function Filter Metric Fock Finset Lat Lattice Next.Free Cube Tulip Scroll Spire Pastry RP Branch
  Wilson Phase SU Rush Mir Reflect Lifted Window Skye Dial Analysis MeasureTheory
open Lamour Lamour.Bridge Celeste Morn Hiro RG Girt
open Py Py.Rate Py.Rate.LocalLimit Preparation Yoke Papal Tapestry Journey
open Ballad EmberWind CF.Pannier.Chancel WakeInvestment Jewel
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology ContDiff Classical

-- rerun calibration at these colours (uses proof of CurrentClan/spin_00).
private lemma spin_00 (j: SpinIdx) : pin 3 j 0=(if j=(2:SpinIdx) then 1 else 0) ∧ pin 3 j 2=(if j=0 then -1 else 0):=by
 fin_cases j
 · simp only [pin,Matrix.mul_apply,SpinIdx,Fin.sum_univ_succ,Fintype.sum_empty] 
   change ((0*(1)+ (0*(0) + (1*(0) + (0*(0) + 0)))) :ℂ)=0 ∧ ((0*(0)+ (0*(0) + (1*(-1) + (0*(0) + 0)))) :ℂ)= -1; norm_num
 · simp only [pin,Matrix.mul_apply,SpinIdx,Fin.sum_univ_succ,Fintype.sum_empty] 
   change ((0*(1)+ (0*(0) + (0*(0) + (1*(0) + 0)))) :ℂ)=0 ∧ ((0*(0)+ (0*(0) + (0*(-1) + (1*(0) + 0)))) :ℂ)=0; norm_num
 · simp only [pin,Matrix.mul_apply,SpinIdx,Fin.sum_univ_succ,Fintype.sum_empty] 
   change ((1*(1)+ (0*(0) + (0*(0) + (0*(0) + 0)))) :ℂ)=1 ∧ ((1*(0)+ (0*(0) + (0*(-1) + (0*(0) + 0)))) :ℂ)=0; norm_num
 · simp only [pin,Matrix.mul_apply,SpinIdx,Fin.sum_univ_succ,Fintype.sum_empty] 
   change ((0*(1)+ (1*(0) + (0*(0) + (0*(0) + 0)))) :ℂ)=0 ∧ ((0*(0)+ (1*(0) + (0*(-1) + (0*(0) + 0)))) :ℂ)=0; norm_num
variable (k:ℤ)(N:Side)(u:Cover)
local notation "P₀" => Prototype.goldF
local notation "T" => plane 3 k
local notation "τ" => (plane 3 k).flee u

lemma crossSlot (p q:SU.Slot) : theta (carR 3 k N) (create (basisC N u 0 p)*Fock.remove (basisC N u 2 q))=
    create (basisC N τ 0 q)*Fock.remove (basisC N τ 2 p):=by
  let f:= basisC N τ 2 p; let g:=basisC N τ 0 q
  rw [theta_mul, (Lifted.flips_basisC 3 k N u 0 p).1,(Lifted.flips_basisC 3 k N u 2 q).2]
  simp_rw [(spin_00 _).1,(spin_00 _).2,ite_smul,zero_smul,sum_ite_eq',mem_univ,ite_true,one_smul,neg_one_smul]
  rw [map_neg]; change (-Complex.I • Fock.remove f)*(Complex.I • -create g)= _
  have h: Fock.remove f * create g= -(create g * Fock.remove f):=SitSpin.cr_swap 0 0 τ τ p q
  rw [smul_neg, mul_neg,Matrix.smul_mul,Matrix.mul_smul,smul_smul,neg_mul,Complex.I_mul_I,neg_neg,one_smul,h, neg_neg]

-- even needs passage on *whole* masks
open Scree
-- `Zena.ping_spot` argument (pay directly without extra imports)
omit N k u in
private lemma ping_carry {n:Side} (R:Gauge) (s:Signed) (c:Site n)(A:Support n)(e:ℝ)(V:Config R n): pingS e A (pull s c V)↔pingS e (A.image (affine s c)) V:=by
  let f:= Face.send s c; have hf: Function.Surjective f:= Finite.surjective_of_injective (Face.injective_send s c)
  let Y:= A.image (affine s c); have hu(i:Lattice.Face (Per n)): Disjoint A (touched i)↔ Disjoint Y (touched (f i)):=by unfold Y f; rw [Work.H03.touched_send]; exact (disjoint_image (fun {_} {_} e=> s.act_injective (add_right_cancel e))).symm
  have he(i:Lattice.Face (Per n)): R.chord (faceValue (pull s c V) i)= R.chord (faceValue V (f i)):= Face.send_price _ _ _ _ _ R.chord_inv fun i j=> R.chord_conj j i
  constructor; · intro q i v; obtain ⟨j,rfl⟩:=hf i; rw [← he]; exact q _ fun i=>v ((hu j).mp i)
  intro p i t; rw [he]; exact p (f i) fun w=> t ((hu i).mpr w)
local notation "Z_" u:max => (wrap (More N) u)
private lemma affine_shift : affine (Signed.mirror 3) (Z_ (2 • (k • step 3))) (Z_ (nodeC u))= Z_ (nodeC τ):=by
  change (T).anon N (Z_ (nodeC u))= _
  rw [(T).anno]; exact congrArg (wrap _) ((T).mote _)
lemma pearl_place (ρ t:ℝ) (r:ℕ) (U: Fields N) : (staffAt u).pearl ρ N r t (reflFields 3 k U).1=
    (staffAt τ).pearl ρ N r t U.1:=by
  let f:= U.1; let g:= fling 3 k N f; let m:= Signed.mirror 3; let o:=Z_ (2 • (k • step 3)); let ℓ:= Z_ (nodeC u); let w:=Z_ (nodeC τ)
  have hf:g=pull m o f:=rfl
  have hu: pingS t (Lattice.halo r {ℓ}) g ↔ pingS t (Lattice.halo r {w}) f:=by
    rw [hf,ping_carry,← CF.Tye.dignify,image_singleton, show affine m o ℓ=w from affine_shift ..]
  have he: faceValue g (ℓ,P₀) = faceValue f (w,P₀):=by rw [faceValue, hf, travel_pull, show List.map _ _=square 0 1 from rfl]; exact congrArg (fun i:Seat N=> travel f i (square 0 1)) (affine_shift ..)
  unfold Staff.pearl
  rw [show pingS t ((staffAt u).gateS r N) (reflFields 3 k U).1 ↔ pingS t ((staffAt τ).gateS r N) U.1 from hu]
  split_ifs with p
  · exact congrArg (fun y=> (SU.group.adjoint 1 (ρ • SU.group.curvature y))) he
  rfl

lemma balanceSpear (U:Staff)(ρ t:ℝ)(r:ℕ) (x:Fields N):
    U.rungWeave ρ r t N x =
    ∑ b:SU.Slot, ∑ c:SU.Slot, walkC (U.pearl ρ N r t x.1) b c •
        (create (basisC N U.u (upSpin U.spin.1) b) * Fock.remove (basisC N U.u (dnSpin U.spin.2) c)):=by
  rw [Staff.spear,walk_price]; rfl
lemma flowingStencil (ρ t:ℝ)(r:ℕ) : fluent 3 k ((staffAt u).rungWeave ρ r t) = (staffAt τ).rungWeave ρ r t := by
  funext N X
  let g:= staffAt u; let y:= staffAt τ; let F:= reflFields 3 k X; change theta _ (g.rungWeave _ _ _ N F)=_
  change theta _ ((staffAt u).rungWeave _ _ _ N (reflFields 3 k X))=(staffAt τ).rungWeave ρ r t N X; rw [balanceSpear,balanceSpear]; simp_rw [pearl_place,theta_sum,theta_smul]; rw [Finset.sum_comm]; refine sum_congr rfl (fun i _=> sum_congr rfl fun j _=> ?_)
  refine congrArg₂ (· • ·) ?_ (crossSlot k N u j i); let A:=walkC (y.pearl ρ N r t X.1)
  exact congrFun (congrFun (walk_star ..) i) j
lemma gate_roll (P:Spine) (A:ℝ)(s r:ℕ)(t : Sewer)(β:ℕ→ℝ) : fluent 3 k (stitch P A s β (staffAt u) r t)=
    stitch P A s β (staffAt τ) r t := by
  cases t with
  | none=>
    rw [stitch_yes,stitch_yes]; let a:= ampl P s A
    have he : star a=a:=by simp [a,ampl]
    funext N X; change theta _ (a • _) = a • _; rw [theta_smul,he]; exact congrArg ((a) • ·) (congrFun (congrFun (flowingStencil k u ..) N) X)
  | some z=> rw [stitch_tone, stitch_tone]; funext N; exact Yoke.pill_theta .. -- order

variable {I:Type*}(P:Spine)(A:ℝ)(tag:I→ Sewer)(u:I→ Cover)
def blockVisit (P:Spine)(tag:I→ Sewer)(A:ℝ)(s:ℕ)(β:ℕ→ℝ)(r:ℕ)(u:I→ Cover)(L:List I) :=
    carpet P tag A (fun _ => P₀) (fun _=> pairMood) β r L u s
-- for reindexing sums
lemma block_cons (s:ℕ)(β:ℕ→ℝ)(r:ℕ)(i:I)(L:List I) : blockVisit P tag A s β r u (i::L)=
    stitch P A s β (staffAt (u i)) r (tag i) * blockVisit P tag A s β r u L := rfl
lemma block_flown (s:ℕ)(β:ℕ→ℝ)(r:ℕ)(L:List I) :
    fluent 3 k (blockVisit P tag A s β r u L)= blockVisit P tag A s β r (fun x=> (plane 3 k).flee (u x)) L := by
  induction L with
  | nil=> exact funext (fun i=> funext fun _=>theta_one _)
  | cons i L ih=> rw [block_cons, Yoke.Shuttle.vocal_two, gate_roll, ih]; rfl
#print axioms pearl_place
#print axioms flowingStencil
#print axioms block_flown
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.LoomForce.Palette
