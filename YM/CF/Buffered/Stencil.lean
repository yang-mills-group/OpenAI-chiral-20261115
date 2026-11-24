import YM.CF.Buffered.Aliases
import YM.CF.Peaks.Mantle
import YM.CF.Cubes.Flag

/-! # From Fourier support to an actual stencil on link and matter arguments -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Buffered.Stencil
open Function Fock Filter NormedSpace Lat Lattice Branch Finset Laurent Bloch Next.Free Fir Rush Scroll Peaks Cube Tenant Tulip
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Kronecker
attribute [local instance] opCStarAlgebra
variable {N P : Side}

lemma remaining_length (w : Walk) (x y : Site N) (h : y∈visits x w) :
    separation (stop x w) y ≤ w.length := by
  induction w generalizing x with
  | nil => simp [stop,(show y=x from by simpa [visits] using h)]
  | cons s w ih=>
    rcases List.mem_cons.mp h with rfl|p
    · rw [separation_comm]; exact leakspan ..
    exact (ih (x+s.vec) p).trans (Nat.le_add_right ..)
private lemma size_box (R : ℕ) (x : Cover) (h : Laurent.size x ≤ R) : x∈box R := by
  have he (i : Axis) : (x i).natAbs ≤ R := (Finset.single_le_sum (f:=fun j:Axis=> (x j).natAbs) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)).trans h
  rw [box_test]; constructor <;> intro i <;> have ht := he i <;> omega

def LabelSet (R : ℕ) := (Lattice.box R).filter (fun x => Laurent.size x ≤ R)
lemma labels (R : ℕ) (x : Cover) : x ∈ LabelSet R ↔ Laurent.size x ≤ R := by
  unfold LabelSet; rw [mem_filter]; exact ⟨And.right, fun h => ⟨size_box _ _ h,h⟩⟩

variable (G : Ratio N P) (j : ℕ)
local notation "T" => St G.count
local notation "I" => Iota G
local notation "U" => tub (brix j G.count)
local notation "D" => drag G true false
local notation "V" => mosaic G true false (tub (brix j G.count))

def LaurentRadius (j : ℕ) (L : Side) (R : ℕ) := ∀ x : Cover, R < Laurent.size x → tub (brix j L) x = 0
def clothRadius (L : Side) (R : ℕ) := 16 * L.val + 8*L.val*R
variable {R : ℕ} (h : LaurentRadius j G.count R)
lemma drag_entry (M : Nom N P) (o : Lattice.Order) (r t : T) (i : I) (k : I) (x : Cover) :
    D r t x (U x r t) o (unionP M) i k =
      if i.1.2 = r ∧ k.1=(i.1.1+wrap N x,t) then
        Rush.wind i.1.1 x * (U x r t) *
          (SU.matter (travel M.1 (touch G true (i.1.1,r)) (runD true false G.count r t x o))).val i.2 k.2
      else 0 := by
  unfold drag; rw [Matrix.sum_apply, sum_eq_single i.1.1]; swap
  · intro a _ e; simp only [panel,Matrix.of_apply]; rw [if_neg ?_]; exact fun p=> e (congrArg Prod.fst p.1).symm
  swap; · simp
  unfold unionP; dsimp only; rw [track_pr]; simp only [panel,Matrix.of_apply,Matrix.smul_apply,smul_eq_mul]; apply ite_congr
  ·  apply propext; exact and_congr_left fun _=> ⟨fun h=> congrArg Prod.snd h, fun h=> by rw [←h]⟩
  · intro; rfl
  intro; rfl
include h
lemma douse_sum (x : Coil N P) (o : Lattice.Order) : douse G true false U o x =
    ∑ r : T,∑ t:T,∑ k∈ LabelSet R, D r t k (U k r t) o x := by
  refine sum_congr rfl fun r _ => sum_congr rfl fun t _ => ?_
  rw [names.tsum_eq (f:=fun k:Cover=> D r t k (U k r t) o x)]
  apply tsum_eq_sum; intro b g; rw [show U b=0 from h b (lt_of_not_ge (fun v=> g ((labels ..).mpr v))),drag]; simp [panel, ← Matrix.ext_iff]
lemma mosaic_entry (x : Coil N P) (i k : I) : V x i k =
    ((Fintype.card Lattice.Order:ℝ)⁻¹) • ∑ o:Lattice.Order,∑ r:T,∑ t:T,∑ z∈ LabelSet R,
      D r t z (U z r t) o x i k := by
  unfold mosaic; rw [Matrix.smul_apply,Matrix.sum_apply]; simp_rw [douse_sum G j h,Matrix.sum_apply]
lemma mosaic_cont : Continuous (fun x => V (unionP x)) := by
  apply continuous_matrix; intro i k; simp_rw [mosaic_entry G j h,drag_entry]
  refine Continuous.smul (f:=fun _=> (Fintype.card Lattice.Order:ℝ)⁻¹) continuous_const ?_; refine continuous_finsetSum _ fun o _=> continuous_finsetSum _ fun r _=> continuous_finsetSum _ fun t _=> continuous_finsetSum _ fun x _=> ?_
  split; swap; exact continuous_const
  exact continuous_const.mul ((SU.matter_cont.comp ((travel_cont ..).comp continuous_fst)).matrix_elem _ _)
theorem cloth_cont (M : Male) : Continuous (fun x => Peaks.cloth j M G (unionP x)) := by
  have he := mosaic_cont G j h
  exact ((continuous_const.mul he).mul continuous_const).add ((continuous_const.mul he).mul continuous_const)
omit h
lemma cloth_entry (M : Male) (x : Coil N P) (i k : I): Peaks.cloth j M G x i k=
    (lobe G true i i * (V x i k) * lobe G true k k) +
    (lobe G false i i * (V x i k) * lobe G false k k) := by
  have he(b): (lobe G b * V x * lobe G b) i k = _ := calc
    _ = (Matrix.diagonal (fun i => lobe G b i i) * V x * Matrix.diagonal (fun k=> lobe G b k k)) i k:= by
      exact congrArg (fun (M:Op I)=> (M*V x*M) i k) (lobe_diag G b)
    _ = _ := by rw [Matrix.mul_diagonal,Matrix.diagonal_mul]
  unfold Peaks.cloth; rw [Matrix.add_apply,he,he]
include h
local notation "ψ" => clothRadius G.count R
-- Column k: from projected gauge vertex of its block. Only needs the first Nom argument (fine field).
theorem cloth_support (p : Odd G.count.val) (M : Male) (i k : I) (x : Nom N P)
    (hy : ψ < separation (Peaks.touch G false k.1) (Peaks.touch G true i.1)) : Peaks.cloth j M G (unionP x) i k = 0 := by
  have he(o r t z)(hz : z∈LabelSet R):
      D r t z (U z r t) o (unionP x) i k= 0 := by
    rw [drag_entry]; split; swap; rfl
    next u =>
      have hx:i.1=(i.1.1,r) := by rw [←u.1]
      let Z:= runD true false G.count r t z o
      have hw:= leakspan (a:=touch G true (i.1.1,r)) Z
      unfold Z at hw; rw [worn G true false p,←u.2,←hx] at hw
      rw [separation_comm] at hw
      exact (hy.not_ge (hw.trans ((run_len ..).trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ ((labels ..).1 hz)) _)))).elim
  rw [cloth_entry,mosaic_entry G j h]; simp_rw [sum_eq_zero fun z u=> he _ _ _ z u]; simp

theorem cloth_local (p : Odd G.count.val) (M : Male) (i k : I)
    (x y : Nom N P) (e : Agrees (halo ψ {touch G false k.1}) x.1 y.1) :
    Peaks.cloth j M G (unionP x) i k=Peaks.cloth j M G (unionP y) i k := by
  suffices he : V (unionP x) i k=V (unionP y) i k by rw [cloth_entry,cloth_entry,he]
  rw [mosaic_entry G j h,mosaic_entry G j h]; apply congrArg
  refine sum_congr rfl fun o _=> sum_congr rfl fun r _=> sum_congr rfl fun t _=> sum_congr rfl fun z pz=> ?_
  rw [drag_entry, drag_entry]; split; swap; rfl
  next u =>
    let Z:=runD true false G.count r t z o
    have hv(v : Site (More P))(h:v∈visits (touch G true (i.1.1,r)) Z): v∈ halo ψ {touch G false k.1} := by
      have he:= remaining_length Z _ _ h
      refine halo_spec.mpr ⟨_,mem_singleton_self _,?_⟩
      unfold Z at he; rw [worn G true false p, ← u.2] at he
      exact he.trans ((run_len ..).trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ ((labels ..).1 pz)) _))
    exact congrArg (fun v : SU.E => (Rush.wind i.1.1 z * (U z r t)) * (SU.matter v).val i.2 k.2) (travel_local _ Z x.1 y.1 (fun i h₁ h₂=>e i (hv _ h₁) (hv _ h₂)))

end YM.CF.Buffered.Stencil
