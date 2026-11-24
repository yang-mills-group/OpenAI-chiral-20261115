import YM.CF.Buffered.Borel
import YM.CF.Continuum.CoherentSeams
import YM.CF.Nacre.Mary
import YM.Push.LOCAL_SPLITTING.Orientation

/-!
# Use FiniteGaugeData's antilinear Fock reflection with a specified physical plane

Here s denotes the **gauge-coordinate** plane. Note `Shape`'s translation t
counts *two* gauge steps. No choice of a reduced rep of s in the torus:
`prepU` uses the cover, important for tracking CAR signs. It has precisely the
site reflection, multiplied by its sign (`payA`, `vibes`) of crossing any
cut, and here by `pinLift` = γᵢ γ₅ (Mir.pin). Gauge uses native spacing and
`pull`. Also reflect a Loom *output* field argument as a gauge field; not its
tag.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Buffered
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Kronecker
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset Reflect
open RP RG Scroll Spire Push.SectorMeasure Nacre Window Tulip Skye
attribute [local instance] opCStarAlgebra
variable {m B n : Side}
def plane (i : Axis) (s : ℤ) : Shape := ⟨Signed.mirror i, s • step i⟩
def fling (i : Axis) (s : ℤ) (n : Side) := Yg (n := n) (plane i s)
def carR (i : Axis) (s : ℤ) (n : Side) := prepU (plane i s) (pinLift i) inert n

-- native reflection, link and CAR factors together on the same field
def refl (i : Axis) (s : ℤ) (F : Window.Evaluation n) := fun y => theta (carR i s n) (F (fling i s n y))

variable (i : Axis) (s : ℤ)
lemma mirror_axial (k : ℤ) : (Signed.mirror i).act (k • step i : Cover) = -(k • step i) := by
  funext j; by_cases e : i=j <;> simp_all [Signed.mirror, Signed.act, eq_comm (a:=j) (b:=i)]
lemma gaugeSquare : joinX (plane i s) (plane i s) = incX 1 := by
  unfold joinX plane incX; dsimp only
  rw [mirror_axial, neg_add_cancel]; congr 1
  nth_rw 1 [← Signed.mirror_inv i]; exact inv_mul_cancel _
lemma fling_eq : fling i s n = pull (Signed.mirror i) (wrap _ (2 • (s • step i))) := rfl
lemma fling_invol : Involutive (fling i s n) := fun x => by
  unfold fling; rw [← kor, gaugeSquare, Nacre.blank]
lemma fling_cont : Continuous (fling i s n) := Wilson.continuous_pull ..
lemma fling_mp (n : Side): MeasurePreserving (fling i s n) (Wilson.prior SU.group (More n)) (Wilson.prior SU.group (More n)) :=
  Wilson.prior_pull ..
lemma fling_there (x : Seat n) : (plane i s).anon n ((plane i s).anon n x)=x := by
  have he a b : Shape.anon (joinX a b) n x=a.anon n (b.anon n x) := by
    rw [←Rush.nat_true x, Shape.anno,palm,← Shape.anno,← Shape.anno]
  rw [← he, gaugeSquare]; simp [incX,Shape.anon,affine]
lemma fling_image (T : Support (More n)) : (T.image ((plane i s).anon n)).image ((plane i s).anon n)=T := by
  rw [image_image,show (plane i s).anon n ∘ (plane i s).anon n=id from funext (fling_there i s), image_id]
lemma Yg_agrees (S : Support (More n)) (p : Shape) {x y : Pane n} (h : Agrees (S.image (p.anon n)) x y) :
    Agrees S (Yg p x) (Yg p y) := Push.Local.agrees_pull (s:=p.s) (b:=wrap _ (2 • p.t)) h
lemma fling_local (S : Support (More n)) {x y : Pane n} (h : Agrees (S.image ((plane i s).anon n)) x y) :
    Agrees S (fling i s n x) (fling i s n y) := Yg_agrees _ _ h
lemma fling_move (j) (x : Cover) : (plane i s).motion x j = if i=j then -x j + 2*s else x j := by
  by_cases e : i=j <;> simp_all [plane, Signed.mirror, Signed.act, Shape.motion, eq_comm (a:=j) (b:=i)] -- includes zsmul step
lemma matter_invol (x : Site n) : (plane i s).mills n ((plane i s).mills n x)=x := by
  apply Tenant.needle; rw [Shape.nodex,Shape.nodex,fling_there]
lemma plane_broad {f : Side} (G : Ratio n f) : Shape.broad G (plane i s)=plane i (G.count.val * s) := by
  unfold Shape.broad plane; rw [mul_smul]; simp
lemma prep_one (n : Side) : prepU (incX 1) 1 inert n=1 := by
  have he := kio n (lagX 0) (lagX 0) 1 1; rw [trips,zero_add,mul_one] at he
  exact mul_left_cancel (b:=_) (show prepU (incX 1) 1 inert n * _= _ * (1 : UNI _) from he.trans (mul_one _).symm)
lemma carR_square : (carR i s n).val * (carR i s n).val= -1 := by
  let U := carR i s n; have h : U*U= _ := kio n (plane i s) (plane i s) (pinLift i) (pinLift i); rw [gaugeSquare] at h
  have he : (pinLift i * pinLift i).val=(-1:ℂ) • (1 : UNI SpinIdx).val := by rw [neg_one_smul]; exact pin_square i
  change (U*U).val= _; rw [h,Ygs (incX 1) _ 1 he, prep_one,neg_one_smul]; rfl

-- translate by z in MATTER-coordinates. For s even, translate to origin.
lemma plane_join_lag (z : ℤ) : joinX (plane i (2*z)) (lagX (z • step i)) = joinX (lagX (z • step i)) (plane i 0) := by
  simp only [joinX,plane,lagX, zero_smul, Signed.act_one, zero_add,mul_one,one_mul,mirror_axial,mul_smul,two_smul]; abel
lemma carR_shift (z : ℤ) (n : Side) :
    prepU (lagX (z • step i)) 1 inert n * carR i (2*z) n = carR i 0 n * prepU (lagX (z • step i)) 1 inert n := by
  unfold carR; rw [kio,kio, plane_join_lag, one_mul,mul_one]
lemma fling_shift (z : ℤ) (n : Side) (y) :
    Yg (lagX (z • step i)) (fling i (2*z) n y) = fling i 0 n (Yg (lagX (z • step i)) y) := by
  unfold fling; rw [←kor,←kor,plane_join_lag]
lemma plane_zero : plane i 0=Window.shape i := by rw [plane,zero_smul,shape]
lemma carR_zero : carR i 0 (CSide m B)= fullTurn m B i := by rw [carR,plane_zero]; rfl
lemma fling_zero : fling i 0 (CSide m B)= mirrorPane m B i := by rw [fling_eq, zero_smul,smul_zero,map_zero,mirrorPane_eq]

-- Fock support relative to a gauge region
variable (n : Side)
def sitesIn (S : Support (More n)) : Finset (Site n) := univ.filter fun x => node x ∈ S
def modesIn (S : Support (More n)) := Window.matterSet n (sitesIn n S)
variable {n}
@[simp] lemma sites_at (S : Support (More n)) (x) : x∈ sitesIn n S ↔ node x ∈ S := by simp [sitesIn]
@[simp] lemma modes_at (S : Support (More n)) (x : Single n) : x∈ modesIn n S ↔ node x.1.1∈ S := by
  rw [modesIn, mem_matterSet, sites_at]
lemma modes_monotone : Monotone (modesIn n) := by intro S T h x; simp only [modes_at]; exact fun k=> h k
lemma modes_univ (n : Side) : modesIn n univ= univ := by ext; simp
lemma prep_moves (p : Shape) (U : UNI SpinIdx) (G H : Support (More n))
    (e : ∀ x, x∈ H ↔ p.anon n x ∈ G) : twist (prepU p U inert n) (cutM (modesIn n G))= cutM (modesIn n H) := by
  -- same sparse jump argument as in Continuum/MirrorGrid
  apply Mir.twist_comm
  ext ⟨⟨x,i⟩,j⟩ ⟨⟨y,k⟩,l⟩
  simp only [cutM, Matrix.mul_diagonal, Matrix.diagonal_mul, modes_at]
  change jump (Tofu p n) (fun v=>(milU p U inert v).val) (x,i,j) (y,k,l)*_ = _ * jump (Tofu p n) (fun v=>(milU p U inert v).val) (x,i,j) (y,k,l)
  by_cases w : p.mills n x = y
  · subst y; rw [p.nodex]; by_cases u : node x∈ H <;> simp [← e (node x),u]
  rw [jump_apply,if_neg (show Tofu p n x≠ _ from w)]; simp
lemma refl_modes (S : Support (More n)) : twist (carR i s n) (cutM (modesIn n S))= cutM (modesIn n (S.image ((plane i s).anon n))) := by
  apply prep_moves; intro x
  constructor; rintro h; obtain ⟨x,p,rfl⟩:= mem_image.mp h; rwa [fling_there]
  exact fun p=> mem_image.mpr ⟨_,p,fling_there ..⟩
lemma exchanges_halves (n : Side) : twist (carR i s n) (cutM (Tset n)ᶜ)=cutM (Tset n) := by
  have h : twist (carR i s n) (cutM (Tset n))=1-cutM (Tset n) := tickR (plane i s) inert (pinLift i) (mirrorX i) n
  rw [dim_cut,map_sub,map_one,h]; abel
lemma refl_fine (b : Bool) (T : Support (More n)) (f : FC (Single n)) (h : Reed.Fine (Tset n) (modesIn n T) b f) :
    Reed.Fine (Tset n) (modesIn n (T.image ((plane i s).anon n))) b (theta (carR i s n) f) :=
  Reed.Fine.arrive (refl_modes i s T) (exchanges_halves i s n) h
end YM.CF.Buffered
