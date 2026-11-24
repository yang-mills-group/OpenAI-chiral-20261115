import Anomaly.WindBra
import Anomaly.PinLocal
import YM.CF.Fixed.Extensive
/-!
128. Physical Mark prescription on a fixed stage, before giving geometry
and pricing. `jointMark` uses the truncations charged in `factorium`,
not the abstract local kernels as Tests.
Costs, aperture Claims and normalization assembled afterwards.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 12000
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Skye Jet Scroll Finset
open RG MeasureTheory Salt Metric Drapes Tulip Lat Branch Cube Tenant Rill
open Buffered StressExchange
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Moto Oath Font Haro Spire Dial
variable {N : Side}
local notation "Ω" => Single N

/-- The price-free masked operands, moving the same J from its reference
anchor to the respective midpoint inside this calculation. O is matter
site, offset in matter sites. `X` is the local truncation for the trace.
The physical (128) scales `jointMark` by Q/τ²; do not leave that out when
spending it. -/
def traceMeter (b:BudgetPoint) (K : Scree.Loom N)(O : Site N)(X : SOp N) : Pane N → ℂ:=
  fun x => Matrix.trace (pinMatrix b K (node O) X x)

def gaugeMark (b:BudgetPoint) (K : Scree.Loom N)(O : Site N)(X : SOp N) : Mark N :=
  fun x => traceMeter b K O X x.1 • 1

def spinMark (b:BudgetPoint)(K : Scree.Loom N)(O : Site N)(X:SOp N) : Mark N :=
  fun x=> preJ (tickA N) (pinMatrix b K (node O) X x.1)

def moveMark (b:BudgetPoint) (K : Scree.Loom N)(O : Site N)(m : Site N) (F : SOp N) : Mark N :=
  spinMark b K m (co_Ψ m O F)

def diffMark (b : BudgetPoint) (K : Scree.Loom N)(O : Site N)(m : ℕ)(Y : Axis→ SOp N) : Mark N :=
  ∑ i:Axis,(moveMark b K O (O+gapPlus i m) (Y i) - moveMark b K O (O-gapPlus i m) (Y i))

def jointMark (b : BudgetPoint) (K : Scree.Loom N)(O : Site N)(m : ℕ)(X:SOp N)(Y : Axis → SOp N) : Mark N :=
  gaugeMark b K O X + diffMark b K O m Y

structure WindowTag (F : Mark N)(o : Site N)(k : ℕ) (c : ℝ) : Prop where
  ticket : AtSupport false (offsetMask k o) F
  rolls : covariant F
  price : ∀ x, ‖F x‖ ≤ c
  pane : ∀ x y : Fields N, x.1=y.1 → F x=F y

namespace WindowTag
variable {F G : Mark N} {o m : Site N} {k r : ℕ} {c d : ℝ}
theorem transfer (p : WindowTag F o k c) (w : offsetMask k o ⊆ offsetMask r m) : WindowTag F m r c :=
  ⟨p.ticket.mono w,p.rolls,p.price,p.pane⟩
theorem add (p : WindowTag F o k c) (q : WindowTag G o k d) : WindowTag (F+G) o k (c+d) :=
  ⟨p.ticket.addM q.ticket,fun s x=>by simp only [Pi.add_apply,p.rolls s x,q.rolls s x,map_add],fun x=>(norm_add_le _ _).trans (add_le_add (p.price x) (q.price x)),
    fun x y w=>by simp only [Pi.add_apply,p.pane x y w,q.pane x y w]⟩
theorem scale (p : WindowTag F o k c) (u:ℂ) : WindowTag (u • F) o k (‖u‖*c) := by
  refine ⟨p.ticket.smulM _,fun v x=>by simp only [Pi.smul_apply,p.rolls v x,twist_scalar],fun x=> ?_,fun x y w=>by simp only [Pi.smul_apply,p.pane x y w]⟩
  rw [Pi.smul_apply,norm_smul]; exact mul_le_mul_of_nonneg_left (p.price x) (by positivity)
theorem minus (p : WindowTag F o k c) : WindowTag (-F) o k c := by simpa using p.scale (-1)
theorem sub (p : WindowTag F o k c) (q : WindowTag G o k d) : WindowTag (F-G) o k (c+d) := by
  rw [sub_eq_add_neg]; exact p.add q.minus
theorem zero : WindowTag (0 : Mark N) o k 0 :=
  ⟨AtSupport.zeroM, fun _ _=> (map_zero _).symm, fun _=> norm_zero.le,fun _ _ _=>rfl⟩
theorem addS {ι:Type*}(S:Finset ι)(f:ι→ Mark N)(c:ι→ℝ)(w:∀ i∈S,WindowTag (f i) o k (c i)) :
    WindowTag (∑ i∈S,f i) o k (∑ i∈S,c i) := by
  induction S using Finset.induction_on with
  | empty=> rw [sum_empty,sum_empty]; exact zero
  | insert i S v ih=> rw [sum_insert v,sum_insert v]; exact (w i (mem_insert_self ..)).add (ih fun x g=> w x (mem_insert_of_mem g))
end WindowTag

lemma inspect_fits (x : Site N) (b : ℕ) : inspected (offsetMask b x) ⊆ offsetMask (b+12) x:= by
  refine (Yaw.touchK _).trans ?_
  intro j hi; obtain ⟨y,w,v⟩:= halo_spec.mp hi; obtain ⟨q,h,u⟩:= halo_spec.mp w
  exact halo_spec.mpr ⟨q,h,(separation_triangle q y j).trans (by omega)⟩

lemma shift_fits (x y : Site N) (b t k : ℕ) (u:separation x y ≤ k) (g: b+2*k ≤ t) :
    offsetMask b y ⊆ offsetMask t x:=by
  intro i hi; obtain ⟨z,w,v⟩:= halo_spec.mp hi; rw [mem_singleton.mp w] at v
  refine halo_spec.mpr ⟨node x,mem_singleton_self _, (separation_triangle (node x) (node y) i).trans ?_⟩
  rw [Hove.ζdist]; omega

variable {b:BudgetPoint} {r k : ℕ} {t d a v : ℝ} {K : Scree.Loom N} {F:SOp N} (o : Site N)
    (h: Roof N t d r K) (l:0<d) (g : Trunk (node o) F k a v d) (p:b.threshold≤t) (q:k+r+10≤b.B) (ha:0≤a)
include h l g p q ha

theorem gaugeWindow : WindowTag (gaugeMark b K o F) o (b.B+12) v := by
  let f:=pinMatrix b K (node o) F
  have hv : ∀ x : Pane N, (∑ i : Ω, ∑ j : Ω, ‖f x i j‖) ≤ v := fun x => pinMatrix_price h l g p q ⟨x, Classical.arbitrary _⟩ ha
  have hx: Envelope f := pinMatrix_env h l g p q ha
  refine ⟨AtSupport.mono ?_ (inspect_fits o b.B),?_,?_,?_⟩
  · exact AtSupport.fromEval (fun x=> Matrix.trace (f x) • 1)
      (Girt.pole_w _ (fun Y : Op Ω=>Matrix.trace Y • (1:FC Ω)) (continuous_id.matrix_trace.smul continuous_const) hx)
      (fun x y u=> congrArg (fun Y : Op Ω=>Matrix.trace Y • (1:FC Ω)) ((pinMatrix_local h l g p q) x y u))
      (fun x=> Reed.Fine.one.scale _)
  · intro u x
    have he:= pinMatrix_gauge h l g p q (x.1,Classical.arbitrary _) u
    change Matrix.trace (pinMatrix b K (node o) F (Lattice.gauge u x.1)) • _= twist _ (Matrix.trace (f x.1) • 1)
    dsimp only at he
    rw [he,trace_twist,twist_scalar,map_one]
  · intro x
    unfold gaugeMark; rw [norm_smul,norm_one,mul_one]; unfold traceMeter Matrix.trace
    exact (norm_sum_le ..).trans ((sum_le_sum (fun i (_:i∈(univ:Finset Ω))=> Finset.single_le_sum (f:=fun j=> ‖f x.1 i j‖) (fun j _=> norm_nonneg _) (mem_univ i))).trans (hv x.1))
  intro x y H; unfold gaugeMark; rw [H]

theorem spinWindow : WindowTag (spinMark b K o F) o (b.B+12) (v+v) := by
  let f:=pinMatrix b K (node o) F
  have hx: Envelope f:= pinMatrix_env h l g p q ha
  let S:=Tset N
  let A:= tickA N
  have he: A=cutM S:=touchP _ -- check
  have hA:= Cascade.plus_P N
  refine ⟨AtSupport.mono (AtSupport.fromEval (S:= inspected (offsetMask b.B o)) (fun x=>preJ A (f x)) (Girt.pole_w _ (preJ A) ?_ hx)
    (fun x y H=>congrArg (preJ A) ((pinMatrix_local h l g p q) x y H)) ?_) (inspect_fits ..), ?_, ?_, fun x y H=>congrArg (fun V : Pane N=> preJ A (f V)) H⟩
  · unfold preJ dg dyad
    fun_prop
  · intro x; rw [he]
    let X:=offsetMask k o
    refine Window.fine_enlarge (modes_monotone ?_) (StressExchange.inSector (f x) S (modesIn N X) (pinMatrix_support h l g p q (x,Classical.arbitrary _)))
    exact (Corona.halo_mono (show k≤b.B by omega) le_rfl).trans subset_union_left
  · intro C x; let X:=f x.1
    have hv:f (Lattice.gauge C x.1)= twist (tradew N C) X:=pinMatrix_gauge h l g p q (x.1,Classical.arbitrary _) C
    let U:=tradew N C
    change preJ A (f (Lattice.gauge C x.1))= twist (quantU U) (preJ A X)
    have hpA: twist U A=A := Cascade.tick_g _
    rw [hv]; unfold preJ; rw [map_add,twist_scalar,map_one,dg_cov]
    simp only [map_mul,map_sub,map_one,hpA]; rw [show Matrix.trace (A*twist U X)=Matrix.trace (A*X) from ?_]
    rw [← show twist U (A*X)=A*twist U X from by rw [map_mul,hpA]]; exact trace_twist ..
  intro x; let W:=f x.1
  have hv : (∑ i:Ω,∑ j:Ω, ‖W i j‖) ≤ v:= pinMatrix_price h l g p q (x.1,Classical.arbitrary _) ha
  refine (norm_add_le (Matrix.trace (A * W) • (1:FC Ω)) _).trans (add_le_add ?_ ((Fixed.Extensive.dgN W _ _ (hA.norm_le _) (hA.one_sub.norm_le _)).trans hv))
  rw [norm_smul,norm_one,mul_one, he,Matrix.trace]; refine (norm_sum_le ..).trans ((sum_le_sum ?_).trans hv)
  intro i hi; change ‖(cutM S*W) i i‖ ≤ _
  rw [cutM,Matrix.diagonal_mul]; split_ifs; rw [one_mul]; exact single_le_sum (fun i _=> norm_nonneg _) (mem_univ _)
  rw [zero_mul,norm_zero]; exact sum_nonneg fun j _=> norm_nonneg _

-- these pay on the individual Marks before contact replacement.
variable {Y:Axis→ SOp N} (hy : ∀ i:Axis,Trunk (node o) (Y i) k a v d)
include hy

local notation "pp" => (quota^2*v+quota^2*v)
def framePay (v : ℝ):ℝ:= let p:= Tenant.quota^2*v+Tenant.quota^2*v; v+∑ _i:Axis,(p+p)

theorem jointWindow (m:ℕ) : WindowTag (jointMark b K o m F Y) o (b.B+12+2*m) (framePay v) := by
  have he : offsetMask (b.B+12) o⊆ offsetMask (b.B+12+2*m) o := Corona.halo_mono (Nat.le_add_right ..) le_rfl
  refine ((gaugeWindow o h l g p q ha).transfer he).add (WindowTag.addS univ _ _ (fun i _=> ?_))
  have hw (x:Site N)(z:separation o x ≤ m) : WindowTag (moveMark b K o x (Y i)) o (b.B+12+2*m) pp :=
    (spinWindow x h l ((hy i).station x) p q ha).transfer (shift_fits o x _ _ _ z le_rfl)
  exact (hw _ (stopBeam o i m).1).sub (hw _ (stopBeam o i m).2)
end YM.CF.Swell
