import YM.CF.Buffered.CutChange
import YM.CF.Fixed.Seam

/-!
# Testing the hot integral at the specified plane

No translation-invariance assumption on any selected period-limit or coarse
state! Use the plane of the tests on the given cube. Transform both slots
using the *same* change of coordinates so as to do the kernel calculation at
that plane in the sewn/cut basis.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Buffered.Heat
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Kronecker ComplexOrder
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset Reflect
open RP Spark RG WilsonStartup Vale Scroll Spire Nova Push.SectorMeasure Nacre Window Tulip Skye Brace
attribute [local instance] opCStarAlgebra

variable {m B n : Side} {c : Phase.Part m B} {e d a₁ a₂ : ℝ}
local notation "X" => Pack m B
local notation "I" => Xmind m B
local notation "A" => FC (Xmind m B)
local notation "N" => CSide m B
local notation "Wμ" => wheel m B
local notation "β₀" => Brace.northZ m B

variable (i : Axis) (z : ℤ)

-- parameterize plane here by z steps of 4B gauge (thus 2B matter shift). z can be negative.
def gaugeShift (B : Side) (z : ℤ) : ℤ := 4*B.val*z
def coverShift (i : Axis) (B : Side) (z : ℤ) : Cover := (2*(↑B.val:ℤ)*z) • step i
def liftShift (B : Side) (z : ℤ) (F : Evaluation n) : Evaluation n := fun x =>
  twist (quantU (prepU (lagX (coverShift i B z)) 1 inert n)) (F (Yg (lagX (-(coverShift i B z))) x))
lemma shift_eq (B : Side) : B.val • ((2*z) • step i : Cover)=(coverShift i B z) := by
  unfold coverShift; rw [mul_comm (2:ℤ) (↑B.val), mul_assoc, mul_smul]; simp; ring
lemma pack_shift (x : X) : (onPack B (shiftTrip m ((2*z) • step i)) x).1 = Yg (lagX (coverShift i B z)) x.1 := by
  rw [shift_pack,shift_eq]
lemma lag_cancel (q : Cover) (x : Pane n) : Yg (lagX (-q)) (Yg (lagX q) x) = x := by rw [←kor, trips, add_neg_cancel]; exact Nacre.blank _
lemma liftShift_env (B : Side) (f : Evaluation n) (h : Envelope f) : Envelope (liftShift i B z f) := by
  have he : Continuous (Yg (n:=n) (lagX (-(coverShift i B z)))) := by
    simp_rw [show @Yg n (lagX (-coverShift i B z))=pull (K:=SU.group.El) 1 (wrap _ (2 • -(coverShift i B z))) from rfl]; exact Wilson.continuous_pull ..
  exact Girt.pole_w (fun y : Pane n=>f (Yg (lagX (-(coverShift i B z))) y)) _ (breeze _) (Env.along h he.measurable)

lemma liftShift_local (B : Side) (f : Evaluation n) (w : ℕ) (h : LocalOn (Buffered.band n i (gaugeShift B z) w:Set _) f) :
    LocalOn (Buffered.band n i 0 w : Set _) (liftShift i B z f) := by
  intro x y hxy; unfold liftShift; apply congrArg; apply h; apply Yg_agrees
  apply agrees_mono hxy _; intro j hj; obtain ⟨k,e,rfl⟩ := mem_image.mp hj
  have he:= (band_shift i (gaugeShift B z) n (-(2*(↑B.val:ℤ)*z)) w k).1 e
  rw [show (gaugeShift B z)+2 * -(2*(↑B.val:ℤ)*z)=0 from by unfold gaugeShift; ring, neg_smul] at he; exact he
lemma north_sector (e : Finset (Single n)) {V : UNI (Single n)} (f : Finset (Single n)) (h : twist V (cutM e)=cutM f)
    {b : Bool} {x : FC (Single n)} (p : Sector e b x) : Sector f b (twist (quantU V) x) := by
  have hx i (v:i∈e) : Sector f true (twist (quantU V) (put i)) := by
    rw [←create_put,twist_create]; apply Sector.makeP; nth_rw 1 [←h]; rw [←Fock.swivel,cut_basis]; rw [if_pos v]
  induction p with
  | up _ p => exact hx _ p
  | down i p => rw [takeF,map_star]; exact (hx i p).contr
  | zero=> rw [map_zero]; apply Sector.zero
  | one=> rw [map_one]; apply Sector.one
  | add _ _ p q=> rw [map_add]; exact p.add q
  | mul _ _ p q=> rw [map_mul]; exact p.mul q
  | scale _ c p=> rw [twist_scalar]; exact p.scale c
lemma liftShift_modes (B : Side) (f : Evaluation n) (w : ℕ)
    (h : ∀ x,Sector (modesIn n (Buffered.band n i (gaugeShift B z) w)) false (f x)) :
    ∀ x, Sector (modesIn n (Buffered.band n i 0 w)) false (liftShift i B z f x) := by
  intro x; apply north_sector _ _ _ (h _); apply prep_moves; intro x
  rw [show (gaugeShift B z)=2*(2*(↑B.val:ℤ)*z) from by unfold gaugeShift; ring]; simpa only [coverShift,zero_add] using (band_shift i 0 n (2*(↑B.val:ℤ)*z) w x)
lemma liftShift_prod (B : Side) (F G : Evaluation n) : liftShift i B z (F*G)=liftShift i B z F*liftShift i B z G := by funext x; exact map_mul ..
lemma liftShift_refl (B : Side) (f : Evaluation n) (b : Bool) (k : Finset (Single n)) (h : ∀ x, Sector k b (f x)) :
    liftShift i B z (Buffered.refl i (gaugeShift B z) f)= Buffered.refl i 0 (liftShift i B z f) := by
  funext x; unfold liftShift Buffered.refl
  have hp : fling i (gaugeShift B z) n (Yg (lagX (-(coverShift i B z))) x)=Yg (lagX (-(coverShift i B z))) (fling i 0 n x) := by
    apply_fun Yg (lagX (coverShift i B z)); swap
    · apply LeftInverse.injective (g:=Yg (lagX (-(coverShift i B z)))); exact fun x=> lag_cancel ..
    have hv(x:Pane n): Yg (lagX (coverShift i B z)) (Yg (lagX (-(coverShift i B z))) x)=x:=by nth_rw 1 [←neg_neg (coverShift i B z)]; rw [lag_cancel]
    rw [show (gaugeShift B z)= _ from (show gaugeShift B z=2*(2*(↑B.val:ℤ)*z) by unfold gaugeShift; ring)]
    change Yg (lagX ((2*(↑B.val:ℤ)*z) • step i)) _ = _
    rw [fling_shift,hv]; exact congrArg (fling i 0 n) (hv x)
  rw [hp]; apply twist_inter _ _ _ _ (h _)
  rw [show (gaugeShift B z)=2*(2*(↑B.val:ℤ)*z) from by unfold gaugeShift; ring]; exact congrArg Subtype.val (carR_shift i (2*(↑B.val:ℤ)*z) n)

variable (p : Pinning m B) (W : Scroll m B c) (clip : Clip) (β t u : ℝ)

def insertTop (f : Evaluation N) : RP.Test m B := fun x => crossL (helix _).symm (f x.1)
def rephased (f : Evaluation N) : RP.Test m B := fun x => toSeam m B i (liftShift i B z f x.1)
lemma rephased_eq (f : Evaluation N) (e : ℝ) :
    heatNum p W clip β t e u β₀ (insertTop f) = heatNum p W clip β t e u (axisCut m B i β₀) (rephased i z f) := by
  trans heatNum p W clip β t e u β₀ (insertTop (liftShift i B z f))
  · apply heatNum_shift _ _ _ _ _ _ ((2*z) • step i)
    intro x; unfold insertTop liftShift; rw [pack_shift,lag_cancel,shift_eq]
    exact CF.Fixed.across_twist (helix _).symm (shiftFrame (coverShift i B z) N) (prepU (lagX (coverShift i B z)) 1 inert N) rfl _
  exact integral_congr_ae (Eventually.of_forall fun x=> heatTerm_cut p W clip β t u _ (axisCut m B i β₀) _ _ _ x rfl)
lemma north_modes_eq : modesIn N (Buffered.band N i 0 0) = Window.matterSet N (posY m B i) := by
  rw [band_zero, modesIn]; congr; ext x; exact (sites_at _ _).trans (holder ..).symm
lemma rephased_north (f : Evaluation N) (h : Envelope f) (w : LocalOn (Buffered.band N i (gaugeShift B z) 0 : Set _) f)
    (u : ∀ x, Sector (modesIn N (Buffered.band N i (gaugeShift B z) 0)) false (f x)) : NorthMark i (rephased i z f) := by
  refine ⟨Girt.pole_w _ (toSeam m B i) ((breeze _).comp (cxC _)) (Env.along (liftShift_env i z B f h) measurable_fst),
    fun x=> toSeam_forward i (north_modes_eq i ▸ liftShift_modes i z B f 0 u x.1) rfl,?_⟩
  intro x y k; unfold rephased; apply congrArg; apply liftShift_local _ z B f 0 w; rw [band_zero]; exact k.gaugeS
lemma rephased_pair (f g : Evaluation N) (h : ∀ x,Sector (modesIn N (Buffered.band N i (gaugeShift B z) 0)) false (f x)) :
    rephased i z (Buffered.refl i (gaugeShift B z) f * g)=testProduct i (rephased i z f) (rephased i z g) := by
  funext x; unfold rephased testProduct; rw [liftShift_prod,Pi.mul_apply,toSeam_prod,liftShift_refl _ z B f _ _ h]
  unfold Buffered.refl; rw [carR_zero,fling_zero, toSeam_turn i (north_modes_eq i ▸ liftShift_modes i z B f 0 h _)]
  rfl
section plt
variable (b : Budget B e d) (H : ScaleK a₁ a₂ W)
include H b
local notation "S" => Buffered.band N i (gaugeShift B z) 0
-- whole translated statement, pinning as in Manuscript
lemma displaced_limit (hu : 0 ≤ u) (f g : Evaluation N) (hf : Envelope f) (hg : Envelope g)
    (wf : LocalOn (S:Set _) f) (wg : LocalOn (S:Set _) g)
    (p' : ∀ x,Sector (modesIn N S) false (f x)) (q' : ∀ x,Sector (modesIn N S) false (g x)) :
    let T := fun n => transfer p W clip β t u e i β₀ n
    Tendsto (fun n=>kernelTrace (n+1) (T n (rephased i z g)) (kernelStar (n+1) (T n (rephased i z f)))) atTop
      (𝓝 (heatNum p W clip β t e u β₀ (insertTop (Buffered.refl i (gaugeShift B z) f * g)))) := by
  intro T; rw [rephased_eq i z p W, rephased_pair _ z _ _ p']
  exact from_layers p W clip β t u b H i _ hu _ _ (rephased_north i z f hf wf p') (rephased_north i z g hg wg q')

theorem top_nonnegative (hu : 0 ≤ u) (f : Evaluation N) (h : Envelope f) (w : LocalOn (S:Set _) f)
    (w₀ : ∀ x,Sector (modesIn N S) false (f x)) :
    0 ≤ heatNum p W clip β t e u β₀ (insertTop (Buffered.refl i (gaugeShift B z) f * f)) := by
  rw [rephased_eq i z p W,rephased_pair _ z f f w₀]
  exact two_slab p W clip β t _ b H i β₀ hu _ (rephased_north i z f h w w₀)
end plt
end YM.CF.Buffered.Heat
