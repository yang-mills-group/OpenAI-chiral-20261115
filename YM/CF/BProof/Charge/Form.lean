import YM.CF.BProof.Charge.Own

/- Lie forms L, Q. defined on arbitrary perturbations on all micro bonds here. Specialize
to the canonical projections of VolB to form the gap Hessian. The color norm of `G.Color`
is already physically normalized (including squared factor 5). `leading_curvature` says
its derivative is identity in this normalization. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Charge.Form
open Function Filter RG Wilson Lattice Finset Work Micro Moment MeasureTheory Angular AnalyticBridge.SectorAffine Mag
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
local notation "G" => SU.group
variable {s:Side}(T:PathData G)(M:ℕ)(σ: Signed)(x:Site s)(l:Cell s)

abbrev a₁(p:PlaqAxes):=p.val.1
abbrev a₂(p:PlaqAxes):=p.val.2
def turn (o:Bool) : Lie→ₗ[ℝ] Lie:=if o then -LinearMap.id else LinearMap.id
@[simp] lemma turn_v (u:Lie)(p:Bool): turn (!p) u= -(turn p u):=by cases p<;>simp [turn]
@[simp] lemma turn_size (u:Lie)(p:Bool): ‖turn p u‖=‖u‖:=by cases p<;>simp [turn]

def chargeX (i:Axis) : Lie:=Fin.cases 0 X i
def pointed (a:Axis) := turn (σ.flip a) (chargeX (σ.perm a))
lemma pointed_time {a} (h:σ.perm a=0): pointed σ a=0:=by rw [pointed,h]; apply map_zero

def mark (a:PlaqAxes) : Lie:= SU.group.ad (pointed σ (a₁ a)) (pointed σ (a₂ a))
lemma no_mark (a:PlaqAxes)(h:σ.perm (a₁ a)=0 ∨ σ.perm (a₂ a)=0) : mark σ a=0:=by unfold mark; rcases h with h|h; rw [pointed_time σ h,map_zero]; rfl; rw [pointed_time σ h,map_zero] -- tune

abbrev Argument (s:Side) := Bond s → Lie
-- Regarding a channel-transformed square, there are offset and inversion signs.
def act (p:Bond s): Argument s→ₗ[ℝ] Lie:= LinearMap.proj p
def part (b:Bond s) : Argument s→ₗ[ℝ] Lie:= (turn (σ.flip b.2)).comp (act (sendEdge σ 0 b))
def coset (a:Axis) := if σ.flip a then (-step (σ.perm a):Site s) else 0 -- translation at physical config. implicit s inferred?
lemma part_key (a:Axis) : sendEdge σ 0 (x,a)=(spin σ x+coset (s:=s) σ a,σ.perm a):=by unfold sendEdge Step.used coset; dsimp only [Step.rotate,posDir,affine]; simp only [Bool.false_xor,add_zero]; split; rw [sub_eq_add_neg]; rw [add_zero] -- tune
lemma part_one (b:Bond s) : part 1 b=act b:= by unfold part; rw [Signed.one_flip]; obtain ⟨x,p⟩:=b; rw [part_key]; simp [turn,spin,coset]

/-- order of the four edges (positive orientation throughout). -/
def positions : Fin 4→ Bond s:= ![(l.1,a₁ l.2),(l.1+step (a₁ l.2),a₂ l.2),(l.1+step (a₂ l.2),a₁ l.2),(l.1,a₂ l.2)]
def curlP : Argument s→ₗ[ℝ] Lie:= part σ (positions l 0)+part σ (positions l 1)-part σ (positions l 2)-part σ (positions l 3)
lemma curl_px (W:Argument s) : curlP σ l W=part σ (positions l 0) W+part σ (positions l 1) W-part σ (positions l 2) W-part σ (positions l 3) W:=rfl
lemma curl_positions (i:Fin 4) : let b:=positions l i; b.1∈ touched l ∧ b.1+step b.2∈ touched l:= by
  intro b; rw [Angular.four]; fin_cases i <;> simp [positions,a₁,a₂,b,add_right_comm] -- tune

abbrev coeff (p:PlaqAxes) (a:RG.Slot):= Stack.grouped T p a
def glow (p:PlaqAxes) : Lie:= ∑ i∈Stack.allShort M, coeff T p i • mark σ i.plaq
def ray (a:Lam s): Argument s→ₗ[ℝ] Lie:= ∑ i∈ Stack.allShort M, coeff T a.2.1 i • curlP a.1 (F03.slotFace i (ref a).1)
lemma rays (a:Lam s) (W:Argument s): ray T M a W=∑ i∈Stack.allShort M, coeff T a.2.1 i • curlP a.1 (F03.slotFace i (ref a).1) W:=by simp only [ray,LinearMap.sum_apply,LinearMap.smul_apply]

def root (b:Tile s): Lie:= Sum.elim (fun p=>mark 1 p.2) (fun p=>glow T M p.1 p.2.1) b
def linear (b:Tile s) := Sum.elim (curlP 1) (ray T M) b
def unit (c:Clip)(β:ℝ)(b:Tile s):= β * Sum.elim (fun _=> c.direct) (fun _=>share) b
def L (c:Clip)(β y:ℝ)(b:Tile s) (W:Argument s): ℝ:= unit c β b * inner ℝ (mA y • root T M b) (linear T M b W)
def Q (c:Clip)(β:ℝ)(b:Tile s) (W:Argument s): ℝ:= unit c β b* ‖linear T M b W‖^2/2 -- W actual, later Q uses gw
end YM.CF.BProof.Charge.Form
