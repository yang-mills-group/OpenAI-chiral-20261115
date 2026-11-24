import YM.SU5.Interaction.Source.Flux
import YM.SU5.Exchange.Stack.Manor
/-!
# Symmetric current kernels, before moving to Sweep frames

Rooted `Soak` budgets on the full Guard helmet, using the actual projector
and the actual Aim (their authorizations `p,t`). W is the occupancy in
Interaction/Source, hence the jump is in matter sites without requiring
block congruence. J uses `Pipe`'s column routing, and the centered rake
from `Stride`. This is before mask and CAR reflection centering.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.LitCurrent
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{X Y:SOp N}{o:Seat N}{a b c d v:ℝ}{r:ℕ}
local notation "I" => Single N

lemma house_cell (y:Site N): houseW y=millQ y:=by
 rw [millSt]
 unfold houseW cutM inhabit Tye.stock
 apply congrArg Matrix.diagonal
 funext i; simp [place_x,Swell.unaryN.eq_iff]

lemma house_bill (y:Site N): Soak (node y) (fun _=>houseW y) a (oneMill a) d:= by
 rw [house_cell]; exact millBill _

lemma soak_move {x y:Site N}(Z:Soak (node y) X a v d)(p:separation x y ≤ r)(h:0≤a):
    Soak (node x) X a (Real.exp (a*(4*(2*(r:ℝ))+1))*v) d:=by
 apply lift_U (soak_tr (o':=node x) Z h)
 apply mul_le_mul_of_nonneg_right _ (soakCostNN Z)
 rw [Real.exp_le_exp]
 apply mul_le_mul_of_nonneg_left _ h
 gcongr
 rw [Hove.ζdist,separation_comm y]; exact_mod_cast Nat.mul_le_mul_left 2 p

abbrev rakePrice (a:ℝ)(r:ℕ):ℝ:=4*r*Real.exp (a*(4*(2*(r:ℝ))+1))
lemma rake_bill (Z:Site N→SOp N) (p:∀ x, Soak (node x) (Z x) a v d)
    (h:0≤a)(g:Axis)(m:ℕ)(u:m≤r)(x:Site N):
    Soak (node x) (fun y=> StressExchange.rake (step g) (fun i=>Z i y) m x) a
      (4*m*Real.exp (a*(4*(2*(r:ℝ))+1))*v) d:=by
 induction m with
 |zero=> simpa [StressExchange.rake] using ring_u (d:=d) (a:=a) (node x)
 |succ m ih=>
   have v(x y:Site N){c:ℕ}(hc:c≤r)(e:separation x y ≤ c):= soak_move (p y) (e.trans hc) h
   -- shadow v for calls
   have hh:=plus_U (plus_U (plus_U (plus_U (ih (by omega))
       (v x _ (Nat.le_trans (Nat.le_succ m) u) (stopBeam x g m).1))
       (v x _ (Nat.le_trans (Nat.le_succ m) u) (stopBeam x g m).2))
       (v x _ u (stopBeam x g (m+1)).1)) (v x _ u (stopBeam x g (m+1)).2)
   refine lift_U hh (le_of_eq ?_); push_cast; ring

lemma cube_bill (Z:Site N→SOp N)(p:∀ x, Soak (node x) (Z x) a v d)
    (h:0≤a)(r:ℕ)(L:List Axis)(x:Site N):
    Soak (node x) (fun y=>cubelet r L (fun i=>Z i y) x) a
      ((rakePrice a r)^L.length*v) d:=by
 induction L generalizing x with
 |nil=> rw [List.length_nil,pow_zero,one_mul]; exact p x
 |cons i L ih=>
    refine lift_U (rake_bill _ ih h i r (le_refl _) x) (le_of_eq ?_)
    rw [List.length_cons,pow_succ']; unfold rakePrice; ring

abbrev roomPrice (a:ℝ)(r:ℕ):ℝ:=(rakePrice a r)^4*oneMill a
lemma room_bill (x:Site N)(r:ℕ)(h:0≤a): Soak (node x) (fun _=> roomW x r) a (roomPrice a r) d:=
 cube_bill (fun i _=>houseW i) house_bill h r arcOrder x

variable (P T:SOp N)
/-- Symmetric hits at ±r from the matter root. -/
def firstLink (r:ℕ)(a:Axis)(x:Site N):SOp N:=fun V=>packlet r
    (fun i=>chute (millIntro P T) i.1 i.2 V) a x
lemma first_sum (r:ℕ)(G:Chin N)(h:IsStarProjection (P G))(x:Site N):
    Sault.inward (P G) (roomW x r) (T G) =
     ∑ i:Axis,(firstLink P T r i (x+r • step i) G-firstLink P T r i (x-r • step i) G):=by
 let W: LinksV N (Op I):= fun i=> chute (millIntro P T) i.1 i.2 G
 let L:Op I →+ Op I:= inhibitMap (P G) (Swell.sunA P T G)
 have hp: desc W=L ∘ houseW:=funext fun x=>by
    have hv:(∑ x:Site N, millIntro P T x G)=0:= inwardFlux _ millQ _ _ h sumCell
    have hx:= pipeEquation (millIntro P T) G hv x
    change desc W x=L (houseW x); rw [house_cell]; exact hx.symm
 change L (cubelet r arcOrder houseW x)=∑ i:Axis,(packlet r W i (x+r • step i)-packlet r W i (x-r • step i))
 rw [←blockRecv,hp]; exact congrFun (cubelet_natural L houseW r arcOrder) x

/-- Perpendicular rake budgets at the SAME expense across all tori. -/
lemma first_bill (r:ℕ)(h:0<a)(ht:0<b): ∃ Z> (0:ℝ), ∀ {N:Side}(P T:SOp N),
   Solo (100*a) b P d → Solo (100*a) b T d → ∀ (i:Axis) x, Soak (node x) (firstLink P T r i x) a Z d:=by
 let R:=inlandW (100*a) b; have hw:0 ≤ R:=by unfold R inlandW feeRise payΩ oneMill; positivity
 obtain ⟨V,hV,v⟩:= stepOwed (d:=d) h hw
 let A:=Real.exp (a*(4*(2*(1:ℝ))+1))
 let X(i:Axis):=(rakePrice a r)^(StressExchange.north r i).length * (V+A*V)
 have hz(i:Axis):0 ≤ X i:=by unfold X rakePrice A; positivity
 refine ⟨1+∑ i:Axis,X i, add_pos_of_pos_of_nonneg zero_lt_one (sum_nonneg fun i _=>hz i),?_⟩
 intro N P T H G i x
 have hy(y:Site N):= v (millIntro P T) (fun z=>inlandFee H G (by positivity) z) y i
 refine lift_U (cube_bill (v:=V+A*V) (fun (x:Site N) (u:Chin N)=> StressExchange.grain (step i) (fun y=> chute (millIntro P T) y i u) x) (fun y=>?_) h.le r (StressExchange.north r i) x) ?_
 · apply plus_U (hy y)
   have hu : separation y (y-step i) ≤ 1:=by simpa [gapPlus] using (stopBeam y i 1).2
   simpa only [Nat.cast_one] using soak_move (hy (y-step i)) hu h.le
 exact (single_le_sum (fun i _=>hz i) (mem_univ (α:=Axis) i)).trans (le_add_of_nonneg_left zero_le_one)

/-- Hermitian kernel whose trace gives exactly `legTax` on actual links. -/
def taxKernel (P:SOp N)(x:Site N)(r:ℕ)(U:Chin N): Op I:=
 (2:ℂ)⁻¹ • ((P U-tickA N)*roomW x r+roomW x r*(P U-tickA N))
lemma tax_eq (U:Chin N)(x:Site N)(r:ℕ): Matrix.trace (taxKernel P x r U)=legTax (P U) (tickA N) (roomW x r):=by
 unfold taxKernel legTax; rw [Matrix.trace_smul,Matrix.trace_add,Matrix.trace_mul_comm (roomW x r),smul_eq_mul]; ring
abbrev taxPrice (a b:ℝ)(r:ℕ):ℝ:= 2*((b+Tap.wingRent Fir.Aop a)*roomPrice a r)
lemma tax_bill (x:Site N)(h:0≤a)(p: Solo a b P d)(r:ℕ): Soak (node x) (taxKernel P x r) a
    (taxPrice a b r) d:=by
 let A:= room_bill (d:=d) x r h; let u:=p.sub (Tap.soil_tick (N:=N) a d)
 refine lift_U (less_U (plus_U (aura_Y A u h) (aura_X A u h)) (2:ℂ)⁻¹) (le_of_eq ?_)
 unfold taxPrice; norm_num; ring
end YM.CF.LitCurrent
