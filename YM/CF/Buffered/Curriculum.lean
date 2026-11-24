import YM.CF.Volume.Window
import YM.CF.Buffered.Cone
import YM.CF.Buffered.Feats
/-!
# Curriculum. Period list simultaneous prescription & costs. Small sharp anchor.
Uses BudgetCompared on bottom from matched-budget gluing (ms price p-delt).
-/
set_option autoImplicit false
set_option maxHeartbeats 380000
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.Buffered
open Function NormedSpace Filter Metric Finset Lattice MeasureTheory RG
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker ComplexOrder
open Cube Tenant Lat Spire Scroll Scree Jet Phase Branch Fock Skye
open Py Vale Vale.Grace Haro Nova
open Wilson Precision Next.Free Next.SectorChange Tulip Gauge Paige Vault Brace
open Push.SectorMeasure
open Heat Advance Pressure Region
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra

namespace Burn
variable {m B :Side} {n:ℕ}

-- apply to fixed pivot posterior, threshold is independent of which pivot (expands `enrollment`).
structure SpanCal (K:Calibration) where
 KX:ℝ
 read:ℝ
 vL:ℝ
 c':ℝ
 l':ℝ
 b:ℝ
 D:ℝ
 E':ℝ
 C0:ℝ
 h1:ℝ
 r:ℝ
 kT:ℕ
 d':ℕ
 spanX: Pic.Span K.W.pearl KX read vL c' l' b kT
 portX: Mint.Roe.Port spanX D E' C0 h1 r d'
 enough_h:C0 ≤ K.h
 c:ℝ
 k:ℕ

variable {K:Calibration} (p:SpanCal K)
noncomputable def enrollment : ℝ:= (Filter.eventually_atTop.mp (Volume.Window K.V K.a K.p K.i K.N0 K.J K.η K.h K.R0 K.δ p.c p.k K.positive_h p.spanX p.portX p.enough_h)).choose
def under (m: Side) : Prop := grainZ K.V K.W K.N0 K.x ≤ m.val ∧ (m.val:ℝ) ≤ p.c * (((oYY K.V K.N0 K.J K.x).val:ℝ)^p.k)
def rake (m:Side) : ℝ:= Volume.ell K.V (K.c m) K.x p.b p.read

structure Conveyor (K:Calibration) where
 loom : ∀ m: Side, Cape m K.B K.R.L
 lawn : ∀ m, K.takes m → ∀ j:ℕ, LoomLaw (loom m j) K.w
 sharp : ∀ m: Side, ℕ → Vestal m K.B K.R.L
 warm : ∀ m: Side, ℕ → Vestal m K.B K.R.L
 B₀ : ℕ→ℕ→ℝ
 wave : ℕ→ℕ→SpaceM
 tilt : ℕ→ℕ→ℝ
 wave' : ℕ→ℕ→SpaceM
 tilt' : ℕ→ℕ→ℝ
structure Tiling (K:Calibration) where
 d':Side
 qcount : Side → Side -- exact count at each allowed m, elsewhere not read
 ruler (m:Side)(h: K.takes m) : m=d'*qcount m
 even (m:Side)(h: K.takes m) : Even (qcount m).val

variable (C:Conveyor K)
variable {V:Tiling K} (J:Tiling K) (t:Side)
namespace Tiling
theorem native_ord (r:K.takes t) (n:ℕ) : Ordered (mesh t K.R.L n) (mesh J.d' K.R.L n) (J.qcount t):=
 ⟨⟨(by have ht:= J.ruler t r; change t.val*(K.R.L ^ n).val = J.d'.val*(K.R.L ^ n).val*(J.qcount t).val; rw [show t.val= _ from (show t.val=J.d'.val*(J.qcount t).val from congrArg Subtype.val ht)]; ring
 )⟩,fun _=> J.even t r⟩
end Tiling

-- actual history owned at m if in list & cone. assume histories and grants
-- of ms output. strengthen `Shots` only by carrying press metering choices
-- coherently and BudgetCompared, offset comparison as in p-stepv. plus period
-- pressure needn't lie in list if not divisible q odd (ms cuts sufficient).
abbrev paired (h:K.Allowed m n) :=Shots K.V K.T K.J K.η (K.monthSize m h.1) (C.loom m) n (C.sharp m n) (C.warm m n) (C.wave n) (C.wave' n) (C.B₀ n) (C.tilt n) (C.tilt' n) K.h K.R0 K.δ

def launchK (K:Calibration)(n:ℕ):ℝ:= radiusB (hat K.R.L K.x n)
abbrev topT (K:Calibration)(n:ℕ):=(K.T.a n).threshold
-- horizontal budget comparison hypothesis retained
structure Bedded (h:K.Allowed m n) where
 pair: paired C h
 budget : BudgetCompared K n (C.sharp m n) (C.warm m n)
 P: Donor K.P (C.warm m n) (C.loom m) n
 heat: P.heat=launchK K n
 clip: P.clip=K.K.top.clip

variable {C J}
local notation "X" => C.sharp m n
local notation "Y" => C.warm m n
local notation "S" => C.loom m
local notation "cM" => mesh m K.R.L n
namespace Bedded
variable {h:K.Allowed m n}(F:Bedded C h)(J:Tiling K)

noncomputable def permit : Ticket (mesh m K.R.L n) (mesh J.d' K.R.L n) K.B (J.qcount m) K.e (topT K n):=by
 let t:= F.P.grants
 -- choose not rcases
 let ht:= t.choose_spec.choose_spec.choose_spec
 exact ⟨J.native_ord m h.1 n,F.P.pin,Brace.northZ _ _,F.P.scroll, t.choose, t.choose_spec.choose,ht.1,t.choose_spec.choose_spec.choose,ht.2⟩
#print permit
local notation "μ" => F.permit J
include F
theorem hue_p (k:ℕ)(p:k≤n) : (C.warm m n k).p=K.T.a k:= (Shots.hue F.pair k p).width.symm
lemma offset (k:ℕ)(p:k≤n) : partitionZ (C.warm m n 0) K.P (C.loom m 0)=partitionZ (C.warm m n k) K.P (C.loom m k):=by
 induction k with
 | zero=> rfl
 | succ k ih =>
    obtain ⟨g⟩:= (Shots.warm_grant F.pair).grant k p; rw [ih (by omega)]; exact balance_F g ((Shots.warm_grant F.pair).aligned k p) ((Shots.warm_grant F.pair).branch k p) _ ((Shots.warm_grant F.pair).noTies k (by omega)) (fun i v=> (Shots.warm_grant F.pair).wears k p i v)
lemma pays_num (A:Mark (cell m K.B K.R.L n))(p:Envelope A):
 markedRead A (C.loom m n) (denZ (C.warm m n n) K.P (C.loom m n)) = heatNum F.P.pin F.P.scroll K.K.top.clip (C.warm m n n).beta (topT K n) K.e (launchK K n) (Brace.northZ cM K.B) (Heat.insertTop (both A)):=by
 obtain ⟨a,D,b,k,v⟩:=F.P.grants; obtain ⟨x,y,r,L,H⟩:= F.P.roof; rw [←F.heat,← F.clip,topT,←F.hue_p n le_rfl]; exact summit_num K.P _ _ F.P.pin F.P.scroll _ _ F.P.top k v L H ((Shots.warm_grant F.pair).noTies n le_rfl) p
lemma grantU : partitionZ (C.warm m n 0) K.P (C.loom m 0)= Ticket.moment μ 1 K.K.top.clip (C.warm m n n).beta (launchK K n):=by
 rw [Ticket.moment_zero,offset F n le_rfl,partitionZ, ←markvac (C.loom m n)]; rw [F.pays_num 1 (Girt.rite_c _)]; apply congrArg; funext x; exact Spark.cx_eq _ _ _ fun x=>by simp [Heat.both]
lemma low (h₁:enrollment p≤ K.x)(g:under p m): 0<rake p m ∧ rake p m≤ ‖vac0 K.P (C.sharp m n 0) (C.loom m 0)‖ :=by
 let A:Volume.History K.V K.a K.p K.i K.N0 K.J K.η K.h K.R0 K.δ K.x m n:= ⟨K.T,K.monthSize m h.1,C.B₀ n,X,S,C.wave n,C.tilt n,Shots.sharp F.pair⟩; have he := (Filter.eventually_atTop.mp (Volume.Window K.V K.a K.p K.i K.N0 K.J K.η K.h K.R0 K.δ p.c p.k K.positive_h p.spanX p.portX p.enough_h)).choose_spec K.x h₁ m g.1 g.2 n A; exact ⟨he.1,he.2.1⟩
end Bedded
end Burn
end YM.CF.Buffered
#print axioms YM.CF.Buffered.Burn.Bedded.low
