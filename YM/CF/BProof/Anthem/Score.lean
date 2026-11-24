import YM.CF.BProof.Anthem.East
import YM.CF.BProof.Charge.Own
import YM.CF.BProof.Physical
/-! Band Score with bought traces. Representatives on EVERY mark argument, within costs.
Summing face labels, equivariance of N, equivariance of whole slot system under Frozen on D. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.BProof.Anthem
open Function Filter NormedSpace Finset MeasureTheory
open Cube Lattice Tenant SU Lat Dial Tulip Fock Skye Spin Branch Hearth Tape Hero Stint Oasis Scree Palot Wick Crystal Garden Veil Trek Mark Mapping Angular
open Vault Paige Drapes Moment RG Wilson
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical Hearth Tape Mark
attribute [local instance] opCStarAlgebra
variable {N:Side} {I:Type}[Fintype I](Y:Yard (More N))
structure Score (Y:Yard (More N))(I:Type)[Fintype I] where
 y:ℝ
 S:Hall (More N)
 G:Side
 f:Ratio G (More N)
 r:ℕ
 M: Manus N I
 -- gauge cost endpoint (outlay)
 gaugeCharge : Y.Index→ Pane N → ℝ
namespace Score
variable {Y}(Q: Score Y I)(i:Y.Index)
structure Budget (Q:Score Y I)(A B C:ℝ) : Prop where
 big: 4≤Q.G.val
 width: Hero.Width Q.f Y.long
 see : Seen Q.S.K Q.y
 xi : BProof.xi Q.y≤ 1
 rho : ∃ ρ:ℝ, 0≤ρ ∧ Moment.Toll Q.M.floor Q.M.price ρ A
 costG (i:Y.Index)(U:Pane N): ‖Q.gaugeCharge i U‖≤ B*((More N).val:ℝ)^3
 meas(i:Y.Index): Measurable (Q.gaugeCharge i)
 read(i:Y.Index): LocalOn (↑(Y.band i)) (Q.gaugeCharge i)
 walk(i:Y.Index)(g:Geometry N)(U:Pane N): Q.gaugeCharge i (gauge g U)=Q.gaugeCharge i U
 ang(i:Y.Index)(U:Pane N)(v:Y.FaceS): Y.toll i Q.y Q.S U v ≤ Real.exp (C*((More N).val:ℝ)^3)
-- Band index grammar
variable (x:Pane N)(b:Eyes (More N))(v:Angular.Signs (More N))
-- truncated grade acts at ALL nodes in band, only deep uses exp
variable (Y) in
def inn := univ.filter (fun j:Site N=> node j∈Y.band i)
def mask := Manus.fee Q.M Y i Q.r (fiddle Y i Q.S Q.f x b)
def t := Y.toll i Q.y Q.S x (fun _=>b)
def amt := (Q.t i x b:ℂ)*Complex.exp ((Q.gaugeCharge i x:ℂ)-Q.mask i x b)
def H : Quilt N:=fun p=> summer Y i Q.S Q.f x b p 2
def partOp : FC (Single N):= (Q.amt i x b) • (Madd (Q.H i x b)).prod (inn Y i)
def named := if Y.D i then {(0:Angular.Signs (More N))} else wages (Y.u i) Y.long Q.y Q.S x
def basisLabel := if Y.D i then 1 else peeks (Y.u i) Y.long Q.y Q.S x v
lemma basis_eq(f:Y.Glyph): Q.basisLabel i x (f i)=Y.sweepLabel Q.y Q.S x f i:=rfl
def slot (x:Pane N) : FC (Single N):=∑ j∈Q.named i x,Q.partOp i x (Q.basisLabel i x j)
local instance (I : Type)[Fintype I][DecidableEq I]: MeasurableSpace (Op I):=borel _
local instance (I : Type)[Fintype I][DecidableEq I]: BorelSpace (Op I):=⟨rfl⟩
variable {A B C:ℝ}
lemma H_seal (p:Site (More N)):SealH (Q.H i x b p):= (nightsM Y i Q.S Q.f x b p).1.1 _
lemma fork (r:Y.FaceS) : Q.t i x (r i)=Y.toll i Q.y Q.S x r:=rfl
@[fun_prop] lemma seat_m : Measurable (uncurry (Q.H i)):= storyL Y i Q.S Q.f 2
@[fun_prop] lemma label_m : Measurable (fun x=> Q.basisLabel i x v):=by unfold basisLabel; split_ifs; exact measurable_const; exact peek_m ..
lemma named_m : MeasurableSet {x:Pane N | v∈ Q.named i x}:=by unfold named; split_ifs; by_cases k:v=0 <;> simp [k]; exact wage_m .. -- tune
lemma inn_scope : modes (Y.band i)= stake (inn Y i):= by ext j; simp [inn]
lemma partOp_modes : Sector (modes (Y.band i)) false (Q.partOp i x b):= (inn_scope i).symm ▸ ((Madd _).prod_at (inn Y i)).scale _ -- tune
lemma slot_modes : Sector (modes (Y.band i)) false (Q.slot i x):=by
 let F(j:Angular.Signs (More N)):= Q.partOp i x (Q.basisLabel i x j)
 have h(S:Finset (Angular.Signs (More N))): Sector (modes (Y.band i)) false (∑ j∈S,F j):=by
   induction S using Finset.induction_on with| empty=> rw [sum_empty]; apply Sector.zero | insert j S u ih=> rw [sum_insert u]; exact (Q.partOp_modes ..).add ih
 exact h (Q.named i x)
variable (h:Q.Budget A B C)
include h
lemma tapeMeas : Measurable (uncurry (Q.amt i)):=by
 let k (p:Street (More N)): Pane N × Y.FaceS:= (p.1,fun _=>p.2); have ht:Measurable k:=by unfold k; fun_prop
 have hh:=(Measurable.comp Complex.measurable_ofReal ((Y.toll_m i Q.y Q.S).comp ht)) -- tune
 exact hh.mul (Complex.continuous_exp.measurable.comp ((Complex.measurable_ofReal.comp ((h.meas i).comp measurable_fst)).sub ((Q.M.feeMeas Y i Q.r).comp (fiddle_m Y i Q.S Q.f)))) -- tune
@[fun_prop] lemma partOp_m : Measurable (uncurry (Q.partOp i)):= (Q.tapeMeas i h).smul ((Madd_cont _).measurable.comp (Q.seat_m i))
omit h in
lemma rural {D K V:Type}[Fintype K][MeasurableSpace D][AddCommMonoid V][MeasurableSpace V][MeasurableAdd₂ V](f:D→Finset K)(F:K→ D→V)(p:∀ i,Measurable (F i))(h:∀ k,MeasurableSet {x:D| k∈ f x}) : Measurable (fun x=>∑ j∈ f x, F j x):= by
 let A(i)(x:D):= if i∈ f x then F i x else 0; have hh(i):Measurable (A i):= Measurable.ite (h i) (p i) measurable_const
 have hx(x:D): (∑ j∈f x,F j x)=∑ j,A j x:= by unfold A; rw [←sum_filter]; simp -- tune
 simp_rw [hx]; exact Finset.measurable_sum _ (fun i _=> hh i)
lemma z_meas(j:Angular.Signs (More N)): Measurable (fun U:Pane N=> Q.partOp i U (Q.basisLabel i U j)):= by
 change Measurable ((uncurry (Q.partOp i)) ∘ (fun U:Pane N=>(U,Q.basisLabel i U j)))
 apply (Q.partOp_m i h).comp ((measurable_id (α:= Pane N)).prodMk (Q.label_m i j))
lemma slot_m : Measurable (Q.slot i):= rural (Q.named i) (fun j U=> Q.partOp i U (Q.basisLabel i U j)) (Q.z_meas i h) (Q.named_m i)
lemma H_read : LocalOn (↑(Y.band i)) (fun x=> (Madd (Q.H i x b)).prod (inn Y i)):= fun U V p=> Madd_here (fun j u=> congrFun (Trek.strong Y i Q.S Q.f U b V p h.big h.width _ (mem_filter.mp u).2).2 _)
lemma amt_read : LocalOn (↑(Y.band i)) (fun x=>Q.amt i x b):=by
 intro U V p; dsimp only; unfold amt mask; rw [h.read i U V p,Q.M.feeAgree Y i Q.r (fiddle_read Y i Q.S Q.f U b V p h.big h.width)]; unfold t Yard.toll; split_ifs with g; rw [shut_local _ _ Q.y U V p]; try dsimp only
 rw [stream_local _ _ Q.y Q.S U b Y.lL V p] -- tune gauge variable s
lemma partOp_read : LocalOn (↑(Y.band i)) (fun x=>Q.partOp i x b):= fun U V p=>congrArg₂ (· • ·) (Q.amt_read i b h U V p) (Q.H_read i b h U V p)
lemma slot_read : LocalOn (↑(Y.band i)) (Q.slot i):=by
 intro U V p; have hz:=Y.long_lt.trans Y.count_lt
 have E: Q.named i U=Q.named i V:=by unfold named; split_ifs; rfl; exact wages_local _ _ _ _ U hz V p
 have L(z): Q.basisLabel i U z=Q.basisLabel i V z:=by unfold basisLabel; split_ifs; rfl; exact peeks_local _ _ _ _ U hz V p _
 exact sum_congr E fun z hv=> by rw [L]; exact Q.partOp_read i _ h U V p
lemma openN (g:Geometry N)(u:¬Y.D i): twist (quantU (tradew N g)) (Q.partOp i x b)= Q.partOp i (gauge g x) (b*(eye (Y.u i) Y.long g)⁻¹):=by
 let F:=b*(eye (Y.u i) Y.long g)⁻¹; let L:=Lattice.gauge g x
 have ht: Q.H i L F=stitch g (Q.H i x b):=funext fun k=>congrFun (Trek.wear Y i Q.S Q.f x b g u k).2 2
 have he: Q.amt i (gauge g x) (b*(eye (Y.u i) Y.long g)⁻¹)= Q.amt i x b:=by unfold amt t Yard.toll mask; simp only [if_neg u,stream_rot,h.walk, fiddle_move Y _ Q.S Q.f x b g u,Q.M.feeTwist Y i Q.r g]
 unfold partOp; rw [he,twist_scalar,Madd_march, ← ht]
lemma closeD (g:Geometry N)(u:Y.D i)(p:Set.EqOn g 1 ↑(Y.band i)): twist (quantU (tradew N g)) (Q.partOp i x b)=Q.partOp i (gauge g x) b:=by
 have hz:Agrees (↑(Y.band i)) x (gauge g x):= fun j hj v=> by unfold Lattice.gauge; rw [p hj,p v]; simp
 rw [← (show Q.partOp i x b=Q.partOp i (gauge g x) b from Q.partOp_read i b h _ _ hz)]; unfold partOp; rw [twist_scalar,Madd_march,Madd_here (A:=stitch g (Q.H i x b)) (B:=Q.H i x b) (S:=inn Y i)]; intro j v; change motion (g (node j)) _=_; rw [p (mem_filter.mp v).2]; exact congrFun motion_one _
lemma slot_rot (g:Geometry N)(u: Y.Frozen g) : twist (quantU (tradew N g)) (Q.slot i x)=Q.slot i (gauge g x):=by
 unfold slot basisLabel named; rw [map_sum]; split_ifs with k
 · rw [sum_singleton,sum_singleton]; exact Q.closeD i x 1 h g k (u i k)
 exact wages_sum (Y.u i) Y.long Q.y Q.S x (fun b=> twist (quantU (tradew N g)) (Q.partOp i x b)) (Q.partOp i (gauge g x)) h.see g (fun b _=> Q.openN i x b h g k)
end Score
end YM.CF.BProof.Anthem
