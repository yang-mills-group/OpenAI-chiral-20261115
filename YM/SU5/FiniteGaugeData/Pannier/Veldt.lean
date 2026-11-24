import YM.SU5.FiniteGaugeData.Pannier.ShelfFog
import YM.CF.Buffered.Lifted
/-! # Hand-over. projection simplification for Mate and the chosen Ω. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pannier.Chancel
open Function Finset Filter NormedSpace Metric Lattice Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Fixed Skye Pastry
open Damask Buffered
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {n ι : Type*}[LinearOrder n][Fintype n]
def hand (b:Bool)(P:Op n): Op n := if b then 1-P else P
def trim (B:Op n)(x : Ket n):= acts B x=x
def cardH (b:Bool)(P:Op n)(x: Ket n): Ket n:= acts (hand b P) x
def handy (b:Bool) (S:Finset n) (x y:Ket n): FC n := together (creed (!b) x) (creed b (cardH b (cutM S) y))

variable {b:Bool}{P:Op n}{r ε:ℝ}{x y x' z:Ket n}{M:Wave n}
lemma raft (b: Bool)(p:IsStarProjection P): IsStarProjection (hand b P):=by cases b; exact p; exact p.one_sub
lemma raft_trim (b:Bool)(p:IsStarProjection P)(x:Ket n): trim (hand b P) (cardH b P x) := by unfold trim cardH; rw [←act_mul,(raft b p).isIdempotentElem.eq]
lemma including (b:Bool)(P : Op n) : hand (!b) P=1-hand b P:=by cases b; rfl; change P=1-(1-P); abel
lemma server (p:IsStarProjection P)(h: Sea P M)(g:trim (hand b P) x): acts (creed b x) M=0:=by
 cases b; exact tarp p h.1 g; apply tars p h.1; change acts (1-P) x=x at g; rw [act_sub,act_one,sub_eq_self] at g; exact g
lemma muted (b:Bool)(p:IsStarProjection P)(h: Sea P M)(x:Ket n) : mute M (creed b x-creed b (cardH b P x)):=by
 let v:= cardH b P x; let F:= hand b P; have hp: acts (hand (!b) P) (x-v)= x-v:=by
    rw [including,act_sub,act_one,map_sub,raft_trim b p x,show acts F x=v from rfl,sub_self,sub_zero] -- tune
 unfold mute; rw [←courage,show star (creed b (x-cardH b P x))= creed (!b) (x-v) from ?_]; exact server p h hp
 cases b; rfl; exact star_star (create _)
lemma siteCar {q:ℝ} (t:inner ℂ x y=(q:ℂ))(b:Bool): antiB (creed b x) (creed (!b) y)= (q:ℂ) • (1:FC n):=by
 cases b; · rw [antiB_comm]; change antiB (remove y) (create x) = _; rw [antiB,car,show inner ℂ y x=(q:ℂ) from ?_]
            rw [←inner_conj_symm, t]; simp
 change remove x* create y+ create y* remove x=_; rw [car x y,t]
lemma far (X:Finset n)(w:withinM X x):Sector X true (creed b x):=by cases b; exact Sector.makeP x w; exact (Sector.makeP x w).contr
lemma passing (S T:Finset n)(q:trim (hand b (cutM S)) x)(w:withinM T x): Fine S T true (creed b x):=by
 cases b; exact fine_create x q w
 apply fine_remove x _ w; unfold withinM; rw [dim_cut]; exact q
lemma fine_arch (S : Finset n)(u: trim (hand (!b) (cutM S)) x)(y:Ket n): Fine S univ false (handy b S x y):= by
 let R:= cardH b (cutM S) y
 exact Fine.one.add ((passing S _ u (within_univ x)).grow (passing S _ (raft_trim b (cutM_idp S) y) (within_univ R))) -- fix
lemma asGrade (S:Finset n)(q:trim (hand (!b) (cutM S)) x)(y:Ket n): antiB (creed b (cardH b (cutM S) y)) (creed (!b) x)=0:=by
 rw [antiB,(passing S univ (raft_trim b (cutM_idp S) y) (within_univ _)).sign_com (passing S _ q (within_univ _))]; simp [Sector.grainB]
lemma fineWise {s:Finset n}{F G:FC n}(h:Fine s univ false F)(p:Fine s univ false G):Commute F G:=by
 unfold Commute SemiconjBy; rw [h.sign_com p]; simp [Sector.grainB] -- rw loops?
lemma comm_lost {s : Finset n}{G:FC n}(h:Sector s false G)(f:withinM sᶜ x):Commute G (creed b x):= by
 unfold Commute SemiconjBy; rw [h.apart (far _ f) (disjoint_compl_right)]; simp [Sector.grainB]
lemma hand_cost [Nonempty n] (b:Bool)(p:IsStarProjection P)(x:Ket n): ‖cardH b P x‖ ≤ ‖x‖:= (Flare.opy ..).trans (mul_le_of_le_one_left (norm_nonneg _) ((raft b p).norm_le _))
variable {W:Wave n}{T S:Finset n}{G:FC n}{X Y Z:ι→Ket n} {R E:ℝ}
/-- exact λ senders live in hand of spar (supplied fields), contact orth on the X,
local approximation Z needs no uniform order in all budget heights. -/
structure Sheet (S T:Finset n)(P:Op n)(G: FC n)(b:Bool)(X Y Z:ι→Ket n)(R E:ℝ) : Prop where
 gram: ∀ i, trim (hand b P) (Y i)
 sigh: ∀ i, ‖Y i‖ ≤ R
 within: ∀ i, withinM (Tᶜ) (Z i)
 stipend: ∀ i, ‖Z i-Y i‖ ≤ E^3
 seat: ∀ i, trim (hand (!b) (cutM S)) (X i)
 ace: ∀ i, ‖X i‖ ≤ 1
 atone: ∀ i, inner ℂ (Y i) (X i)=1
 unoccupied: ∀ i j, i ≠ j→ inner ℂ (Y i) (X j)=0
 fence: Fine S T false G

local notation "U"=> fun i:ι=> creed (!b) (X i)
local notation "V"=> fun i:ι=> creed b (cardH b (cutM S) (Y i))
local notation "V'"=> fun i:ι=> creed b (cardH b (cutM S) (Z i))
variable (h:Sheet S T P G b X Y Z R E)(p:IsStarProjection P)(e:Sea P W)(m:Sea (cutM S) M)(c:0<E)(g:E ≤ 1)
include h c g p m e
lemma lodging [Nonempty n] : Folder (fun i=> creed (!b) (X i)) (V) (V') (fun i=> creed b (Y i)) (fun i=> creed b (Z i)) b R E M W G:=by
 have hx(i):(V') i-(V) i = creed b (cardH b (cutM S) (Z i-Y i)):=by unfold cardH; rw [map_sub,courage]
 have hf(i):Fine S univ false (((U) i)* ((V') i-(V) i)):=by rw [hx]; exact (passing S _ (h.seat i) (within_univ _)).grow (passing S _ (raft_trim b (cutM_idp S) _) (within_univ _))
 constructor
 · exact fun i=> ⟨_,rfl⟩
 · exact fun i=> ⟨_,rfl⟩
 · intro i; rw [←courage]; apply (Flare.cost_pe ..).trans ((h.stipend i).trans ?_); nth_rw 2 [←pow_one E]; exact pow_le_pow_of_le_one c.le g (by decide)
 · exact fun i=> (Flare.cost_pe ..).trans (h.sigh i)
 · exact fun i=> server p e (h.gram i)
 · exact fun i=> muted b (cutM_idp S) m (Y i)
 · exact fun i j w=> by simpa using siteCar (q:=0) (by simpa using h.unoccupied i j w) b
 · exact fun i=> by simpa using siteCar (q:=1) (by simpa using h.atone i) b
 · exact fun i j=> asGrade S (h.seat j) (Y i)
 · exact fun i=> ⟨_,rfl⟩
 · intro i; rw [hx]; exact ⟨_,_,rfl⟩
 · intro i; rw [hx]; exact (Flare.cost_pe ..).trans ((hand_cost b (cutM_idp S) _).trans (h.stipend i))
 · exact fun i=> ⟨_,_,rfl⟩
 · exact fun i=> (Flare.cost_pe ..).trans (h.ace i)
 · exact fun i j=> fineWise (hf i) (fine_arch S (h.seat j) (Z j))
 · exact fun i=> fineWise (hf i) (Window.fine_enlarge (subset_univ _) h.fence)
 · exact fun i=> comm_lost h.fence.sector (h.within i)

lemma forded [Nonempty n] (t:0<R)(l:List ι)(p':l.Nodup): Yep E⁻¹ (acts (star (fo (fun i=>handy b S (X i) (Z i)) l*G)) M) W ((E*(R+3))^l.length *‖G‖) :=
 (lodging h p e m c g).earn m.2.le c t g e.2 l p'

end YM.CF.Pannier.Chancel
#print axioms YM.CF.Pannier.Chancel.forded
