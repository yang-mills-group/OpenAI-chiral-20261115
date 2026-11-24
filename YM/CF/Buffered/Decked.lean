import YM.CF.Buffered.Film
/-! Collection on local slabs. There are no geometric assumptions on the
histories here: just the algebraic (local-kernelizable) form of these
finite-cube-layer integrals. -/
set_option autoImplicit false
set_option maxHeartbeats 460000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Stack
open Function Fock NormedSpace Finset Filter MeasureTheory Lattice Reflect RG Push.SectorMeasure Cin
open Sector (grainB)
open Film (Leaf)
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology ComplexOrder Fin.NatCast
attribute [local instance] opCStarAlgebra
abbrev DeckIn (n:ℕ)(X Y:Type*):= Many n X × Many n Y
variable {X Y B I J:Type*} [TopologicalSpace X][TopologicalSpace Y][MeasurableSpace X][MeasurableSpace Y][LinearOrder I][Fintype I][LinearOrder J][Fintype J]
variable {n:ℕ}[NeZero n]
def atCell (x:DeckIn n X Y) (i : ℕ) : Cell X Y:= ((recur x.1 i,recur x.1 (i+1)),recur x.2 i)
lemma atCell_full (x:DeckIn n X Y): atCell x n=atCell x 0:=by simp [atCell,recur]
@[fun_prop] lemma atCell_cont (i:ℕ): Continuous (fun x:DeckIn n X Y=> atCell x i) := by unfold atCell recur; fun_prop
@[fun_prop] lemma atCell_meas (i:ℕ): Measurable (fun x:DeckIn n X Y=> atCell x i):=by unfold atCell recur; fun_prop
structure Batch (n:ℕ)(I J:Type*) [LinearOrder I][LinearOrder J][Fintype J][Fintype I] where
 site : Many n (I↪J)
 grade : Finset J
 post : Finset I
 rider : Pairwise fun i j=>Disjoint (lows (site i)) (lows (site j))
 care (i x): site i x∈ grade ↔ x∈ post
namespace Batch
variable [Fintype B] (R : Batch n I J) (F : Many n (Film X Y B I)) (c: DeckIn n X Y)
abbrev place (i:ℕ):=into (recur R.site i)
abbrev slice (i:ℕ):=lows (recur R.site i)
abbrev screen (i : ℕ) := atCell c i -- binder not Batch rm
lemma place_exp (A : FC I) (i:ℕ) : R.place i (exp A)=exp (R.place i A):=by
 letI : NormedAlgebra ℚ (FC I) := NormedAlgebra.restrictScalars ℚ ℝ _; letI : NormedAlgebra ℚ (FC J):= NormedAlgebra.restrictScalars ℚ ℝ _; exact map_exp _ (into_cont _) _
lemma place_real (i:ℕ)(z:ℝ)(A:FC I): place R i (z • A)=z • place R i A:= map_smul ((place R i).toLinearMap.restrictScalars ℝ) _ _
lemma place_iso: lonely (slice R) n := by
 intro i v j t; unfold slice recur; apply R.rider; intro x; have hk:= Fin.val_cast_of_lt v; rw [x, Fin.val_cast_of_lt (t.trans v)] at hk; omega
lemma place_state (i:ℕ)(A:FC I) : place R i A R.grade R.grade=A R.post R.post:=into_state _ _ (R.care _)
def core (i:ℕ):= R.place i ((recur F i).core (atCell c i))
def leg (i:ℕ) (d:Bool)(b:B):=R.place i ((recur F i).side d b (atCell c i))
def feet (i:ℕ) := ∑ x, outer n i true • (leg R F c i true x* leg R F c (i+1) false x)
def needle (i:ℕ) := R.place i ((recur F i).mark (atCell c i))
def root (i:ℕ):= R.place i ((recur F i).seed (atCell c i))
lemma needle_home (i:ℕ): Sector (slice R i) false (needle R F c i):= sector_in _ ((recur F i).sectorM _)
lemma root_home (i:ℕ): Sector (slice R i) false (root R F c i):= sector_in _ ((recur F i).sectorV _)
lemma tower_eq {t:ℝ}(v: 0 ≤ t)(u:2 ≤ n) : Trotter.braid (core R F c) (feet R F c) n t= whole n (fun i x y=> R.place i ((recur F i).stretch (atCell c i) t x y)) := by
 let a (j:ℕ) := exp (t • core R F c j); have ha(j:ℕ): R.place j ((recur F j).ready (atCell c j) t)=a j:= by rw [Film.ready, R.place_exp,R.place_real]; rfl
 let p(j:ℕ)(b:Bool) : Option B→ FC I:= (recur F j).port (Real.sqrt t) (atCell c j) b
 let f(j:ℕ)(k:Option B):= R.place j (p j false k)
 let g(j:ℕ)(k:Option B):= R.place j (p j true k)
 have hk : f n = f 0 := by funext i; unfold f place p; rw [recur_full, recur_full, atCell_full]
 have hp(i:ℕ): 1 + t • feet R F c i = ∑ x:Option B, outer n i x.isSome • (g i x * f (i+1) x):=by
    rw [Fintype.sum_option]; have hv(i:ℕ) : outer n i false=1:=by by_cases k:i+1=n <;> simp [outer,k,chord]
    unfold g f feet p; simp_rw [smul_sum]; simp only [Option.isSome_none,Option.isSome_some,Film.port,hv,map_one,mul_one,one_smul]; congr 1; refine sum_congr rfl fun i _=> ?_
    rw [place_real,place_real, Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul, ←pow_two, Real.sq_sqrt v, smul_comm]; rfl
 have hx(i):bind (a i) Option.isSome (f i) (g i)=fun x y=> R.place i ((recur F i).stretch (atCell c i) t x y):=by
    funext x y; unfold Film.stretch bind; rw [map_mul, map_smul,map_mul,ha]
 unfold Trotter.braid; simp_rw [hp]; rw [woven _ Option.isSome u f g (slice R) a (R.place_iso) ?_ hk ?_ ?_]; swap
 · exact fun i t=> ha i ▸ sector_in _ (Heat.sector_exp (Heat.sector_real _ ((recur F i).sectorC _)))
 swap; · exact fun i a x=>⟨sector_in _ ((recur F i).port_grade ..),sector_in _ ((recur F i).port_grade ..)⟩
 swap; · intro x y; unfold f g; rw [←map_mul,←map_mul,←map_smul]; exact congrArg (R.place 0) ((recur F 0).spare ..)
 simp_rw [hx]
variable (k:ℕ)
private lemma late (i:ℕ)(G:Board I (Option B))(k:ℕ)(x y:Leaf k B): R.place i (issue Option.isSome G k x y)= issue Option.isSome (fun x y=> R.place i (G x y)) k x y := by
 induction k with
 | zero=> exact map_one _
 | succ k ih=> simp [issue,map_smul,ih,map_mul]
abbrev unitT (k:ℕ) := (k+1:ℝ)⁻¹
def wgt := ∏ i:Fin n,(F i).weight (atCell c i.val)
def layerNum (k:ℕ) := wgt F c * (run (needle R F c) n*Trotter.plays (core R F c) (feet R F c) n k*run (root R F c) n) R.grade R.grade
local notation "ℱ" i:max => recur F i
lemma read_layer (h:2≤n) : layerNum R F c k= ∑ x:Many n (Leaf (k+1) B),∏ i:Fin n,(F i).evaluate (unitT k) R.post (k+1) (x i) (x (i+1)) (atCell c i.val) := by
 let t:=unitT k; let Q(i:ℕ):=(recur F i).stretch (atCell c i) t
 let A(i:ℕ)(x y:Option B):= R.place i (Q i x y); let T (i:ℕ):= issue Option.isSome (A i) (k+1)
 let P:= Stack.parity (Option.isSome (α:=B)) (k+1)
 have hp: ∀ i<n,∀ x y:Option B,Sector (slice R i) (x.isSome.xor y.isSome) (A i x y):= fun i _ x y=> sector_in _ ((ℱ i).berth t _ _ _)
 unfold layerNum Trotter.plays; rw [tower_eq R F c (t:=unitT k) (by unfold unitT; positivity) h, whole_power Option.isSome _ A (slice R) hp (R.place_iso)]; rw [whole_mark P n T (slice R) (fun i h=> issue_here Option.isSome (A i) (hp i h) _) R.place_iso]; swap; · exact fun i _=> needle_home ..
 swap; · exact fun i _=> root_home ..
 rw [mul_sum]; refine sum_congr rfl fun x _=> ?_; unfold wgt; rw [←prod_mul_distrib]; refine prod_congr rfl fun i _=> ?_
 apply congrArg; unfold T; rw [←late (G:=Q i.val)]; unfold needle root; rw [←map_mul, ←map_mul,R.place_state]; unfold Film.lace; simp [Q,recur]; rfl
end Batch
end YM.CF.Buffered.Stack
#print axioms YM.CF.Buffered.Stack.Batch.read_layer
