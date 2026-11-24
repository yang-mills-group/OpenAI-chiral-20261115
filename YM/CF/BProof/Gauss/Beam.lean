import YM.CF.BProof.Gauss.Bin
import YM.CF.BProof.Prox.Route

/- Spectrum and range of actual T change. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Gauss.Bin
open Function Filter RG Wilson Lattice Finset Work Micro MeasureTheory Mag Angular Angular.Yard Charge Charge.Form Matrix Roll Precision RealM SignScalar
open scoped Topology BigOperators Classical Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
variable {I:Type*}[Fintype I][DecidableEq I]
variable (p a r:ℝ)(n:ℕ)(H: Pool I)(U:Move I)(d:I→ℝ)

def ray (H:Pool I) := 1 - p⁻¹ • H
def slab := pay p • ∑ i∈ Finset.range n, SignScalar.c i • ray p H^i
def beam := slab p n H+ (1-tap p n 1) • 1
lemma ray_dial : ray p (dial U d) = dial U (afford p ∘ d):= by rw [ray,← dial_one U,← dial_smul,← dial_sub]; rfl
lemma slab_dial : slab p n (dial U d)=dial U (tap p n ∘ d):= by
 unfold slab; simp_rw [ray_dial,← dial_pow, ←dial_smul, dial_sum, ←dial_smul]; congr; ext i; simp [tap,fee,Finset.sum_apply] -- tune
lemma beam_dial : beam p n (dial U d)=dial U (fare p n ∘ d):= by
 rw [beam,slab_dial, ← dial_const U,←dial_add]; rfl

structure Qualified (p a:ℝ)(n:ℕ): Prop where
 above : 1 ≤ p
 below : a ≤ 1
 pos : 0<a
 start : 0<n
 tail : Bin.tail p a n ≤ 1
variable {p a} (q:Qualified p a n)(h: H.IsHermitian)(g: Numeric H a p)
include q h g
lemma sun : let T:=beam p n H; T.IsHermitian∧ Numeric T (pay p) (maximum a) ∧ ‖T‖≤maximum a ∧ ‖1-Tᵀ * H*T‖≤scope p a n := by
 obtain ⟨U,d,rfl,hA⟩:= dial_receipt H h g -- rfl? structure
 let P:=pay p; let f:= fare p n ∘ d; let M:= maximum a; have ho:=q.above; have ha:=q.below; have hv:=q.pos
 have hM := max_ge ho hv ha; have hp:=pay_pos ho hv ha
 have hf(i): P ≤ f i ∧ f i ≤ M := fares_bound _ ho hv ha q.start q.tail (hA i).1 (hA i).2
 dsimp only; rw [beam_dial]; refine ⟨dial_reflect .., dial_numeric U f (fun i=>(hf i).1) (fun i=>(hf i).2),RealM.norm_le U f (zero_le_one.trans hM) (fun i=> ?_),?_⟩
 · rw [abs_of_nonneg (hp.le.trans (hf i).1)]; exact (hf i).2
 have hx: (dial U f)ᵀ=dial U f:= by simpa using (dial_reflect U f).eq
 change ‖1-(dial U f)ᵀ*dial U d*dial U f‖≤_; rw [hx, ← dial_mul, ←dial_mul, ←dial_one U, ←dial_sub]; refine RealM.norm_le _ _ ?_ (fun i=>disburse n ho hv ha q.start q.tail (hA i).1 (hA i).2)
 have hz:0≤ tail p a n:= (abs_nonneg _).trans (shift_size n ho hv ha (v:=le_rfl) (u:=ha.trans ho))
 unfold scope; positivity
omit q h g
section
variable {p':Type*}[Fintype p']{B:Prox.Base p'}(p)
lemma fareVia {X:Type*}(S:Prox.Scope X p') (F:B.Index I) (H:X→ Pool I){k:ℕ}(h:Prox.Via F S H k) : Prox.Via F S (fun x=>beam p n (H x)) (k*n) := by
 let A(x:X) :=ray p (H x); let Z(k) := SignScalar.c k • (A^k); let T :=∑ i∈ Finset.range n,Z i
 have hx:Prox.Via F S A k := (Prox.Via.one (S:=S) (F:=F)).sub (h.pi_smul p⁻¹)
 have he: Prox.Via F S T (k*n):=Prox.Via.sum _ _ (fun i hi => ((hx.pow i).pi_smul _).le (Nat.mul_le_mul_left _ (mem_range.mp hi).le))
 rw [show (fun x=> beam p n (H x))= pay p • T+(1-tap p n 1) • (1:X→ Pool I) from ?_]; exact (he.pi_smul (pay p)).add (Prox.Via.one (X:=X) (k:=k*n) |>.pi_smul (1-tap p n 1))
 ext1 x; unfold beam slab; simp only [Pi.add_apply,Pi.smul_apply,T,Z,Finset.sum_apply,Pi.pow_apply]; rfl
end
-- severe row identity
abbrev Badge (c:ℝ)(i:I)(T:Pool I): Prop:=∀ j,T i j=(c • (1:Pool I)) i j
namespace Badge
variable (p) {a b:ℝ}{X Y:Pool I}{i:I}
lemma id (i:I): Badge 1 i (1:Pool I) :=by intro j; rw [one_smul]
lemma add (x: Badge a i X)(y:Badge b i Y): Badge (a+b) i (X+Y):=by intro j; rw [Matrix.add_apply,add_smul,Matrix.add_apply,x,y]
lemma sub (x: Badge a i X)(y:Badge b i Y): Badge (a-b) i (X-Y):=by intro j; rw [Matrix.sub_apply,sub_smul,Matrix.sub_apply,x,y]
lemma mon (x:Badge a i X): Badge (p*a) i (p • X):=by intro j; rw [Matrix.smul_apply,x,mul_smul,Matrix.smul_apply]; exact rfl
lemma kit (x: Badge a i X)(y:Badge b i Y): Badge (a*b) i (X*Y) :=by intro j; rw [Matrix.mul_apply,sum_eq_single i]; rw [x,y]; simp [mul_assoc]; intro k hk h; simp [x,Matrix.one_apply,Ne.symm h]; simp
lemma seq (x: Badge a i X)(b:ℕ): Badge (a^b) i (X^b):=by induction b with|zero=>rw [pow_zero,pow_zero]; exact id _|succ n ih=> rw [pow_succ,pow_succ]; exact ih.kit x
lemma lot {J:Type*}(Z:Finset J)(x:J→ℝ)(X:J→Pool I)(h:∀ j∈Z,Badge (x j) i (X j)) : Badge (∑ j∈Z,x j) i (∑ j∈ Z,X j):=by
 induction Z using Finset.induction_on with|empty=> simp only [sum_empty]; intro j; rw [zero_smul]|insert a Z u ih=> rw [sum_insert u,sum_insert u]; exact (h a (mem_insert_self ..)).add (ih (fun j h' =>h j (mem_insert_of_mem h')))
lemma carries (x:Badge a i X)(n:ℕ): Badge (fare p n a) i (beam p n X):= by
 unfold fare; exact Badge.add (Badge.mon (pay p) (Badge.lot _ _ _ (fun j _=> Badge.mon _ (Badge.seq ((Badge.id i).sub (Badge.mon p⁻¹ x)) j)))) (by simpa using Badge.mon (1-tap p n 1) (Badge.id i))

end Badge
end YM.CF.BProof.Gauss.Bin
