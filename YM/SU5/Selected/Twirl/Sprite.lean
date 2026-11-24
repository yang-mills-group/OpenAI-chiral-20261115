import YM.SU5.Selected.Twirl.Tide
import YM.CF.Lattice.Reference
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Crest.Airy
open Function Filter Topology Metric NormedSpace Lattice Laurent Bloch Next.Free MeasureTheory
open Ember Jill Fir Shore Real Finset Fock Rush Lat
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ComplexOrder
local notation "I"=>Complex.I
local notation "φ" => 2 * π
local instance : Fact (0<φ):= ⟨piRank⟩
attribute [local instance] opCStarAlgebra
local instance : CompactSpace grounds:= isCompact_iff_compactSpace.mp groundsCompact
-- assemble unnormalized spine first. `Coined` expects covector Leg with bound 1 => scale later.
variable (N:Side) (n p:ℕ)(G D:Side)(g:8≤G.val)(e:n≥4)
local notation "Y"=> artisans G n p e
local notation "V"=> plinth G n p e
local notation "Fp"=>children G n p
local notation "ρ"=> Real.exp (-(1/2))
private lemma pink {n v:Type*}[Fintype n][DecidableEq n][Fintype v][DecidableEq v](ε δ C:ℝ)(hp:0≤ε)(cv:ε≤1){A X B Z:WRect n v}{P:Op n}(h:‖A‖≤C)(p:‖B‖≤C)(g:‖Aᴴ*B-1‖≤δ)(k:‖P‖≤1)(t:‖P*B‖ ≤ ε)(eX:‖A-X‖ ≤ ε)(eZ:‖B-Z‖≤ε) : ‖X‖≤ C+1 ∧ ‖Z‖ ≤ C+1 ∧ ‖Xᴴ*Z-1‖≤δ+ε*(2*C+1) ∧ ‖P*Z‖≤2*ε:=by
 have tR:0≤C:= (norm_nonneg A).trans h; have e₁:‖X-A‖≤ε:= (norm_sub_rev ..).trans_le eX; have e₂:‖Z-B‖≤ε:= (norm_sub_rev ..).trans_le eZ;
 have ht:‖X‖ ≤ C+1:=by linarith [norm_le_norm_sub_add X A]; -- scope
 have hu:‖Z‖ ≤ C+1:=by linarith [norm_le_norm_sub_add Z B];
 refine ⟨ht,hu,?_,?_⟩
 · have he:Xᴴ*Z-1=(Aᴴ*B-1)+(X-A)ᴴ*B + Xᴴ*(Z-B):=by rw [Matrix.conjTranspose_sub,Matrix.sub_mul,Matrix.mul_sub]; abel
   have hx: ‖(X-A)ᴴ*B‖≤ ε*C:= (Matrix.l2_opNorm_mul ..).trans (mul_le_mul ((Matrix.l2_opNorm_conjTranspose ..).trans_le e₁) p (norm_nonneg _) hp)
   have hy: ‖Xᴴ*(Z-B)‖ ≤ (C+1)*ε:= (Matrix.l2_opNorm_mul ..).trans (mul_le_mul ((Matrix.l2_opNorm_conjTranspose ..).trans_le ht) e₂ (norm_nonneg _) (by positivity))
   rw [he]; apply (norm_add_le ..).trans; exact (add_le_add ((norm_add_le ..).trans (add_le_add g hx)) hy).trans_eq (by ring)
 apply (norm_le_norm_sub_add _ (P*B)).trans; rw [←Matrix.mul_sub]; exact (add_le_add ((Matrix.l2_opNorm_mul ..).trans ((mul_le_of_le_one_left (norm_nonneg _) k).trans e₂)) t).trans_eq (by ring)

private lemma tintB (f:Torch→ℂ)(i:ℤ)(h:Color (fun _=>True) f): Color (fun v:Cover=> v 3=i) (fun w=> fourier i (lapse w) * f (pier w)):=by
 let G(g:Torch→ℂ)(w:Coast):= fourier i (lapse w)*g (pier w); change Color _ (G f)
 induction h with
 | zero=> exact (show G 0=0 from (by funext w; unfold G; simp)).symm ▸ Color.zero
 | mode v p => have he:G (prefixG v)=prefixG (Ε v i):= by ext1 w; unfold G; conv_rhs => rw [← to_whole w,tintMono]; rw [mul_comm];
               exact he.symm ▸ .mode _ (by simp)
 | smul s p v=> rw [show G (s •_)=s • G _ from ?_]; exact v.smul _; ext1 w; unfold G; simp; ring
 | add p s a b=> rw [show G (_+_)=G _+G _ from ?_]; exact a.add b; ext1 w; unfold G; simp [mul_add]

def rondo(f:Torch→ℂ)(x: Coast):Wq p:= f (pier x) • nails n p (lapse x)
lemma rondo_est (f:Torch→ℂ) (h:Color (fun _=>True) f)(a:SpinIdx)(i:Fin p) : Color (Qlate n p a i) (fun x=> rondo n p f x a i):=by
 unfold rondo nails forge; simp_rw [Matrix.smul_apply,Matrix.of_apply,smul_eq_mul]; by_cases p:2=a
 · subst a; simp_rw [if_true]; conv in (_*_)=> rw [mul_comm]
   exact Color_mono (tintB f _ h) fun i z => ⟨rfl,z⟩
 simp_rw [if_neg p,mul_zero]; exact Color.zero
-- approximate with spine laws preserved exactly, for later sharing. fixed p (need before CHOICE)
private lemma life (n p:ℕ): ∃ C>(0:ℝ),∀ x:roundC, ‖nails n p x‖ ≤ C:=by
 obtain ⟨C,h⟩:= (isCompact_range (f:=fun x:roundC=>‖nails n p x‖) (nails_c n p).norm).bddAbove; exact ⟨max 1 C,lt_of_lt_of_le (by norm_num) (le_max_left ..),fun i=> (h ⟨i,rfl⟩).trans (le_max_right ..)⟩
include g
lemma rondos (ε:ℝ)(k:0<ε): ∃ f:Torch→ℂ, Color (fun _=>True) f∧ ∀ x, ‖Fp x - rondo n p f x‖ ≤ ε :=by
 obtain ⟨C,h,q⟩:=life n p; obtain ⟨z,u,v⟩:=fromStone (Complex.continuous_ofReal.comp (soap_c G g)) (ε/C) (by positivity)
 refine ⟨z,u,fun x=>?_⟩; unfold children rondo; rw [←sub_smul,norm_smul]; exact (mul_le_mul (v _) (q _) (norm_nonneg _) (by positivity)).trans_eq (div_mul_cancel₀ _ h.ne')
lemma rondeau(ε:ℝ)(k:0<ε) : ∃ (x:Torch→ℂ)(y:Coast→Wq p)(w:ℕ),(∀ i j,Color (fun v=> Piece v w∧ Qlate n p i j v) (fun t=> rondo n p x t i j)) ∧ (∀ i j,Color (fun v=> Piece v w∧ Qearly p i j v) (fun t=> y t i j)) ∧∀ z, ‖Fp z-rondo n p x z‖ ≤ ε ∧ ‖Y z-y z‖ ≤ ε:=by
 obtain ⟨x,X,z⟩:= rondos n p G g ε k; obtain ⟨y,A,b⟩:= coast_approx _ _ (before_plasma n p G g e) ε k
 obtain ⟨w,c,d⟩:= ((eventually_all.mpr fun i=> eventually_all.mpr fun j=> hedge (rondo_est n p x X i j)).and (eventually_all.mpr fun i=> eventually_all.mpr fun j=> hedge (A i j))).exists; exact ⟨x,y,w,c,d,fun p=>⟨z p,b p⟩⟩
include g e
lemma starlight : ∃ C> (0:ℝ),∃ K:ℝ,0<K∧∀ (D:Side)(ε:ℝ),0<ε→ε≤1→∃ (w:ℕ)(x:Torch→ℂ)(Z: Coast→ Wq p),Frame (G:=G) n p (rondo n p x) Z D w (K*ρ^D.val+ε*(2*C+1)) (2*ε) (C+1) :=by
 obtain ⟨K,hK,v⟩:= coin n p G g e; obtain ⟨C,hc,gC⟩:= general_bound n p G g e -- e not in binder; include e
 refine ⟨C,hc,K,hK,fun D ε pε vε=>?_⟩; obtain ⟨X,Z,R,f,b,q⟩:=rondeau n p G g e ε pε; refine ⟨R,X,Z,f,b,?_⟩; filter_upwards [backend_price n p G g e ε pε] with M y N v' i _ x k; -- implicit
 apply pink ε (K*ρ^D.val) C pε.le vε (A:=hire p Fp x) (B:= hire p Y x) (P:=1-tip N M)
 · apply (Matrix.l2_opNorm_mul _ (mask x)).trans; apply (mul_le_of_le_one_right (norm_nonneg _) (mask_toll x k.mono)).trans; exact freeze_norm hc.le (fun i=> (gC (brim N i)).1)
 · apply (Matrix.l2_opNorm_mul _ (mask x)).trans; apply (mul_le_of_le_one_right (norm_nonneg _) (mask_toll x k.mono)).trans; exact freeze_norm hc.le (fun i=> (gC (brim N i)).2.2)
 · exact v N D x k -- tune
 · exact (tipped N M).one_sub.norm_le _
 · unfold hire; rw [←Matrix.mul_assoc]; apply (Matrix.l2_opNorm_mul ..).trans; apply (mul_le_of_le_one_right (norm_nonneg _) (mask_toll x k.mono)).trans; exact y N
 · unfold hire; rw [←Matrix.sub_mul,← freeze_sub]; refine (Matrix.l2_opNorm_mul ..).trans ?_; exact (mul_le_of_le_one_right (norm_nonneg _) (mask_toll x k.mono)).trans (freeze_norm pε.le (fun i=>(q (brim N i)).1)) -- first `any_goals` hazard
 unfold hire; rw [←Matrix.sub_mul,← freeze_sub]; refine (Matrix.l2_opNorm_mul ..).trans ?_; exact (mul_le_of_le_one_right (norm_nonneg _) (mask_toll x k.mono)).trans (freeze_norm pε.le (fun i=>(q (brim N i)).2))
end YM.CF.Crest.Airy
open YM.CF.Crest.Airy
#print axioms starlight
