import YM.SU5.Selected.Airy.Approve
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
private lemma tender {n v:Type*}[Fintype n][DecidableEq n][Fintype v][DecidableEq v](ε δ C:ℝ)(hp:0≤ε)(cv:ε≤1){A X B Z:WRect n v}{P:Op n}(h:‖A‖≤C)(p:‖B‖≤C)(g:‖Aᴴ*B-1‖≤δ)(k:‖P‖≤1)(t:‖P*B‖ ≤ ε)(eX:‖A-X‖ ≤ ε)(eZ:‖B-Z‖≤ε) : ‖X‖≤ C+1 ∧ ‖Z‖ ≤ C+1 ∧ ‖Xᴴ*Z-1‖≤δ+ε*(2*C+1) ∧ ‖P*Z‖≤2*ε:=by
 have tR:0≤C:= (norm_nonneg A).trans h; have e₁:‖X-A‖≤ε:= (norm_sub_rev ..).trans_le eX; have e₂:‖Z-B‖≤ε:= (norm_sub_rev ..).trans_le eZ;
 have ht:‖X‖ ≤ C+1:=by linarith [norm_le_norm_sub_add X A]; -- scope
 have hu:‖Z‖ ≤ C+1:=by linarith [norm_le_norm_sub_add Z B];
 refine ⟨ht,hu,?_,?_⟩
 · have he:Xᴴ*Z-1=(Aᴴ*B-1)+(X-A)ᴴ*B + Xᴴ*(Z-B):=by rw [Matrix.conjTranspose_sub,Matrix.sub_mul,Matrix.mul_sub]; abel
   have hx: ‖(X-A)ᴴ*B‖≤ ε*C:= (Matrix.l2_opNorm_mul ..).trans (mul_le_mul ((Matrix.l2_opNorm_conjTranspose ..).trans_le e₁) p (norm_nonneg _) hp)
   have hy: ‖Xᴴ*(Z-B)‖ ≤ (C+1)*ε:= (Matrix.l2_opNorm_mul ..).trans (mul_le_mul ((Matrix.l2_opNorm_conjTranspose ..).trans_le ht) e₂ (norm_nonneg _) (by positivity))
   rw [he]; apply (norm_add_le ..).trans; exact (add_le_add ((norm_add_le ..).trans (add_le_add g hx)) hy).trans_eq (by ring)
 apply (norm_le_norm_sub_add _ (P*B)).trans; rw [←Matrix.mul_sub]; exact (add_le_add ((Matrix.l2_opNorm_mul ..).trans ((mul_le_of_le_one_left (norm_nonneg _) k).trans e₂)) t).trans_eq (by ring)

abbrev hire {N:Side}(X:Coast→Wq p){v:Type*}[Fintype v](x:v→ Site N×Fin p) := freeze (X ∘brim N) * mask x -- no p? Lean
structure Frame {G:Side} (n p:ℕ)(X Z: Coast→Wq p)(D:Side)(w:ℕ)(δ η C:ℝ): Prop where
    late : ∀ i j, Color (fun k=> Piece k w∧Qlate n p i j k) (fun t=> X t i j)
    early : ∀ i j, Color (fun k=> Piece k w∧Qearly p i j k) (fun t=> Z t i j)
    ticket : ∀ᶠ M:Jill.Male in mtn,∀ (N:Side){v:Type}[Fintype v][DecidableEq v],∀ (x:v→ Site N×Fin p), Beacons G D p x→
       let F':= hire p X x; let V':= hire p Z x; ‖F'‖ ≤ C∧‖V'‖ ≤ C∧‖F'ᴴ * V'-1‖ ≤ δ ∧ ‖(1-tip N M)* V'‖≤ η

include g e
lemma looked : ∃ C> (0:ℝ),∃ K:ℝ,0<K∧∀ (D:Side)(ε:ℝ),0<ε→ε≤1→∃ (w:ℕ)(X Z: Coast→ Wq p),Frame (G:=G) n p X Z D w (K*ρ^D.val+ε*(2*C+1)) (2*ε) (C+1) :=by
 obtain ⟨K,hK,v⟩:= coin n p G g e; obtain ⟨C,hc,gC⟩:= general_bound n p G g e -- e not in binder; include e
 refine ⟨C,hc,K,hK,fun D ε pε vε=>?_⟩; obtain ⟨X,Z,R,f,b,q⟩:=stubs n p G g e ε pε; refine ⟨R,X,Z,f,b,?_⟩; filter_upwards [backend_price n p G g e ε pε] with M y N v' i _ x k; -- implicit
 apply tender ε (K*ρ^D.val) C pε.le vε (A:=hire p Fp x) (B:= hire p Y x) (P:=1-tip N M)
 · apply (Matrix.l2_opNorm_mul _ (mask x)).trans; apply (mul_le_of_le_one_right (norm_nonneg _) (mask_toll x k.mono)).trans; exact freeze_norm hc.le (fun i=> (gC (brim N i)).1)
 · apply (Matrix.l2_opNorm_mul _ (mask x)).trans; apply (mul_le_of_le_one_right (norm_nonneg _) (mask_toll x k.mono)).trans; exact freeze_norm hc.le (fun i=> (gC (brim N i)).2.2)
 · exact v N D x k -- tune
 · exact (tipped N M).one_sub.norm_le _
 · unfold hire; rw [←Matrix.mul_assoc]; apply (Matrix.l2_opNorm_mul ..).trans; apply (mul_le_of_le_one_right (norm_nonneg _) (mask_toll x k.mono)).trans; exact y N
 · unfold hire; rw [←Matrix.sub_mul,← freeze_sub]; refine (Matrix.l2_opNorm_mul ..).trans ?_; exact (mul_le_of_le_one_right (norm_nonneg _) (mask_toll x k.mono)).trans (freeze_norm pε.le (fun i=>(q (brim N i)).1)) -- first `any_goals` hazard
 unfold hire; rw [←Matrix.sub_mul,← freeze_sub]; refine (Matrix.l2_opNorm_mul ..).trans ?_; exact (mul_le_of_le_one_right (norm_nonneg _) (mask_toll x k.mono)).trans (freeze_norm pε.le (fun i=>(q (brim N i)).2))
omit g e
-- concrete support below separated. Note result includes all shifts (incl y columns in visible FootprintY) in one tile chosen *after* fees. Boolean chirality signs as actual. need transportation. 
variable {N G n p D} {δ ε R:ℝ}{w:ℕ}{X Z:Coast→ Wq p}(h:Frame (G:=G) n p X Z D w δ ε R){v:Type}[Fintype v][DecidableEq v](x:v→ Site N×Fin p)
include h
lemma Frame.turnY (a:SpinIdx)(y:Site N)(i:v) (p':hire p Z x (y,a) i≠0): ∃ k:Cover, y=(x i).1+wrap N k ∧ Piece k w ∧ (a∈plusHalf→ ∃ i:Fin p,k 3=strikeE p i):=by
 unfold hire at p'; rw [mask_mem,← Prod.eta (p:=x i)] at p'; obtain ⟨k,⟨t,f⟩,hz⟩:= leaves y _ _ _ (h.early a (x i).2) p'
 refine ⟨-k,?_,?_,?_⟩; · rw [hz,map_neg,sub_eq_add_neg]
 · exact fun i=> (Int.natAbs_neg _).trans_le (t i)
 intro u; obtain ⟨v,l⟩:= f u; exact ⟨v,by simp [l]⟩
lemma Frame.turnX (a:SpinIdx)(y:Site N)(i:v) (p':hire p X x (y,a) i≠0): ∃ k:Cover, y=(x i).1+wrap N k ∧ Piece k w ∧ a=2∧ k 3=strikeL n p (x i).2:=by
 unfold hire at p'; rw [mask_mem,← Prod.eta (p:=x i)] at p'; obtain ⟨k,⟨t,f,l⟩,hz⟩:= leaves y _ _ _ (h.late a (x i).2) p' -- ⟨t,⟨f,l⟩⟩ autosubst
 refine ⟨-k,?_,?_, f,by simp [l]⟩; · rw [hz,map_neg,sub_eq_add_neg]
 exact fun i=> (Int.natAbs_neg _).trans_le (t i)
end YM.CF.Crest.Airy
open YM.CF.Crest.Airy
#print axioms Frame.turnY
#print axioms Frame.turnX
#print axioms looked
