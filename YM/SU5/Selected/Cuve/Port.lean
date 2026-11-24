import YM.SU5.Selected.Cuve.Skill
import YM.SU5.Selected.Lantern.Winter
import YM.SU5.FiniteGaugeData.Pannier.FoyerSeat
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Pannier.Chancel.Cuve
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest Rail Airy Lantern
open Lantern.Bulb
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 24000
local notation "I"=> Complex.I
local notation "PS" N:max => cutM (Tset N)
/-! # Neumann budget with *uniform* cutoff Snow. canopy construction without differentiating
in all coordinates. ---/ -- tune close
variable {n k t w:ℕ} {N:Side} (M:Tulip.Male)
local notation "F" => spar 4 M (1: Pane N)
local notation "W" s:max S:max=> Lattice.halo s S
variable {δ γ ε R C:ℝ}
private lemma farther (S:Finset (Seat N)) (k s:ℕ): Distant k (W (k+s) S)ᶜ (W s S):=by
 intro i e j v; by_contra! h; obtain ⟨x,p,hp⟩:=halo_spec.mp v; rw [separation_comm] at h; exact (mem_compl.mp e) (halo_spec.mpr ⟨x,p,(separation_triangle x j i).trans ((Nat.add_le_add hp h.le).trans_eq (Nat.add_comm ..))⟩)
-- τ forecast. weighted even K≥1 choose d. 
variable (q:Type*)[Fintype q][DecidableEq q]
variable (X Z:WRect (Single N) q)(T:Finset (Seat N))(x:Contained (modesIn N T) X)
 (u:0≤δ)(wn:Winter 4 δ N γ w ε)(p:IsStarProjection (spar 4 M (1:Pane N)))
 (v:0 ≤ ε)(c:‖X‖ ≤ C)(h:PS N*Z=X)(g:spar 4 M (1:Pane N)*Z=Z)
local notation "Y" => ruin M N
local notation "λa" i:max => Z-Y^i*Z
omit h g
include v u wn x in
private lemma w_flow (Q:WRect (Single N) q)(y:ℕ)(f:Contained (modesIn N (W y T)) Q):
      ‖Vo ((W (w+y) T)ᶜ) * (F*Q)‖ ≤ ε*‖Q‖:=by
 let P':= Vo ((W (w+y) T)ᶜ); change ‖P'*(F*Q)‖≤_; rw [show P' * (F*Q)= (P'* F* Vo (W y T))*Q from ?_]; apply charge_mul _ le_rfl; exact hearthB_cross wn false M (guard0 u) (farther T w y)
 rw [Matrix.mul_assoc,show Vo (W y T)*Q=Q from f,Matrix.mul_assoc] -- tune P
lemma aura (Q:WRect (Single N) q)(h:Contained (modesIn N T) Q) : Contained (modesIn N T) ((1-PS N)* Q):=by unfold Contained; rw [←Matrix.mul_assoc, ← dim_cut (Tset N), (cutLane ..).eq,Matrix.mul_assoc,h];
lemma rising (A:Finset (Seat N)) (Q: WRect (Single N) q):Contained (modesIn N A) (Vo A*Q):= by unfold Contained; rw [←Matrix.mul_assoc]; exact congrArg (fun z:_=> z * Q) (cutM_idp _).isIdempotentElem
include p h g in
lemma newsletter(y:ℕ): λa (y+1)= F * (X + (1-PS N)*(λa y)):=by
 rw [pow_succ']; unfold ruin; simp only [Matrix.mul_add, Matrix.mul_sub, ←Matrix.mul_assoc]; rw [Matrix.sub_mul (F * 1) (_ * PS N) Z, Matrix.mul_one, g, Matrix.mul_assoc (F) (PS N) Z,h]; abel -- tune occurrence
-- recurrence test
include c p h g x u wn v
private lemma gust(y:ℕ): ∃ Q: WRect (Single N) q, Contained (modesIn N (W (y*w) T)) Q∧ ‖Q‖ ≤ y*C ∧ ‖λa y-Q‖ ≤ (y:ℝ)^2 * ε * C:=by
 have hQ:0 ≤ C:= (norm_nonneg _).trans c; have ht:IsStarProjection (1-PS N):=(cutM_idp _).one_sub
 induction y with
 | zero=> exact ⟨0, (show Contained _ _ from (show cutM _*(0:WRect _ q)=0 from Matrix.mul_zero _)), by simp,by simp⟩ -- tune
 | succ y ih=>
    obtain ⟨D,q,g',t⟩:=ih; let R:=X+(1-PS N)*D; let V:= F * R; let TS:=W ((y+1)*w) T; let Y':=Vo TS* V; have he : (y+1)*w=w+y*w:=by ring
    let b:=W (y*w) T; have hv:‖R‖ ≤ (↑(y+1:ℕ):ℝ)*C:= ((norm_add_le ..).trans (add_le_add c (bound_shift ht g'))).trans_eq (by push_cast; ring); have hz:= (bound_shift p hv); have hK:Contained (modesIn N b) R:= (x.grows (modes_monotone (fun i h=>halo_spec.mpr ⟨i,h,(separation_self _).trans_le (Nat.zero_le _)⟩))).add (aura _ b D q) -- args.
    refine ⟨Y',rising ..,bound_shift (cutM_idp _) hz,?_⟩; rw [show λa (y+1)- Y'=F*((1-PS N)*((λa y)-D)) + Vo TSᶜ * V from ?_]; apply (norm_add_le ..).trans;
    have hx:‖Vo TSᶜ* V‖≤ ε*((↑(y+1:ℕ):ℝ)*C):=by unfold TS; rw [he]; exact (w_flow M _ X T x u wn v R _ hK).trans (mul_le_mul_of_nonneg_left hv v);
    have hl:=(bound_shift p (bound_shift ht t)); refine le_trans (add_le_add hl hx) ?_; push_cast; nlinarith only [mul_nonneg (mul_nonneg (Nat.cast_nonneg (α:=ℝ) y) v) hQ] -- tune
    rw [newsletter M _ X Z p h g,Vo_neg]; unfold Y' V R; simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_add,Matrix.one_mul]; abel
-- manufacturing exact upper trunc
lemma busy (y:ℕ)(V:Finset (Seat N))(e:W (y*w) T⊆ V) (d:‖Y^y * Z‖≤R):
      ‖Z-Vo V*Z‖≤ (y:ℝ)^2*ε*C+R:=by
 obtain ⟨Q,hK,hp,hx⟩:=gust M q X Z T x u wn p v c h g y; let T':=Vo V; let U:=1-T'; have hf:IsStarProjection U:=(cutM_idp _).one_sub; have he:T'*Q=Q:=hK.grows (modes_monotone e); rw [show Z-Vo V*Z= U*((λa y)-Q + Y^y*Z) from ?_]; exact bound_shift hf ((norm_add_le ..).trans (add_le_add hx d)); unfold U; simp only [T',Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul,Matrix.one_mul]; 
 unfold T' at he; rw [he]; abel
end YM.CF.Pannier.Chancel.Cuve
open YM.CF.Pannier.Chancel.Cuve
#print axioms newsletter
#print axioms w_flow
#print axioms gust
#print axioms busy
#check @w_flow
#check @aura
#check @newsletter
