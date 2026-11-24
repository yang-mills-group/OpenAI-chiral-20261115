import YM.SU5.FiniteGaugeData.Signal.Sampling
/-! # Free compression port. λ turns convergence in Grassmann at height every choice.
Pointwise in parameters but constants before period, level./ -/
set_option autoImplicit false
set_option maxHeartbeats 460000
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Signal.Sparkle
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill SU Rush Tulip Cube Fock Peaks Dial Spire Vault Scroll Paige Brace Kea Supplies
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Kronecker Classical
attribute [local instance] opCStarAlgebra
variable {I J:Type*}[Fintype I][LinearOrder I]
variable {N:Side}{a b c C u v s H:ℝ}{i j d k:ℕ}
open Condense Retain OrbitPort LocalPlane Branch Tenant Circuit Skye
namespace Portage
open Furnace
variable [Nonempty I]
lemma straight_cost (x:Ket I){A:Op I}(hp:IsStarProjection A)(p:0<H) : ‖acts (upstairs A H) x‖≤ H⁻¹*‖x‖+H*‖x‖:=by
 unfold upstairs burn; rw [act_add,act_smul,act_smul]; refine (norm_add_le ..).trans ?_ ; rw [norm_smul,norm_smul, Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg p.le,Real.norm_of_nonneg (inv_pos.mpr p).le]; exact add_le_add (mul_le_mul_of_nonneg_left (cap hp _) (inv_pos.mpr p).le) (mul_le_mul_of_nonneg_left (cap hp.one_sub x) p.le)
lemma contract_cost (x:Ket I){A:Op I}(hp:IsStarProjection A)(p:0<H)(B:Op I)(b₀: IsStarProjection B)(u:‖acts (1-B) (acts A x)‖≤ a):
    ‖acts (upstairs A H) (acts B (acts A x))‖≤H⁻¹*‖x‖+(H⁻¹+H)*a:=by
 let Y:= acts A x; let V:= upstairs A H
 rw [show acts B (acts A x)= acts A x-acts (1-B) (acts A x) by rw [act_sub,act_one,sub_sub_cancel],map_sub]; let J:= acts (1-B) Y; apply (norm_sub_le (acts V Y) _).trans; apply add_le_add
 · change ‖acts (upstairs A H) (acts A x)‖≤_; rw [←act_mul, rento hp,act_smul,norm_smul,Complex.norm_real, Real.norm_of_nonneg (inv_pos.mpr p).le]; exact mul_le_mul_of_nonneg_left (cap hp _) (inv_pos.mpr p).le
 apply (straight_cost J hp p).trans; rw [add_mul]; exact add_le_add (mul_le_mul_of_nonneg_left u (inv_pos.mpr p).le) (mul_le_mul_of_nonneg_left u p.le)

lemma distant(c d:ℝ)(p:0<c)(e:a>0)(g:b>0) : ∃ z:ℝ,0<z∧ a*z*b ≤ c:=⟨c/b/a,by positivity,by field_simp; rfl⟩ -- omit d
variable (N l:Side) -- remove l
variable {N}
variable {A:Produce j u v a b s}
def colorWall (S:Support (More N)): Finset (Single N):= (board (forum N 1) S)
lemma locate_wall (S:Support (More N))(i:Single N): i∈ colorWall S ↔ node i.1.1∈ S:=by unfold colorWall board; rw [mem_filter,and_iff_right (mem_univ _)]; rfl
lemma color_wall (S:Support (More N))(a:ℝ):colorWall S=board (forum N a) S:=rfl
lemma wallUp {S T:Support (More N)}(p:S⊆T): colorWall S⊆colorWall T:=fun i v=> (locate_wall T _).mpr (p ((locate_wall S i).1 v))

lemma rack (o:Site (More N)){Y:Finset (Site N)} (l:Slot) (u:∀ i∈Y,separation o (node i) ≤ d) : colorsOne Y l⊆ colorWall (bay (terr (More N)) o d):=by
 intro i v; exact (locate_wall _ i).2 ((bay_mem _).2 (u _ (mem_filter.mp v).2.2))
local notation "F"=> forum N s
lemma outside (O:Site (More N)) (P B:Op (Single N))(h:‖P-B‖≤a)(p: FiniteOp (forum N s) d B) (x:Ket (Single N))(t:Focus (b:=forum N s) O 0 i x): ‖acts (1-(cutM (colorWall (bay (terr (More N)) O (i+d))))) (acts P x)‖ ≤ a*‖x‖:=by
 let Q:=Branch.strip (forum N s) (bay (terr (More N)) O (i+d)); have he: acts Q (acts B x)= acts B x:=by
    nth_rw 1 [←(show acts _ x=x from t)]; rw [←act_mul B,←act_mul,show Q * (B*Branch.strip (forum N s) (bay ((forum N s).F) O i)) = _ from locates (d:=i) p O,act_mul, t]
 change ‖acts (1-Q) (acts P x)‖≤_
 have ht:acts (1-Q) (acts B x)=0:=by rw [act_sub,act_one,he,sub_self]
 rw [show acts (1-Q) (acts P x)=acts (1-Q) (acts (P-B) x) by rw [act_sub (A:=P),map_sub,ht,sub_zero]]; exact (cap (show IsStarProjection Q from cutM_idp _).one_sub _).trans ((Flare.opy ..).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))) -- A implicit?
structure Column (T:Support (More N))(j:ℕ)(M:Jill.Male)(u:Slot)(W:Finset (Site N))(H d b:ℝ)(x y:Ket (Single N)) : Prop where
  color : acts (cutM (colorsOne univ u)) y=y
  supported : acts (cutM (colorWall T)) y = y
  anchor : acts (cutM (colorsOne W u)) y=x
  cost : ‖y‖ ≤ d
  pay : ‖acts (upstairs (funde j M N 1) H) y‖ ≤ b
-- Note independent of radius i of the local tile containing T!
include A
theorem election (hp:0<s)(hx:0<H)(v₀:0<C) {g:ℝ} (e:H⁻¹ * C⁻¹ < g): ∃ k:ℕ,∀ᶠ n:Side in atTop,Pad j n →∀ (M:Jill.Male)(o:Seat n)(l:Slot)(d:ℕ)(T:Finset (Site n)),Circuit.Screen j s C l n T → (∀ i∈ T,separation o (node i) ≤ d) →∀ x:Ket (Single n), acts (cutM (colorsOne T l)) x=x→‖x‖≤1→∃ y, Column (bay (terr (More n)) o (d+k)) j M l T H C⁻¹ g x y:=by
 obtain ⟨a0,r,k',a',t,h,_⟩:= A.outset; let u:=g-H⁻¹*C⁻¹; have hp':0<C⁻¹:=inv_pos.mpr v₀; have hs:0<u:=sub_pos.mpr e; have hv:0<H⁻¹+H:=(by positivity); obtain ⟨z,hy,hl⟩:= distant (d:=0) u hs hv hp'; obtain ⟨k,hκ⟩:=sunray a0 r a' t z hy
 refine ⟨k,?_⟩; filter_upwards [eventually_ge_atTop (⟨k'+1,by omega⟩:Side)] with n ht d
 intro M o l d' T S t0 x u p; change k'+1≤n.val at ht; let U:= colorsOne T l; let V:=colorsOne (N:=n) univ l; let P:= funde j M n 1; have f: IsStarProjection P:= compass M j d; obtain ⟨v,q,hx₂,w⟩:= solveMark U P v₀ (S M) x u
 have hc: ‖v‖≤ C⁻¹:=by
    rw [inv_eq_one_div]; apply (le_div_iff₀ v₀).2; rw [mul_comm]; exact w.trans p
 let R:= bay (terr (More n)) o (d'+k); let W:=colorWall R; let B:=cutM W; have hB:IsStarProjection B:=cutM_idp W; let y:= acts B (acts P v); have v' : acts (cutM V) v=v:= closedCut (fun i h=> mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h).2.1,mem_univ _⟩) q
 refine ⟨y,sectorwiseCut (Q:=B) ?_ (embargo_slot l _ M d v'),bore hB _, (inwardCut  (W:=U) (W':=W) ?_ _).trans hx₂, (cap hB _).trans ((cap f v).trans hc),?_⟩; swap
 · change U⊆W; exact rack o l (fun i v=> (t0 i v).trans (Nat.le_add_right ..))
 · intro i v j p; have hj : i ≠ j:= fun u=> p (u ▸ v); simp [B,cutM,hj,Ne.symm hj]
 let G:=h n (by omega) M; let A':Openc (More n) s :=⟨1,vacancy0 _ hp⟩; obtain ⟨F',hx',w₁,_⟩:= supply (Drapes.Crown.lib G) a' z hy k hκ
 have hs: ‖acts (1-B) (acts P v)‖ ≤ z * C⁻¹ := (outside o P (F' A') (w₁ A') (hx' A') v (closedCut (rack o l t0) q)).trans (mul_le_mul_of_nonneg_left hc hy.le) -- tune Focus
 apply (contract_cost v f hx B hB hs).trans; have WU: (H⁻¹+H)*z*C⁻¹ ≤ g-H⁻¹*C⁻¹:=hl
 change H⁻¹*‖v‖+_ ≤g; linarith only [WU,mul_le_mul_of_nonneg_left hc (inv_pos.mpr hx).le]
end Portage
end YM.CF.Signal.Sparkle
#print axioms YM.CF.Signal.Sparkle.Portage.election
