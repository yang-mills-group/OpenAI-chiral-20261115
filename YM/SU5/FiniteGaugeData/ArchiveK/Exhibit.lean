import YM.SU5.FiniteGaugeData.ArchiveK.Minke
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.ArchiveK
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush Largo WithLp
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
namespace Midway
open Violas LightK Concert
variable {n J t q m j k:ℕ}{G:E4≃ₗᵢ[ℝ] E4}(L:FilterK){r V θ:ℝ}{D:ℕ}(K:ZephyrG G D t) (b:Bool) {S T U: Finset Cover}
abbrev glyph(n:ℕ):=Fin (n^3)
local notation "X" => glyph n
local notation "W" => Fin J × glyph n
structure FlockX (q w:ℕ) (p q':glyph n→Cover)(v:q*w=n):Prop where
 portrait: ∃ E: glyph n≃ Stamp q w, (∀ i,p i=actor K q w (E i) true)∧ ∀ i,q' i=actor K q w (E i) false -- can skip.
structure Ledger (K:ZephyrG G D t)(F:FilterK)(J:ℕ)(n:ℕ)(v r:ℝ) where
 U : Fin J × glyph n→ Cover
 V : Fin J × glyph n→ Cover -- scope shadow S e
 pos_all : 0<r ∧ r≤1
 bridge_Y (j:Fin J): let M:Op (glyph n):= Matrix.of (fun i i'=> stone G F (U (j,i)) (V (j,i')));
  ∃ P: PlansM (glyph n),page (glyph n)≤2*dim P ∧ ∀ z∈P, v*‖z‖^2 ≤ gas M z
 cloak(j k: Fin J) (u:j≠k) : (∀ i i':glyph n,∀ t∈ F.s, River r (emitX (U (j,i))) (rebate (V (k,i')) t)) ∨ (∀ i i':glyph n,∀ t∈ F.s,River r (rebate (V (k,i')) t) (emitX (U (j,i))))
variable (A:Ledger K L J n V r)
local notation "X'"=> Ledger K L J n V r
namespace Ledger
def city := Matrix.of fun i j: (Fin J × glyph n)=> stone G L (A.U i) (A.V j) -- shadow `city`
local notation "Μ"=> city L K A
-- K est.Acc.Camera dimension.W
lemma enroll (j:ℕ): ∃ P : PlansM W, (J*n^3:ℕ)≤2*(dim P+ J^2*page (BddT j))∧ ∀ v∈P,(V- ((J:ℝ)*(n:ℝ)^3)^2*(bumble G L*r^j))*‖v‖^2 ≤ gas (city L K A) v:=by
 let Ψ:= city L K A; let e:=A.pos_all; let Q:=bumble G L; have ht:0≤Q:=bumble_n G L; have hP:page (W)= J*n^3:=by simp [page,glyph] -- tune
 have ht(i k:Fin J)(p:i≠k) : Cast (BddT j) (parch i k Ψ) (bumble G L*r^j):=by
   rcases A.cloak i k p with g|g; · exact plaque_left G L (fun a: glyph n=>A.U (i,a)) (fun a:glyph n=>A.V (k,a)) (fun _ _=> rfl) j e.1 e.2 g -- tune
   exact plaque_right G L (fun a:glyph n=>A.U (i,a)) (fun a:glyph n=>A.V (k,a)) (fun _ _=> rfl) j e.1 e.2 g
 obtain ⟨P,h,T⟩:= crawl Ψ (BddT j) V (bumble G L*r^j) (mul_nonneg (bumble_n G L) (pow_nonneg e.1.le _)) ht (A.bridge_Y)
 rw [hP, page, Fintype.card_fin] at h; refine ⟨P,h,fun p q=>?_⟩; have hu:= T p q; rw [hP] at hu; push_cast at hu; exact hu
-- remove norm.Call. lemma ascend
abbrev Lft : Finset Cover:= univ.image fun i:W=> tax b (A.U i)
abbrev Rht : Finset Cover:= (univ:Finset W).biUnion fun i:W=> L.s.image fun x=>tax b (A.V i-x)
local notation "U₀"=> Lft L K b A
local notation "V₀"=> Rht L K b A
local notation "C"=> city L K A
lemma «use» (m j:ℕ)(x:2*((m*4)+J^2*page (BddT j))< J*n^3) (t:0<θ)(h:θ*coins G L (J*n^3) (page (Waltz.Beam U₀)) (page (Waltz.Beam V₀))+((J*n^3:ℕ):ℝ)^2*(bumble G L*r^j)<V): found (Pick U₀ V₀) m θ:=by
 obtain ⟨P,hP,T⟩:= enroll L K A j; let Y:=page W; have hy:Y=J*n^3:= by simp [Y,page,glyph]
 let f:= V-((J:ℝ)* (n:ℝ)^3)^2*(bumble G L*r^j); have he : found C (dim P) f:= castSense C P _ le_rfl _ T; -- returns existence P_ variant. use bound.he. tune shadow C( immediate)
 obtain ⟨T,t',g⟩:= he; obtain ⟨u,v,e,l⟩:= onward U₀ V₀ G L b A.U A.V (P:=C) (fun _ _=>rfl) (fun i=> Finset.mem_image_of_mem _ (mem_univ _)) (fun i x e=> Finset.mem_biUnion.mpr ⟨i,mem_univ _, mem_image_of_mem _ e⟩) θ t.le
 apply accrue _ (univ:Finset Glue) u v C e f θ _ T ?_ g t.le (lt_of_le_of_lt l ?_); · rw [card_univ]; rw [show Fintype.card Glue=4 from (by decide)]; omega
 rw [show page W=J*n^3 from hy]; unfold f; norm_cast at h ⊢; exact lt_sub_iff_add_lt.mpr h
#print axioms enroll
#print axioms «use»
end Ledger
-- t
end Midway
end YM.CF.Window.ArchiveK
