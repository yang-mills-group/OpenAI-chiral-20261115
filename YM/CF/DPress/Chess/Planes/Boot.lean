import YM.CF.DPress.Chess.Planes.Sleeve
import YM.CF.DPress.Chess.Planes.Stair
/-!
 One-step inspection radius. No post-h length costs.
 αtrue: X-read constant on *each* level with margin B0 (≤ mρ-4 paid in schedule).
 pager MSP: kernel lift can depend also on REPAIRED Y and emit modes in cropped positive width 2ℓ. Reads including the cones on sampler layers paid here explicitly.
 -/
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Chess
open Function Lattice Finset Laurent Spire Skye Scroll Lat Rush Wilson Fixed FD
open Cube (More assembly)
open scoped Topology BigOperators Classical
namespace Wall
variable (W:Wall){n m:Side}(K:Ratio n m){b a r ℓ d:ℕ}
open Lift RG Transit.Bough
lemma spread (u:r+1+a ≤ b) : spreadB K (W.crop n b) r⊆ twig (ratio K) (W.crop n a):=by
 intro i h; obtain ⟨x,l,h⟩:= halo_spec.mp h; obtain ⟨x,s,rfl⟩:= mem_image.mp l; let P:=ratio K; apply (twig_v ..).2; refine W.surrounding (a:=a) (b:=b) (r:=r+1) (by omega) _ (halo_spec.mpr ⟨x,s,?_⟩); apply Nat.le_of_mul_le_mul_left _ P.count.property; calc
   _ ≤ separation (P.embed x) (P.embed (P.parent i)) := Corona.below P ..
   _ ≤ separation (P.embed x) i + separation i (P.embed (P.parent i)):= separation_triangle ..
   _ ≤ r + P.count.val:=Nat.add_le_add h (by have hx:=Corona.near P i; omega)
   _ ≤ _:=by rw [Nat.mul_succ]; exact Nat.add_le_add_right (Nat.le_mul_of_pos_left r P.count.property) _
-- under a step. need ~(W.site n) action on twig.
lemma twig_T (T:StepData (More n) (More m))(p:T.ratio=ratio K)(S:Support (More n)): (W.boost K.count).negZ (twig (ratio K) S)=twig (ratio K) (W.negZ S):=by
 ext x; rw [swipe, twig_v, twig_v, W.swipe]; unfold site; rw [← W.rod]; rw [sitA,sitA]; unfold reSweep; rw [← reA, ← p]; exact Iff.of_eq (congrArg (·∈ S) (AnalyticBridge.GaussianFieldAlignment.Locations.parent_map (S:=T) ..))
local notation "l'" =>Push.GridApprox.reach
lemma price_I (r x S:ℕ)(p:r*S+x ≤ S*x): S*(x-r) ≥ x:= by rw [Nat.mul_sub,← mul_comm r S]; omega
-- explicit schedule lanes
abbrev rail:ℕ:=200
abbrev wage (N d:ℕ):ℕ:= 1000+ 2*(N+d) -- max Frame recipe stencil and Robes.n, history
lemma Lot_p (v:wage r d ≤ ℓ) : r+1+ℓ ≤ 2*ℓ:=by unfold wage at v; omega
lemma Lot_u(v:wage r d ≤ ℓ)(p:4≤K.count.val): 2*ℓ+K.count.val≤K.count.val*ℓ:=by
 have hp:100 ≤ ℓ:=by unfold wage at v; omega
 nlinarith
lemma Lot_h (v:wage r d ≤ ℓ) : 0<ℓ∧d+rail ≤ ℓ ∧ rail ≤ ℓ ∧ d+1≤ℓ-d:=by unfold wage at v; unfold rail; omega
lemma smart (v:wage r d ≤ ℓ)(n:Side):halo d (W.crop n ℓ) ⊆ W.crop n rail:= W.surrounding (by have ht:= Lot_h v; omega) n
lemma rateF (v:wage r d ≤ ℓ)(n:Side): Far d (halo d (W.crop n ℓ)) (halo d (W.negZ (W.crop n ℓ))):=by
 have he:=Lot_h v; have hp: Far d (W.crop n (ℓ-d)) (W.negZ (W.crop n (ℓ-d))):= W.aloof (a:=1) (by omega) (by omega) (by omega) n; exact hp.down le_rfl (W.surrounding (by unfold rail at he; omega) n) (W.negativity (by unfold rail at he; omega) n)
lemma window_p (S:StepData (More n) (More m))(u:S.ratio= ratio K)(v:S.patch.J=4)(h':S.patch.L=K.count)(p:4≤K.count.val): ∀ i∈ W.crop n rail, Push.GridApprox.window (S.ratio.embed i) (l' S.patch)⊆ ↑((W.boost K.count).crop m rail):=by
 intro i h z l; apply (W.boost K.count).surrounding (b:=K.count.val*rail) (a:=rail) (r:=l' S.patch) _ _; swap; · unfold Push.GridApprox.reach Patch.radius; rw [v,h']; unfold rail; omega
 apply halo_spec.mpr; obtain ⟨y,v,rfl⟩:= l; dsimp only; rw [u]; refine ⟨_,W.spend K _ i h,?_⟩; rw [separation_comm,separation,add_sub_cancel_right]; exact Work.E01.pdist_wrap_le v
lemma torch (S:StepData (More n) (More m))(u:S.ratio=ratio K)(T: Support (More n))(x:ℕ)(z:Support (More m)) (p:∀ i∈T, Push.GridApprox.window (S.ratio.embed i) x⊆ ↑z): ∀ i∈ W.negZ T, Push.GridApprox.window (S.ratio.embed i) x ⊆ ↑((W.boost K.count).negZ z):=by
 intro i h y q; apply ((W.boost K.count).swipe z y).2; let j:= W.site n i; let V:=W.boost K.count; apply p j ((W.swipe ..).1 h); rw [show S.ratio.embed j= V.site m (S.ratio.embed i) from (by rw [u]; unfold site; unfold j site; rw [←W.anon,← V.anon]; exact W.broad K ▸ W.shape.foldsT K i)]; unfold site; rw [sitA,sitA]; exact Push.GridApprox.window_affine _ _ _ q -- tune
end Wall
end YM.CF.DPress.Chess
