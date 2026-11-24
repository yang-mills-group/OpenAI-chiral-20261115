import YM.CF.Continuum.Tremor
import YM.CF.Emu.Peon
import YM.CF.Buffered.Lifted
/-! # Base budget in alternate angular reflection program at the identity pose.
  Not saying it dominates, but this is the actual relative cost on its own probe. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 30000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Hygrometry
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Tulip Phase
open Laurent Next.Free Bloch Fir Ember Jill Kea Sods Flare Emu Onyx Dial
open Filter Topology
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open YM.CF.Buffered YM.CF.Window
open YM.Stationary (Gaia)
variable {N m L B: Side} {j:ℕ}{r:ℝ}{o:Odd L.val}
lemma atAtlas (N:Side) : (Kea.tax emptyC (N:=More N))=1:=by
 funext i; apply group.mat_injective; change Matrix.diagonal (pw ∘ skyV.val)=(1:Op SU.F); ext a b; by_cases e:a=b <;> simp [e,Matrix.one_apply,pw,BZ.phase,skyV]
-- maybe Kea.tax N binder expects Gauge index, check
abbrev latPose (j:ℕ) (M:Jill.Male) (N:Side) := Dofu N (Kea.field (too N) j M)
lemma identity_atlas (M:Jill.Male) (p: Pad j N) : spar j M (1:Bkg (More N))=latPose j M N:=by
 rw [←atAtlas N]; exact p.2 _ _ M
-- uniform even at TOP, Run through all Male
abbrev voucher (j:ℕ) (r:ℝ) := ∀ (N:Side),Even N.val → ∀ (M:Jill.Male)(x:Stag N), disk j M (Kea.angle (too N) x)=Jill.cup N j M r (Kea.angle (too N) x)
lemma salutary (j:ℕ) (h:1≤ j):∃ r:ℝ,0<r ∧ voucher j r:=by
 obtain ⟨r,u,h⟩:= Kea.zipper h (show 0<(1:ℝ) from zero_lt_one); exact ⟨r,u,fun i e M p=>(h i e emptyC (too i) M (empty_m (by norm_num) _) p).symm⟩
lemma on_voucher {M:Jill.Male} (p: Even N.val)(h:voucher j r){w: Wave (Single N)} (k:Sea (latPose j M N) w):
    ‖inner ℂ (mateK N) w‖=iceK j (too N) M r:=by rw [apex (too N) p j M w k]; exact prod_congr rfl fun i _=> h N p M _
lemma can_spend {M:Jill.Male} (p: Even N.val)(hj:1 ≤ j){w: Wave (Single N)} (k: Sea (latPose j M N) w): inner ℂ (mateK N) w≠0:= by
 obtain ⟨r,f,h⟩:= salutary j hj; exact norm_pos_iff.mp (show 0 < ‖inner ℂ (mateK N) w‖ from on_voucher p h k ▸ ice_p _ _ _ f)

abbrev ascender (N:Side)(j:ℕ)(M:Jill.Male):Op (Single N):=Dofu N fun i:Stag N=> polarLift (Kea.field (too N) j M i) (disk j M (Kea.angle (too N) i))
lemma clad_service (M:Jill.Male)(p:Even N.val)(f:1≤ j): Clad (latPose j M N) (tickA N) 1 1 (ascender N j M):=by
 rw [← map_one (Dofu N)]
 refine torn _ p j M _ _ _ ?_; intro i; obtain ⟨a,t,l,W⟩:= crestQ j M (too N) p i; apply polarClad a t l; obtain ⟨r,q,k⟩:= salutary _ f; rw [show high_d _ _ _ _=_ from k N p M i] -- high_d defeq?
 exact cup_p _ q _

abbrev ledger (N:Side)(j:ℕ)(M:Jill.Male):= laneP (tickA N) 1 (ascender N j M)
-- maybe Profile.Pixel general warrant on alternative donor in later file.
end YM.CF.Hygrometry
