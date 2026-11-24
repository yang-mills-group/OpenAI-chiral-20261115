import YM.CF.Buffered.Trim
import YM.CF.Buffered.Floored
/-! Sharp two-base price, both histories as issued (same Month).
 Integrated finite bins; includes BOTH logarithms. Tol paid before pivots. -/
set_option autoImplicit false
set_option synthInstance.maxSize 22000
set_option maxHeartbeats 430000
noncomputable section
namespace YM.CF.Buffered.Edition
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Cube Lat Tenant Tulip Pastry Scroll Spire Fock Vault Pail Stake Vale Vale.Grace Gauge Paige Brace Next.SectorChange Skye Cascade Analysis Pressure Py Haro Jet Vol Rel Graph Nova Alloy Mint Ballad Crust -- remove
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker ComplexOrder Classical
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group} {m M' B:Side}
variable (V:Grace K R L)
variable {d:ℝ}{U:Grasp V.U B d}{W:GivenX V U}
variable (a:ℝ)(p i N0:ℕ) (J:Robes M' V W) (q:Chi) (h:ℝ)(R0 δ:ℝ→ℝ)
variable {x:ℝ} {n:ℕ}(Z:Volume.History V a p i N0 J q h R0 δ x m n)
variable {KX b' vL c l b D E' C0 h1 r α C₁ J₁ D₁ H v₁ R' θ:ℝ}{kT d' w₁ t₁ t₂ R₁:ℕ}
variable (P_ : Pic.Span W.pearl KX b' vL c l b kT) (z:1≤h)
lemma direct_launch : ((Z.gram 0).path=V.L.path n) ∧ ((Z.gram 0).beta=x) ∧ ((Z.gram 0).funds=K.top.clip) ∧ ((Z.gram 0).p=Z.month.a 0) := by
 have he:= Z.flow.note.owns 0 (Nat.zero_le n); exact ⟨he.path.symm,Z.flow.note.color.trans Z.flow.day.unit,he.fund.symm,he.width.symm⟩
variable {x':ℕ→ℝ} (t:Tendsto x' atTop atTop) {M:ℕ→Side}{n':ℕ→ℕ} (Z':∀ k, Volume.History V a p i N0 J q h R0 δ (x' k) (M k) (n' k))
variable (T:∀ k,Volume.History V a p i N0 J q h R0 δ (x' k) (M k*3) (n' k))
variable (Sb:ℝ)(d₀:ℕ)
variable (hm : ∀ k, grainZ V W N0 (x' k) ≤ (M k).val)
variable (hW : ∀ k, ((M k).val:ℝ) ≤ Sb * (((oYY V N0 J (x' k)).val:ℝ)^d₀))
-- volume II h. maybe not needed: angle pressure upper req log angular sign. using hP pad for big size follows from small t. no secondary Window actually. positivity big Angle from positive rec cost (exists growth) via tepid? can show glow on angle via toll globe price positive on small & brink implies log price leaves +. easier generic lower current. use include hW' as in ms.
variable (hW' : ∀ k, (((M k* (3:Side))).val:ℝ) ≤ Sb * (((oYY V N0 J (x' k)).val:ℝ)^d₀))
variable (X:∀ k,(Real.log (x' k))^4 ≤ ((M k).val:ℝ)) (u:0<θ)(Y:∀ k,(Z' k).month=(T k).month)
lemma triple (m:Side): (cell (m*3) B R.L 0).val = (cell m B R.L 0).val*3:=by unfold cell CSide Vale.mesh; simp [More]; ring
local notation "SM" => (fun k=> cell (M k) B R.L 0)
include t X u P_ z hm hW hW' Y
theorem huddle : ∀ᶠ k in atTop,
 Real.log (drip ((Z' k).gram 0) U) -Real.log (drip ((T k).gram 0) U)/81 ≤ θ*(((SM k)).val:ℝ)^4 := by
 let pY:= Volume.windowWindS V a p i N0 J q h R0 δ t Z' Sb d₀ hm hW z
 have hr:= (V.L.mood 0).width
 have he: 0 ≤ K.top.paths:= pY.row
 obtain ⟨C,w,Zc⟩:= Glaze.angel_triple (Y:=V.U) (B:=B) (e:=d) P_.p
 obtain ⟨t',T'⟩:= Pic.sortV P_.p b
 let y:=θ/32; have hy:0<y:=by unfold y; positivity
 let pT:= Volume.windowWindS V a p i N0 J q h R0 δ t T Sb d₀ (fun k=> le_trans (hm k) (Nat.le_mul_of_pos_right _ (by change (0:ℕ)<3; decide))) hW' z
 filter_upwards [t.eventually (Tariff.eventual_fence SU.group _ hr y V.W.bar K.top.paths he K.top.clip hy), Alloy.tepid P_ pY, Roe.touch P_ pT, pY.support,pY.tend.eventually_ge_atTop (kT:ℝ),pT.tend.eventually_ge_atTop (kT:ℝ),pY.tend.eventually_ge_atTop (t':ℝ), (show Tendsto (fun i=> (y*(eur SM i ^4))) atTop atTop from ((tendsto_pow_atTop (by decide : (4:ℕ)≠0)).comp pY.tend).const_mul_atTop hy).eventually_ge_atTop C] with k v ⟨N,G⟩ ⟨N',_⟩ g z z' hK l
 let x:=x' k; let m:= M k; let M:= (SM k); let R':= More M; let Q:= (cell (m*3) B R.L 0); let Q':=More Q
 let Ck:= (Z' k).gram 0; let Dk:= (T k).gram 0; let f:=V.L.path (n' k); let Pk:= Ck.p; let c:=K.top.clip
 obtain ⟨t,u₁,t₁,x'⟩:= direct_launch V a p i N0 J q h R0 δ (Z' k); obtain ⟨e,e₁,t₂,y'⟩:= direct_launch V a p i N0 J q h R0 δ (T k)
 have hP:Dk.p=Ck.p:= x' ▸ (Y k ▸ y') -- issue x' shadow
 have hx:Q.val=3*M.val:=(triple m).trans (mul_comm ..)
 have hu:= V.L.mood (n' k)
 have hR:Ck.path.Bounds Ck.funds K.top.width K.top.paths V.W.bar :=by unfold Ck; rw [t,t₁]; exact hu
 have hD:Dk.path.Bounds Dk.funds K.top.width K.top.paths V.W.bar :=by unfold Dk; rw [e,t₂]; exact hu
 have hp:= P_.plan _ (show kT≤ M.val from Nat.cast_le.mp z); have ht:= P_.plan _ (show kT≤ Q.val from Nat.cast_le.mp z'); -- ℓ defeq issue
 let V:= Graph.angle Ck; let S:= Graph.angle Dk; let Z:=Kea.angel (Vale.mesh m R.L 0) U Ck.J.M; let W':=Kea.angel (Vale.mesh (m*3) R.L 0) U Dk.J.M
 have hZ:0<Z:= Kea.angel_p W.pearl P_.stmt hp.1 P_.p P_.eP _ hp.2; have hw':0<W':= Kea.angel_p W.pearl P_.stmt ht.1 P_.p P_.eP _ ht.2
 let X':= Grid.globe R' f c Ck.p x; let Y':=Grid.globe Q' f c Ck.p x; have hv: X' Pk.threshold= V := by unfold V; rw [← globe_price hR]; unfold X' c f x; unfold Ck; rw [u₁,t,t₁]
 have hl:Y' Pk.threshold=S:=by unfold S; rw [← globe_price hD]; unfold Y' c f x; unfold Dk; rw [e₁,e,t₂]; rw [← show Dk.p=Ck.p from hP]; rw [show Pk=Dk.p from hP.symm]
 have ho: Real.log V-Real.log S/81 ≤ y*(R'.val:ℝ)^4:=by
    rw [←hv, ←hl]; refine v ?_ ?_ hu g.1 (?_) (?_); rotate_left
    · calc _ ≤ _:= X k
           _ ≤ (M.val:ℝ):= by exact_mod_cast Vale.amplit (m:=m) .. -- tune
           _ ≤ _:=by exact_mod_cast (show M.val≤ R'.val from Nat.le_mul_of_pos_right _ (by decide))
    · change 0<X' Pk.threshold; exact hv ▸ (show 0<V from N)
    · change X' Pk.threshold /2 ≤ X' (Pk.threshold/2); rw [hv]; rw [t,t₁,u₁] at G; exact G
    refine ⟨?_⟩; change Q.val*2=M.val*2*3; rw [hx]; ring
 have hτ : ‖Real.log W'-81*Real.log Z‖≤ C:= by
    unfold W'; rw [← show Ck.J.M=Dk.J.M from score_same_map _ a p i N0 J q h R0 δ (Z' k) 0 (Nat.zero_le _) (T k)]; exact Zc _ _ _ hx hp.1 ht.1 hp.2 ht.2 ((T' _ hp.2.1 (Nat.cast_le.mp hK)).2.2) P_.eP _
 change Real.log (V*Z)-Real.log (S*W')/81 ≤ _; rw [Real.log_mul (Ne.symm (ne_of_lt N)) (Ne.symm (ne_of_lt hZ)),Real.log_mul N'.ne' hw'.ne']; rw [show (R'.val:ℝ)= (M.val:ℝ)*2 from ?_] at ho; have he:= abs_le.mp hτ; change C ≤ y*(M.val:ℝ)^4 at l; unfold y at l ho; nlinarith only [ho,he.1,l,mul_nonneg u.le (pow_nonneg (show 0 ≤ (M.val:ℝ) by positivity) 4)]
 exact_mod_cast (show R'.val=M.val*2 from rfl)
omit t Y X hm hW hW' in
lemma mounts : ∀ᶠ x:ℝ in atTop, ∀ m:Side, grainZ V W N0 x ≤ m.val → (m.val:ℝ) ≤ Sb *(((oYY V N0 J x).val:ℝ)^d₀) → (((m* (3:Side))).val:ℝ) ≤ Sb * (((oYY V N0 J x).val:ℝ)^d₀) → (Real.log x)^4 ≤ (m.val:ℝ) →∀ (n:ℕ)(A:Volume.History V a p i N0 J q h R0 δ x m n)(B':Volume.History V a p i N0 J q h R0 δ x (m*3) n), A.month=B'.month → Real.log (drip (A.gram 0) U)- Real.log (drip (B'.gram 0) U)/81 ≤ θ*((cell m B R.L 0).val:ℝ)^4 := by
 rw [eventually_atTop]; by_contra! H
 choose x t' m b' u' f p' n X Y H Z using fun k:ℕ=> H (k:ℝ); obtain ⟨i,w⟩:=(huddle V a p i N0 J q h R0 δ P_ z (tendsto_atTop_mono t' tendsto_natCast_atTop_atTop) X Y Sb d₀ b' u' f p' u H).exists; exact not_lt_of_ge w (Z i)
end YM.CF.Buffered.Edition
#print axioms YM.CF.Buffered.Edition.mounts
