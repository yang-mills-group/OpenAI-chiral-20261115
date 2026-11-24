import YM.CF.BPress.Hazel.Red
/- N collar amendment. Before any activation taper. Uniform costs across depth- & parameter change. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Hazel
open Function Finset Filter NormedSpace Metric SU SU.Pair Lat Fock Lattice Cube Spin Spin.Paint Dial Lute Lute.Kite Lute.Fort Lute.Music Meadow MeasureTheory Net Meadow.Tent Sheet
open scoped Topology BigOperators NNReal Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ContDiff Classical
attribute [local instance] opCStarAlgebra
variable {s :Side}{B:BandWidth}{u v γ : ℝ} (z: Fin 5)
open Grid Wealth Locale Tunnel Bands Branch Clipγ Letter Chrono Meadow.Frame Meadow.Stamps
open Bias
variable {X:Bands s B} {R:Hangar s}{T:Letter X}{k:Tiling s} {S:Seal (SiteX X R)}{U:Micro s}{W:Rental}{q q' ε η g g' d c c' : ℝ}
variable {L: Grip X W R S T U q q' c}{x:Site s}
-- beyond near-gap substitution. not even need checking label center orientation. 
namespace Stopped
variable (p:Stopped T k L ε η)
include p
lemma desert {i:X.Index}(u:x∈ X.band i)(t:¬ NearBlock X W.M x) : Xactual W R S T k U x=T.plant i x∧ ∀ v:ℝ,Kactual W R S T k U v x=T.brush i v x:=by
 obtain ⟨a,b⟩:= p.groomed (beyond L.power x (fun x=>t x.1)); refine ⟨a.trans (Gband T u),fun v=> (b v).trans ?_⟩; rw [Hband W T u]; refine if_neg ?_; intro l; exact t (near_gap (buriesN X u (L.power.summer.trans halfway) (l.2.trans ((Nat.le_succ _).trans W.hm))))
lemma nonchange {i:X.Index}(u:x∈ X.band i)(h:¬ (NearBlock X W.M x ∧ Near X R S 6 x)) : Kactual W R S T k U 2 x=T.brush i 2 x:= (p.groomed (beyond L.power x h)).2 2 |>.trans (H_later W T L.tint L.power.summer u le_rfl)
end Stopped
-- perturbation amount comparison on near-gaps, any point with proper orientation
namespace Zone
variable {L':Grip X W R ∅ (Reference z X) 1 q q' 0}
local notation "K₁"=> Kactual W R S T k U
local notation "X_"=> Xactual W R S T k U
local notation "Ζ" => Rosetta z X W R k
local notation "Ζ'"=> RosettaX z X W R k
abbrev R_ (A:ℝ→Paint s)(U:E)(i:Site s)(v:ℝ):=swivelC U (A v i)
lemma d_swive (A B:ℝ→Paint s)(g:E)(v i) (e:∀ v, A v i = swivelC g (B v i))(h: DifferentiableAt ℝ (fun v => B v i) v): primeC A v i= swivelC g (primeC B v i):=by
 let L:Op Slot→ₗ[ℝ] Op Slot:={
   toFun:=swivelC g
   map_add' x y:=by simp [swivelC,congrC,mul_add,add_mul]
   map_smul' a x:=by simp [swivelC,congrC,Algebra.smul_mul_assoc,Algebra.mul_smul_comm] }
 unfold primeC; simp_rw [e]; exact (L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt v h.hasDerivAt).deriv -- tune
variable (p:Stopped T k L ε η) (t:Stopped (Reference z X) k L' ε η)
include p t
lemma perturbation {i:X.Index}(a:x∈ halo (Warm B) (X.gap i))(h: Good X R S 3 (panel X x))(f:T.color x=z): ∃ g:E,chord g 1 ≤ c ∧ X_ x=scaledV g (Ζ' x)∧ ∀ v, K₁ v x= R_ Ζ g x v:=by
 let W₀:=Reference z X; obtain ⟨α,α'⟩:= read_ref z X W R k t x; obtain ⟨b,b'⟩:= p.groomed (good_retained L.power x h); have he:= L.credit; unfold R_; simp_rw [α,α',b,b']; by_cases p: Welkin X x
 · obtain ⟨j,hj⟩:=p; have Ht:= buriesS X hj halfway a; rw [Gband T hj, Gband W₀ hj]; by_cases g:j∈X.dc
   · have hx:= L.tint.curbD j g x hj; have hy:= L'.tint.curbD j g x hj; refine ⟨1,(chord.refl (1:E)).le.trans he,?_ ,fun t=>?_⟩; rw [scaled_one,hx.1,hy.1]; rw [turn_one,Hclan0 W T L.tint hj g, Hclan0 W _ L'.tint hj g]
   refine ⟨closeC (T.frameN x) z, ?_,?_,fun v=>?_⟩; · rw [close_cost_q,←f]; exact L.nSeat _ (good_m h (by norm_num))
   · rw [(L.tint.curbN j g x hj Ht).1,(L'.tint.curbN j g x hj Ht).1]; rw [←scaled_s, closeC, show W₀.frameN x=Mag.center z from rfl,mul_assoc,mul_inv_cancel,mul_one] -- tune
   rw [HclanN W _ L.tint hj g Ht,HclanN W _ L'.tint hj g Ht,amend,f]; unfold amend; change swivelC _ _ = swivelC _ (castN (Mag.center z) z _ _); rw [castN,closeC,closeC, inv_mul_cancel,turn_one] -- tune closeC order multiple
 refine ⟨1,(chord.refl (1:E)).le.trans he,?_,fun v=>?_⟩; rw [scaled_one,Gmiss T p, Gmiss _ p,f]; rfl; rw [turn_one,Hmiss W T p,Hmiss W _ p,f]; rfl

lemma price {i:X.Index}(a:x∈ halo (Warm B) (X.gap i))(h: Good X R S 3 (panel X x))(f:T.color x=z):dist (X_ x) (Ζ' x) ≤ sphereRate*c ∧ ∀ v∈ Set.Icc (0:ℝ) 2, ‖K₁ v x - Ζ v x‖ ≤ μH*c ∧ ‖primeC K₁ v x-primeC Ζ v x‖≤ μH*c*priceTone:=by
 obtain ⟨g,w,a,b⟩:=perturbation z p t a h f; have hx:= sphereRate_cost.positive; have he: 2*sphereRate*chord g 1≤ μH*c:= mul_le_mul_of_nonneg_left w (by positivity); rw [a]; refine ⟨ ?_, fun v q=>?_⟩; nth_rw 2 [←scaled_one (Ζ' x)]; exact (scaled_chord ..).trans (mul_le_mul_of_nonneg_left w hx.le)
 rw [b,d_swive _ _ g v x b (show _ from ((t.Ksmooth x).differentiable (by norm_num)) v)]; constructor; · exact (Bend.moving ..).trans ((mul_le_of_le_one_right (by positivity [chord.positive g 1]) (show ‖Ζ v x‖≤1 from (norm_κ _ (t.Kplan v x)).le)).trans he)
 exact (Bend.moving ..).trans (mul_le_mul he (pegged _ t.rate x v q) (norm_nonneg _) (by unfold μH; positivity [L.credit])) -- tune
omit p
variable {Y':Grip X W R ∅ (Reference 0 X) 1 q q' 0}(t':Stopped (Reference 0 X) k Y' ε η)
include t'
-- deeper Mark reference comparison is by gauge symmetry; assertion on all Mark support beyond our fixed radius_i.
lemma deep_s {i:X.Index}(h:x∈ X.band i)(v:¬ NearBlock X W.M x): let g:= pivotal z X i; Ζ' x= scaledV g (RosettaX 0 X W R k x) ∧ ∀v, Ζ v x=R_ (Rosetta 0 X W R k) g x v:=by
 intro G; unfold RosettaX Rosetta; obtain ⟨s,t⟩:= t.desert h v; obtain ⟨p,q⟩:=t'.desert h v; unfold R_; rw [s,p]; have he: pivotal 0 X i=1:= by unfold pivotal; split; rfl; rw [orb,Mag.center_zero,inv_one]
 refine ⟨?_,fun v=>?_⟩; · unfold Reference MiniMark; dsimp only; rw [he,scaled_one]
 rw [t,q]; unfold Reference PlateM; dsimp only; rw [he,turn_one] -- tune indent
end Zone
end YM.CF.BPress.Hazel
