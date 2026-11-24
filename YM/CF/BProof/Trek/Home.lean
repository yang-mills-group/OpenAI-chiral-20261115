import YM.CF.BProof.Trek.Mesh
/-! The homogeneous z reference (X_B, H = K unamended beyond its threshold with units
1 everywhere D vs z everywhere N). independent of Mark-entangled fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Trek
open Function Cube Spin Extension Metric MeasureTheory Dial Lat Tulip Tenant Branch Fock SU Lattice Angular Circle Hero Dream Filter Mark Mapping Finset Hearth
open scoped Topology Matrix Matrix.Norms.L2Operator ContDiff Classical BigOperators
attribute [local instance] opCStarAlgebra
variable {s c a:Side}(Y: Yard s)(g:Ratio c s)(i:Fin 5)
def homeScript : Script Y where
 X a := fun _=> if Y.D a then apex else scaledV (locus i) apex
 K a := fun _ => if Y.D a then BM 1 else side i -- side type
 frame _ _:= locus i
 label _ _:= i
variable {u v:ℝ}{H:Herald u v}{t:ℕ}(C:Sized t H.whole)
lemma home_here (d:ℝ)(e:0≤d): Permit (homeScript Y i) C 1 g ∅ d:=by
 let X:=homeScript Y i; have h(k:Y.Index)(p:Y.D k)(x): X.X k x=apex∧ X.K k x=BM 1 :=⟨if_pos p,if_pos p⟩; have hp(k:Y.Index)(p:¬Y.D k)(x): X.X k x=scaledV (locus i) apex ∧ X.K k x=motion (locus i) ∘ BM 1:= ⟨if_neg p,if_neg p⟩
 change Permit X C 1 g ∅ d; constructor
 · intro k x hx; by_cases p:Y.D k; rw [(h k p x).2]; exact moneyB z1; rw [(hp k p x).2]; exact (moneyB z1).pile _
 · intro k x hx; by_cases p:Y.D k; rw [(h k p x).1, (h k p x).2]; exact BM_x ..; rw [(hp k p x).1,(hp k p x).2, Function.comp_apply,BM_x]; exact compass ..
 · intro k x a hx _; unfold EdgePrice; dsimp only; rw [show X.X k (x+step a)=X.X k x from rfl]; change ‖Lat.turn 1 _ -_‖≤_; rw [Lat.turn,fund_one,act_one,sub_self,norm_zero]; exact H.gc.le
 · intro k t u x a hx w; change ‖motion 1 (X.K k _ t)-X.K k x t‖ ≤ v; rw [show X.K k (x+step a)=X.K k x from rfl,motion_one,id_eq,sub_self,norm_zero]; exact H.uf.le
 · exact fun i p b _=> h i p b
 · exact fun i p b _ _=> hp i p b
 · exact fun _ _ _ _ _ _=> (cd_self ..).trans_le e
 · exact fun _ _ _ _ _=>rfl
 exact fun _ _ _=> (Gauge.chord_one _).trans_le e
lemma lampZ (δ:ℝ) (u:0≤δ)(e:δ≤H.calm) : Lamp (Y:=Y) C g ∅ δ 1 1:= ⟨fun _ _ _=>rfl,guard0 u,u,e⟩
variable (f:Ratio a s)(L: Pad Y H C g.count.val)(T:4≤a.val)(W:f.count=H.whole){d:ℝ}(e:Sound Y H C d)
-- ease every point true even off Permit; anchor motion
lemma appearL (x:Site s) : (C.live (ChillF Y g ∅ C.blockY) x)=1:=by
 apply Sized.live_far; apply (Knob.stepZ ..).2 ⟨le_rfl,fun y u=>False.elim (u (show y∈ _ from Or.inr (emptyB ..)))⟩
lemma spectra (x:Site s) : (homeScript Y i).HH C g ∅ 1 f x=(homeScript Y i).port C x :=by unfold Script.HH; rw [appearL]; simp
include L T W
lemma starRise (x:Site s):(homeScript Y i).XX C g ∅ 1 f x=(homeScript Y i).over x:=by -- no Sound needed by direct
 let D:=homeScript Y i; rw [Script.XX, Hero.enter_here,Script.guardX,if_pos (show x∈ _ from Or.inr (emptyB ..))]; exact Hero.pin_safe f (ChillF Y g ∅ C.blockY) x T (fun _ _=>Or.inr (emptyB ..))
-- actual hom root. projection values agreement in deep Price Terms
lemma homX_band {j:Y.Index}{x:Site s}(hx:x∈Y.band j) : (homeScript Y i).XX C g ∅ 1 f x=if Y.D j then apex else scaledV (locus i) apex:=by rw [starRise Y g i C f L T W,Script.over_band _ _ _ hx]; rfl
include e
-- with parameters. rotation at N
lemma hom_H {j:Y.Index}{x:Site s}(hx:x∈Y.band j) : (homeScript Y i).HH C g ∅ 1 f x 2= if Y.D j then BB else BBz i:=by
 rw [spectra Y g i C f x]; let D:=homeScript Y i; have P:=home_here Y g i C d e.fields.le; rw [P.seatM _ _ _ _ _ L hx]; change (if _ then BM 1 else side i) 2= _; split; exact BM_1 (by norm_num); unfold side; rw [BM_1 (by norm_num),BBz_eq] -- tune
end YM.CF.BProof.Trek
