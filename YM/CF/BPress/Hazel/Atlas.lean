import YM.CF.BPress.Hazel.Tonic
import YM.CF.BPress.Hazel.Centers
/- N collar amendment. Before any activation taper. Uniform costs across depth- & parameter change. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Hazel
open Function Finset Filter NormedSpace Metric SU SU.Pair Lat Fock Lattice Cube Spin Spin.Paint Dial Lute Lute.Kite Lute.Fort Lute.Music Meadow MeasureTheory Net Meadow.Tent Sheet
open scoped Topology BigOperators NNReal Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ContDiff Classical
attribute [local instance] opCStarAlgebra
variable {s :Side}{B:BandWidth}{u v γ : ℝ} (z: Fin 5)
open Grid Wealth Tunnel Locale Bands Branch Clipγ
variable {X:Bands s B}
structure Letter (X:Bands s B) where
 h:X.Hcols→ E
 z:X.Hcols→ Fin 5
 plant:X.Index→ Meadow.marks s
 brush:X.Index→ℝ→Paint s
namespace Letter
variable (W:Rental)(A:Letter X){x: Site s}{i j:X.Index}
abbrev color (x:Site s):= A.z (panel X x)
abbrev frameN (x:Site s):= A.h (panel X x)
structure Tint (A:Letter X):Prop where
 clock (i:X.Index): Clue (X.band i) (A.plant i) (A.brush i)
 curbD (i:X.Index)(h:i∈ X.dc)(x:Site s)(p:x∈X.band i): A.plant i x= Seed ∧ ∀ v, A.brush i v x=B_theme (α v)
 curbN (i:X.Index)(h:i∉ X.dc)(x:Site s)(p:x∈X.band i)(u: burial (X.mark i) x≤ Warm B): A.plant i x= scaledV (A.frameN x)⁻¹ Seed ∧ ∀v,A.brush i v x= swivelC (A.frameN x)⁻¹ (B_theme (α v))

def correction(i:X.Index)(x:Site s) : Prop:= i∉ X.dc∧ burial (X.mark i) x ≤ W.H.val -- tune A drops
-- stitched
abbrev zoneD (x:Site s):= adult X (town X x) x
def G : Meadow.marks s:= fun x=> if p:Welkin X x then A.plant (citizen X x p) x else beacon (A.color x) (zoneD (X:=X) x)
abbrev amend (x:Site s)(i:X.Index)(v:ℝ):=castN (A.frameN x) (A.color x) (gamma W.H (burial (X.mark i) x)) v
def H(v:ℝ)(x:Site s):Op Slot:= if p: Welkin X x then if correction W (citizen X x p) x then A.amend W x (citizen X x p) v else A.brush (citizen X x p) v x else dict (A.color x) (zoneD (X:=X) x,v)
-- equality laws all inputs including near patches (clan uses halo of wing not Field).
lemma Gband (p:x∈ X.band i) : A.G x= A.plant i x:=by unfold G; rw [dif_pos (show Welkin X x from ⟨_,p⟩), citizen_t X p]
lemma Gmiss (p:¬ Welkin X x): A.G x=beacon (A.color x) (zoneD (X:=X) x):=dif_neg p
lemma Hband (p:x∈ X.band i) (v:ℝ): A.H W v x= if correction W i x then A.amend W x i v else A.brush i v x:=by unfold H; rw [dif_pos (show Welkin X x from ⟨_,p⟩),citizen_t X p]
lemma Hmiss (p:¬ Welkin X x)(v:ℝ): A.H W v x=dict (A.color x) (zoneD (X:=X) x,v):=dif_neg p -- meta implicit X tune
variable (P:A.Tint)
include P
lemma Hclan0 (p:x∈X.band i) (u: i ∈ X.dc)(v:ℝ): A.H W v x=B_theme (α v):=by rw [A.Hband W p, if_neg (fun h=>h.1 u)]; exact (P.curbD i u x p).2 v
lemma HclanN (p:x∈ X.band i)(u:i∉ X.dc)(t:burial (X.mark i) x ≤ Warm B)(v:ℝ): A.H W v x=A.amend W x i v:=by
 rw [Hband W A p]; split; rfl; next h=> rw [amend,full (le_of_lt (lt_of_not_ge (fun t=> h ⟨u,t⟩))),cast_pure,(P.curbN i u x p t).2]
-- H_on_face in Gap: both values equal equiv ideal by none (D face), or `closeC h z` (N face).
variable {R:Hangar s}
lemma Hfront (p:x∈X.gap i)(t:x∈X.band j)(u:j∉ X.dc)(v:ℝ): A.H W v x= swivelC (closeC (A.frameN x) (A.color x)) (dict (A.color x) (zoneD (X:=X) x,v)) := by
 have ht:= death_gap X t p; rw [HclanN W A P t u (by omega), amend, ht, Clipγ.dark (show 0*8 ≤ W.H.val by omega),castN,neon_face]; unfold zoneD adult; rw [moment_gap X p, at_face X p t,if_neg u,div_self (by positivity [B.D_pos])]
lemma Heart_face(p:x∈X.gap i)(t:x∈X.band j)(u:j∈ X.dc)(v:ℝ) : A.H W v x= dict (A.color x) (zoneD (X:=X) x,v):=by rw [Hclan0 W A P t u]; unfold zoneD adult; rw [moment_gap X p, at_face X p t,if_pos u,Nat.cast_zero, zero_div,edge_west]
lemma H_band_last (d: W.M ≤ Warm B) (p:x∈X.band i)(t: 2 ≤ u): A.H W u x=A.brush i u x:=by
 rw [A.Hband W p]; split; next v=> rw [amend,cast_final _ _ t,(P.curbN i v.1 x p (v.2.trans (d.trans' ((Nat.le_succ _).trans W.hm)))).2, alpha_final (show 1/2≤u by linarith), shape_cost.tail]
 next h=> rfl
lemma H_later (d: W.M ≤ Warm B)(p:x∈X.band i)(t:2≤u): A.H W u x=A.brush i 2 x:=by rw [H_band_last W A P d p t, (P.clock i).station u (by linarith), (P.clock i).station 2 (by norm_num)]
lemma Gfront (p:x∈ X.gap i)(t:x∈ X.band j)(u:j∉ X.dc): A.G x= scaledV (closeC (A.frameN x) (A.color x)) (beacon (A.color x) (zoneD (X:=X) x)):=by
 rw [A.Gband t, (P.curbN j u x t (by have he:=death_gap X t p; omega)).1]; unfold zoneD adult; rw [moment_gap X p, at_face X p t,if_neg u,div_self (by positivity [B.D_pos])]; rw [show beacon (A.color x) 1= scaledV (orb (A.color x)) Seed from Subtype.ext (by exact (light_cost ..).tail)]; rw [←scaled_s, closeC,orb,mul_assoc,mul_inv_cancel,mul_one]
lemma Gface (p:x∈ X.gap i)(t:x∈ X.band j)(u:j∈ X.dc): A.G x= beacon (A.color x) (zoneD (X:=X) x):=by
 rw [Gband A t,(P.curbD j u x t).1]; unfold zoneD adult; rw [moment_gap X p,at_face X p t,if_pos u,Nat.cast_zero,zero_div]; exact Subtype.ext ((light_cost _|>.head).symm)
-- Mark progress for whole
lemma Hplan(x:ℝ): MatPlan (A.H W x):=by
 intro i; by_cases p: Welkin X i; rw [Hband W A (show i∈ X.band (citizen X i p) from p.choose_spec)]; split; exact cast_plan ..; exact (P.clock _).scheme x i
 rw [Hmiss W A p]; exact (dict_s _ _ (age_t X (noWel X p))).1
lemma Hsmooth(x:Site s) : ContDiff ℝ ∞ (fun t=> A.H W t x):=by
 unfold H; split; split; exact cast_smooth ..; exact (P.clock _).smooth x; next h=> exact d_smooth _ (age_t X (noWel X h))
lemma H_seed (d:W.M ≤ Warm B)(x:Site s): A.H W 0 x=fullM (A.G x).val:=by
 unfold H G; split; next h=> split; rename_i t; rw [amend,cast_seed,(P.curbN _ t.1 x h.choose_spec (t.2.trans (d.trans' ((Nat.le_succ _).trans W.hm)))).1]; exact (P.clock _).origin x
 next h=> exact x_z _ (age_t X (noWel X h))
lemma H_pace (x:Site s): LipschitzOnWith priceTone (fun t=>A.H W t x) Meadow.active:=by
 unfold H; split; next h=> split; exact cast_healthy _ _ (lit ..); exact ((P.clock _).pace x).weaken Ω_theme
 next h=> exact o_cost _ _ (age_t X (noWel X h)) (feed _).1
end Letter
end YM.CF.BPress.Hazel
