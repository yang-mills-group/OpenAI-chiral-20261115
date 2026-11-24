import YM.CF.BPress.Hazel.Atlas
import YM.CF.BPress.Locale.Play
/- N collar amendment. Before any activation taper. Uniform costs across depth- & parameter change. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Hazel
open Function Finset Filter NormedSpace Metric SU SU.Pair Lat Fock Lattice Cube Spin Spin.Paint Dial Lute Lute.Kite Lute.Fort Lute.Music Meadow MeasureTheory Net Meadow.Tent Sheet
open scoped Topology BigOperators NNReal Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ContDiff Classical
attribute [local instance] opCStarAlgebra
variable {s :Side}{B:BandWidth}{u v γ : ℝ} (z: Fin 5)
open Grid Wealth Tunnel Locale Bands Branch Clipγ Letter Meadow.Frame Meadow.Stamps
variable {B: BandWidth} {T: BPress.Sheet.Atlas}{Lf C C' y:ℝ}{a:ℕ} (X:Bands s B)(F:Net s T Lf y C C' a)(k:Tiling s) (w:X.Slates)(U:Micro s)
namespace Letters
-- $z$ orientation after gauge fix. labels are parametrized by T.give. Pack(X,w).
def orientation (i:X.Index) : Sheet.Law s:= if i∈ X.dc then (w (i+1)).1 else (w i).2
abbrev code : X.Hcols→ Fin 5:= fun p=> orientation X w p.1 p.2
lemma orientation_left {i:X.Index}(h:i∉ X.dc): orientation X w (i-1)= (w i).1:=by rw [orientation,if_pos ((X.dc_index _).mpr ((X.next_prev _).mpr (fun x=> h ((X.dc_index ..).2 x)))),sub_add_cancel]
lemma orientation_right {i:X.Index}(h:i∉X.dc):orientation X w i=(w i).2:= if_neg h
abbrev window (i:X.Index):= horizontal (X.depth i B.D) U
def launch : X.Slates := w -- not used tune
abbrev knot (i:X.Index):= X.putF T y U i (w i)
def centerH (T : BPress.Sheet.Atlas)(y:ℝ) (i:X.Hcols) := T.frame y (window X U i.1) (orientation X w i.1) i.2 -- arg order T y tune
lemma centerL (T : BPress.Sheet.Atlas)(y:ℝ){i:X.Index}(p:i∉X.dc)(x:Tri s): centerH X w U T y (i-1,x)= (knot (T:=T) (y:=y) X w U i).1 x:=by
 unfold knot putF centerH; dsimp only; rw [if_neg p,orientation_left X w p, window, left_shadow (mem_sdiff.mpr ⟨mem_univ i,p⟩)]; rfl -- tune orientation proof period
lemma centerR(T : BPress.Sheet.Atlas)(y:ℝ){i:X.Index}(p:i∉X.dc)(x:Tri s): centerH X w U T y (i,x)= (knot (T:=T) (y:=y) X w U i).2 x:=by
 unfold knot putF centerH; dsimp only; rw [if_neg p,orientation_right X w p,window,right_shadow (mem_sdiff.mpr ⟨mem_univ i,p⟩)]; rfl
lemma canopy (T : BPress.Sheet.Atlas)(y:ℝ){i:X.Index}(p:i∉X.dc)(x:Site s)(v:x∈X.band i):haloM (X.mark i) (knot (T:=T) (y:=y) X w U i) x=centerH X w U T y (panel X x):=by
 let t:= corner (X.mark i) x; have ht:t ≤(X.mark i).n.val:=Hazel.corner_rank v; unfold haloM book; rw [if_pos (show x∈(X.mark i).mem from v)]; unfold Locale.panel; rw [show moment X (x 0)= _ from (by rw [ Tent.corner_path (X.mark i) x, band_time X i ht] : moment X (x 0)= if t ≤ (X.mark i).cut then i-1 else i)]; unfold Tunnel.access; split; next h=> dsimp only; unfold t corner at h; rw [if_pos h]; exact (centerL X w U T y p _).symm
 next h=> dsimp only; unfold t corner at h; rw [if_neg h]; exact (centerR X w U T y p _).symm

lemma warm_body (i:X.Index) : Warm B ≤ Tent.body (X.mark i):=by unfold Warm Tent.body; rw [mark_n]; omega
lemma warm_o {i:X.Index}{x:Site s}(v: burial (X.mark i) x ≤ Warm B): Meadow.depthP (X.mark i) x ≤1/10:=by
 unfold depthP; rw [div_le_div_iff₀ (nPos _) (by norm_num),one_mul]; exact_mod_cast (show burial _ _*10 ≤ B.marked.val from (by unfold Warm at v; omega))

abbrev vocal (i:X.Index)(v:ℝ): Paint s:= brush F U (knot (T:=T) (y:=y) X w U i) k X i v -- tune T y implicit
abbrev little(i:X.Index):= plant F U (knot (T:=T) (y:=y) X w U i) k X i

def ballot : Letter X :=⟨centerH X w U T y, code X w, little X F k w U, vocal X F k w U⟩
lemma bottle (p:X.hold U) : (ballot X F k w U).Tint:=by
 let A:= ballot X F k w U; constructor; · intro i; exact paid ..
 · intro i h x u; change (plant _ _ _ _ _ _ _) = _ ∧ ∀ v,vocal X F k w U i v x= _; unfold Stamps.plant vocal Stamps.brush; rw [if_pos h, if_pos h]; exact ⟨rfl,fun _=> theme_o _ _ (by norm_num)⟩
 intro i h x v u; have hv: (X.mark i).axial U=1:= no_axial (X.mark i) U (fun j hj=>p _ (X.poles_s i (by rw [storesN,if_neg h]; exact hj)))
 let p':= knot (T:=T) (y:=y) X w U i; let W:=X.mark i; have hx:x∈ Meadow.cloak W (Tent.body W):=mem_filter.mpr ⟨v,u.trans (warm_body X i)⟩; have he:haloM W p' x= A.frameN x:= canopy X w U T y h x v
 constructor; · change plant F U p' k X i x=_; unfold Stamps.plant sprigs ferns headM; rw [if_neg h,hv,inv_one,shuffle_one,if_pos hx]; change scaledV ((haloM W p') x)⁻¹ _=_; rw [he] -- tune
 intro t; change brush F U p' k X i t x = swivelC (A.frameN x)⁻¹ _; unfold Stamps.brush Meadow.Frame.whole stalk; rw [if_neg h,hv,inv_one]; change swivelC 1 _=_; rw [turn_one]; dsimp only; unfold W at hx; rw [if_pos hx, show (haloM (X.mark i) p' x)⁻¹= (A.frameN x)⁻¹ from congrArg _ he,theme_o _ t (warm_o X u)]
end Letters
end YM.CF.BPress.Hazel
