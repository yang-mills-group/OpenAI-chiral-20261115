import YM.CF.BProof.Charge.Stove

/- Rows for vertical plaquettes; price uses actual field and its first horizontal step
from D face. Keep data anchored in one column. `shade` = preceding linear coordinate. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Charge
open Function Filter RG Wilson Lattice Finset Work Micro MeasureTheory Mag Form Angular Angular.Yard AnalyticBridge.SectorAffine
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
local notation "G"=> SU.group
variable {s:Side}(Y:Yard s)(M:ℕ)(b:Y.Door)(W:Y.Branch)(U:Config G s)

def shade := Y.spec (project Y b.1.2 b.2.2 b.1.1 b.2.1.val) W
lemma shading : Y.roll W (Y.side b)= shade Y b W:= by
 unfold side shade; rw [roll_c,heir_h,gap_find _ _ _ _ _ b.2.1.isLt.le]
lemma attends (V:Y.Branch)(h:∀ a:Y.Door,a.1=b.1→ V a=W a): shade Y b W=shade Y b V:=by
 unfold shade project; split; exact rfl; change W (b.1,⟨b.2.1.val-1,_⟩,b.2.2) = V (b.1,⟨_,_⟩,_); exact (h (b.1,⟨b.2.1.val-1,_⟩,b.2.2) rfl).symm
lemma echo : curlP 1 (Y.rise b) (Y.roll W)=if Y.D b.1.1 then W b-shade Y b W else shade Y b W-W b:= by
 let a:=b.1; let i:=a.1; let p:=a.2; let d:=b.2.1; let x:= Y.dawn i d; let k:=b.2.2; let Z:=Y.roll W
 have hg (x:Per s) : curlP 1 (nf x p k) Z= Z (horiz (x+1) p k)- Z (horiz x p k):=by
    rw [curl_px]; simp only [part_one]; change Z (vert x p)+ Z (join x p+step 0,k.succ)- Z (join x p+step k.succ,0)-Z (horiz x p k)=_; rw [← join_step,←step_join,show (join x (p+tstep k),0)=vert x (p+tstep k) from rfl, show Z (vert x p)=0 from roll_v .., show Z (vert x (p+tstep k))=0 from roll_v ..,zero_add,sub_zero]; exact rfl
 rw [← shading,show Y.rise b=nf x p k from rfl,hg,show x+1=_ from (Y.sequence i d).symm, ← Y.roll_inter W b]; change Z (horiz (Y.dusk i d) p k)-Z _=if Y.D i then _ else _; unfold dusk x dawn; split<;> rfl
lemma model_one (T:PathData SU.group)(c:Clip)(β:ℝ): Form.Q T M c β (.inl (Y.rise b)) (Y.roll W)= (β*c.direct)* ‖W b-shade Y b W‖^2/2:=by
 change (β*c.direct)* ‖curlP 1 (Y.rise b) (Y.roll W)‖^2/2=_; rw [echo]; split; rfl; rw [norm_sub_rev]
lemma rise_h (g:Y.Flat U) : SU.group.chord (faceValue U (Y.rise b))= cd G (U (Y.inter b)) (U (Y.side b)) := by
 let p:=b.1.2; let o:=b.1.1; let d:=b.2.1; let i:=b.2.2; let x:=Y.dawn o d; let l:=U (horiz (Y.dawn o d) p i); let k:=U (horiz (Y.dusk o d) p i); let a:=U (Y.side b); let b':= U (Y.inter b); have hv(p:Space s): U (vert x p)=1:=g (Y.trunk_g p (Y.dawn_open ..))
 have hu(x y:SU.E): SU.group.chord (x*y⁻¹)=cd G x y:=by rw [← cd_mul_right G y⁻¹, mul_inv_cancel, cd_symm,cd_one]
 rw [show Y.rise b=nf x p i from rfl,nfc, hv,hv,curl]; simp only [one_mul,inv_one,mul_one]; rw [hu, (Y.sequence o d).symm] -- tune rewrites x+1 cannot syntactic
 change cd G k l=cd G b' a; unfold l k dawn dusk; split; exact rfl; exact cd_symm G _ _

variable {M W U} {S:Hall s}{F:Y.FaceS}{κ y:ℝ}
lemma rise_tone (s₀:Y.Evap κ y U W)(e:Y.Climate y S U F)(p:b.1∉Y.severe κ y U) : Tall y (Y.roll W) M U (.inl (Y.rise b)):= by
 let o:=b.1.1; let d:=b.2.1; let p':=b.1.2; let n:=b.2.2; let x:=Y.dawn o d; have hv:along (Y.v o) x< Y.short:= Y.dawn_open ..
 have hh(p:Space s): Tone (Y.roll W) y (vert x p) U:= by
    apply Y.thirst W s₀ _ _ (Y.roll_v x p W); rw [mag_v,show U (vert x p)=1 from e.flat (Y.trunk_g p hv),cd_self]; exact (coin_pos ..).le
 intro i; rw [show sendEdge (1:Signed) 0 (positions _ i)=positions (Y.rise b) i from by unfold sendEdge; simp only [Step.rotate_one, Step.used,posDir,Bool.false_eq_true,↓reduceIte, Prod.mk.eta,affine,Signed.act_one,add_zero]] -- `Tall` let
 fin_cases i
 · exact hh p'
 · change Tone (Y.roll W) y (join x p'+step 0,n.succ) U; rw [← join_step]; exact Y.tone_gap W e s₀ o (x+1) p' (by unfold Gap; rw [along_succ]; exact hv; have :=Y.dD; omega) n p
 · change Tone _ y (join x p'+step n.succ,0) _; rw [← step_join]; exact hh (p'+tstep n)
 exact Y.tone_gap W e s₀ o x p' hv.le n p
end YM.CF.BProof.Charge
