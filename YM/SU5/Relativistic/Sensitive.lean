import YM.SU5.Relativistic.ChiralMark
import YM.SU5.Selected.Highlite
import YM.CF.Buffered.Crowns

/-! Probes using both sorts of variables, at FIXED testing resolution. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 25000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function NormedSpace Filter Metric Lattice Cube Finset MeasureTheory RG Wilson
open Lat Mir Phase RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Scree Window Vale Girt Lifted
open Py Py.Rate LocalLimit Preparation Satin Heat Fock SlabMark PhaseChoice Push.SectorMeasure
open Tapestry Tapestry.Altitude Tapestry.Exhibition
open CF.Pannier.Chancel CF.Pannier.Chancel.Cliplet
open Reliance ShortWave
open Tower.Selected Vacancy
open Journey
open Reed (Fine think)
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra

section family
variable {J:Calibration}
def probesMatter (f:Family J):Prop:= ∀ m:Side, evanescent (f m)
/-- Low curvature on every plaquette implies mark zero, regardless of matter or Loom data. -/
def probesGauge (t:ℝ)(f:Family J): Prop:= ∀ m: Side,∀ x:Fields (J.c m), flags t x.1=∅ → f m x=0
variable {f g:Family J}
lemma probesMatter.zeroM : probesMatter (0:Family J) := fun _ _=> act_zero _
lemma probesMatter.plusM (h : probesMatter f)(t:probesMatter g): probesMatter (f+g):= by
  intro i x; change acts (f i x+g i x) _=0; rw [act_add,h i x,t i x,zero_add]
lemma probesMatter.smulM (h:probesMatter f)(c:ℂ): probesMatter (c • f):= by
  intro i x; change acts (c • f i x) _=0; rw [act_smul,h i x,smul_zero]
lemma probesMatter.mulM (f:Family J)(h:probesMatter g): probesMatter (f*g):= by
  intro i x; change acts (f i x *g i x) _=0; rw [act_mul,h i x,map_zero]
lemma probesMatter.twistM {S:Finset Cover}{wide b:Bool} (h:probesMatter f)(g:InTest J wide S b f)(i:Axis)(z:ℤ): probesMatter (mirror J i z f):= fun k=> mirror_ev (g.support k) (h k) i z

variable {S:Finset Cover}{k:ℕ}{b:Fin k→ Cover}{z:SU.Slot} {U : Window.Family}

private lemma probed_atom {L : List (Fin k)} (h:CRow J U b S L f)(p : L ≠ []) : probesMatter f:=by
  induction h with
  | zip=> exact probesMatter.zeroM
  | glaze _ _ ih=> exact probesMatter.smulM (ih p) _
  | fuse _ _ a b=> exact probesMatter.plusM (a p) (b p)
  | gave=> contradiction
  | @pair j y c d x a f l h hx hc hd θ' θ hl g ih=>
    -- rightmost tails may be [] but always chiral, hence map basis occupied to
    -- scalar multiples. One nonempty pair kills it.
    intro i v
    have hg:InTest J false S true (creation J y d x):= .creator x hd θ'
    obtain ⟨z,_,hk⟩:= grassmann ((g.inTest.support i).allV v)
    have ht:=grassmann_odd ((hg.support i).allV v)
    change acts (((removal J (b j) c a i v)*(creation J y d x i v))*f i v) (basisKet (Tset (J.c i)))=0
    rw [act_mul,hk,map_smul,act_mul,ht,map_zero,smul_zero]
lemma probed_lode (p:f∈ Lode J U b S) : probesMatter f:=by
  apply Submodule.span_induction (p:=fun x _=> probesMatter x) ?_ probesMatter.zeroM (fun _ _ _ _=> probesMatter.plusM) (fun _ _ _ h=> h.smulM _) p
  intro f h; obtain ⟨L,p,k,f⟩:= h; exact probed_atom f p
lemma probed_base (p:f∈ Filigree J U b S): probesMatter f:= by
  apply Submodule.span_induction (p:=fun x _=> probesMatter x) ?_ probesMatter.zeroM (fun _ _ _ _=> probesMatter.plusM) (fun _ _ _ h=> h.smulM _) p
  intro f h; obtain ⟨x,z,g,p,rfl⟩:=h; exact (probed_lode g).mulM _

variable (j:Axis) (u v:Cover)
lemma cadTestFull (S:Finset Cover) (u:Cover) (l:List Axis) (wide b:Bool) (p:InTest J wide S b f):
    InTest J wide (drivePlot u J l S) b (cad J l u f):=by
  induction l with
  | nil=> exact p
  | cons j l ih=> exact flow_port J _ _ ih
lemma relocatedMatter {f:Family J} (p:InTest J true S false f) (t:probesMatter f)(l:List Axis)(u:Cover): probesMatter (cad J l u f):=by
  induction l with
  | nil=> exact t
  | cons i l ih=>
    exact probesMatter.twistM (ih.twistM (cadTestFull S u l _ _ p) i 0) (axial J i 0 (cadTestFull S u l true false p)) i _
lemma coal_remains {n:Side}(t:ℝ)(x:Pane n)(i:Axis)(s:ℤ)(h:flags t x=∅):
    flags t (fling i s n x)=∅:= by
  have ht := coal_flags i s t x; rw [h] at ht
  unfold hyphen at ht; exact Finset.image_eq_empty.mp ht
lemma probesGauge.twistG {t:ℝ} {f:Family J}(p:probesGauge t f)(i:Axis)(s:ℤ): probesGauge t (mirror J i s f):=by
  intro m x h; unfold mirror reflMark; rw [p m (reflFields i s x) (coal_remains t x.1 i s h), theta_zero]
lemma probesGauge.relocatedGauge {f:Family J}{t:ℝ} (p:probesGauge t f)(l:List Axis)(u:Cover): probesGauge t (cad J l u f):=by
  induction l with
  | nil=>exact p
  | cons i l ih=> exact probesGauge.twistG (probesGauge.twistG ih i 0) i _
lemma probesGauge.mulG {t:ℝ}{f:Family J} (g:Family J)(p:probesGauge t f): probesGauge t (g*f):=by
  intro i x h; change _*f i x=0; rw [p i x h,mul_zero]
lemma tinted_weight {n:ℕ} (h: 0 < n) {w:ℝ} {f:Family J} {z: Fin n→ Cover}
    (p:∀ (m: Side) (v:Fields (J.c m)) (r:Fin n), SU.group.chord (faceValue (onC _ v.1) (facet (z r))) ≤ w → f m v=0): probesGauge w f:=by
  intro m x h'
  let i:Fin n:=⟨0,h⟩
  refine p m x i ?_
  rw [Reliance.ShortWave.tile_face]; exact (Crust.flags_calm x.1 w).1 h' _
-- concrete non-independence from first field and not pointwise scalar ever on hosts
lemma not_idle {x:Family J}(m:Side){S:Finset Cover}(h:InTest J true S false x)(p:Hosp S (J.c m))(hx:x≠0):∃ z:Fields (J.c m), x m z≠0:=by
  by_contra! t
  exact hx (Tower.box_ext J S h InTest.zero p (funext t))
lemma gauge_fluid {N:Side}(w:ℝ)(v:0≤w): flags (G:=SU.group) w (1:Pane N)=∅ := by
  rw [Crust.flags_calm]; rintro p; simp [faceValue, square, travel, v]
lemma true_sensitivity {x:Family J} {S:Finset Cover} {w:ℝ} (p:x≠0)(m:Side) (v:Hosp S (J.c m)) (g:InTest J false S false x)
    (h:probesMatter x) (u:0 < w) (k:probesGauge w x):
    ∃ z : Pane (J.c m), (∀ y, x m (1,y)=0 ∧ x m (z,y) ≠ 0) ∧
      w > 0 ∧ (∃ i: Face (Per (More (J.c m))), w < SU.group.chord (faceValue z i)) ∧
      ∀ c:ℂ, x m (z,z) ≠ c • (1:FC _):=by
  obtain ⟨⟨z,y⟩,hy⟩:= not_idle m g.widen v p
  have ht:∀ i j, x m (z,i)=x m (z,j):=by
     obtain ⟨a,t,u⟩:=g.only_cont m
     rw [t]; intros; rfl
  have he : ¬flags (G:=SU.group) w z=∅:=fun t=> hy (k m (z,y) t)
  rw [Crust.flags_calm] at he; push Not at he
  refine ⟨z,fun j=> ⟨k m (1,j) (gauge_fluid w u.le),ht y j ▸ hy⟩,u,he,?_⟩
  intro c v; have hh:=h m (z,z); rw [v,act_smul,act_one] at hh
  rw [(smul_eq_zero.mp hh).resolve_right (by apply norm_pos_iff.mp; simp [basisKet]),zero_smul] at v
  exact hy ((ht y z).trans v)
end family
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.true_sensitivity
