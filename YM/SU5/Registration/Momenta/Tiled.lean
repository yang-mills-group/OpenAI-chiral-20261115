/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SU5.Registration.Momenta.Paint
import YM.Work.C17
import YM.Work.C20
import YM.Work.C21
/-!
 # Tiled: Full Body matches actual P on analytic Charts (& estimated boost price).
 Verbatim adaptations from Work/C20,C21. For the polarized spin budget of M12;
 obtains smooth (actually analytic on REAL points) helio read price, all distinct poses. Not assuming C∞.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinWFixed
open Function Set Filter Distribution MeasureTheory Mink Mink.Poincare Boundary
open _root_.YM.Boundary.Probe
open scoped Topology BigOperators ContDiff InnerProductSpace
variable {V:Type*} [AddCommGroup V] [Module ℂ V] {W:WView V} {n:ℕ}
namespace Palette
open Metric NearPair Complex
variable {D : ∀ n, Blanket n}{Z:Palette W D} {F:InkWaves V}
open Work.C20
-- Helio is actually smooth on all distinct poses. Need full region between sides/ties. Only after M12 costs.
lemma views (hF:Z.FullBody F)(v:Fin n→V) {q:Points n}(p:q∈ Wheeled n) : F.entrance q v = Z.emit v (wickSlice n q):=by
 rw [wick_glow,hF.pure n _ _ _ (show readings q ∈ east n from p),InkWaves.restricted,trace_place']; exact congrArg (fun y=> F.F n y _ v) (funext (fun i=> by simp only [Boundary.shift,place,points_apply,time_position,Pi.zero_apply,ofReal_zero,zero_add]; rfl))
variable {R:Courts V}(p':F.Region)(h:R.Carriage F)
include h p'
lemma terrace (hF:Z.FullBody F)(v:Fin n→V) : AnalyticOnNhd ℝ (fun x=> helio R F n x v) (conf n):=by
 intro x hx; obtain ⟨U,f,u⟩:= origin_exists hx; let M := (wickSlice n).comp (podium U).toContinuousLinearEquiv.toContinuousLinearMap
 have hp:M x∈tube n:= wick_tube (show reFrame U x ∈ ordered n from u)
 refine ((AnalyticAt.restrictScalars (hF.hol n (reSup U R v) _ hp) |>.comp (?_ : AnalyticAt ℝ (⇑M) x)).congr ?_) -- order of args?
 · exact M.analyticAt x
 filter_upwards [(conf_open n).mem_nhds hx, ((podium U).continuous.tendsto x).eventually ((wheel_open n).mem_nhds u)] with y h' hz
 change Z.emit _ (wickSlice n (reFrame U y))= _
 rw [helio_price h p' y U h' f hz]; exact (views hF _ hz).symm
lemma tiled (v:Fin n→V)(P:NearPair n)(x:Points n): helio R F n (P.switch x) (v ∘ P.s)=helio R F n x v:=by
 let g:Frames n:= (1,P.s); rw [show P.switch x=reFrame g x from PiLp.ext (fun i=>(Ortho.move_one _).symm), show (v∘P.s)=reSup g R v from funext fun i=> (R.eu1 _).symm]; exact helio_carries h p' g Courts.proper_one x v
lemma emit_terrace (hF:Z.FullBody F)(v: Fin n→V){q:Points n}(hq:q∈ordered n) : Z.emit v (wickSlice n q)=helio R F n q v:=by rw [helio_local h p' _ (show q∈Wheeled n from hq), views hF v (show q∈Wheeled n from hq)]
theorem tiled_panes (hF:Z.FullBody F) (v:Fin n →V)(y:Heights n)(X:NearPair n)(A: PairedPanes X Z v y) : A.sameGround:=by
  intro x hx hz
  let p := place (Boundary.trace x) y
  let M := wickSlice n
  let f := (A.original x hx).extendF
  let g := (A.tilted x hx).extendF
  have hy : X.spectator y := A.permitted.willing
  have hup : readings p = y := readings_place ..
  have hvp : readings (X.switch p) = y := same_height hy.1 _
  have hp := euclid_conf hy hx
  have hspace : Boundary.trace p = Boundary.trace x := by funext i; simp [Boundary.trace, p, place]
  have hx0 : readings x = 0 := funext hz
  have hM : M p = glow x (dawn y) := by
    unfold M
    rw [wick_glow, hup, hspace, ← hx0, place_same]
  change f =ᶠ[𝓝 _] g
  have ha : AnalyticAt ℂ f (M p) := hM.symm ▸ (A.original x hx).doc
  have hb : AnalyticAt ℂ g (M p) := hM.symm ▸ (A.tilted x hx).doc

  let C:=fun x => helio R F n x v
  have hC: ContDiffAt ℝ ∞ C p := AnalyticAt.contDiffAt (terrace p' h hF v p hp)

  have hu : Tendsto M (𝓝[ordered n] p) (𝓝[tube n] (glow x (dawn y))) := by
    rw [← hM]
    exact M.continuous.continuousWithinAt.tendsto_nhdsWithin wick_tube
  have heq : f ∘ M =ᶠ[𝓝[ordered n] p] C := by
    have hf : f ∘ M =ᶠ[𝓝[ordered n] p] Z.emit v ∘ M := hu.eventually (A.original x hx |>.fits)
    refine hf.trans ?_
    filter_upwards [self_mem_nhdsWithin] with i hi using emit_terrace p' h hF v hi

  let V : Set (Points n) := X.switch ⁻¹' ordered n
  have hu' : Tendsto M (𝓝[V] p) (𝓝[X.name ⁻¹' tube n] (glow x (dawn y))) := by
    rw [← hM]
    refine M.continuous.continuousWithinAt.tendsto_nhdsWithin fun u hu => ?_
    change X.name (wickSlice n u) ∈ tube n
    rw [wick_name]; exact wick_tube (show X.switch u ∈ ordered n from hu)
  have heq' : g ∘ M =ᶠ[𝓝[V] p] C := by
    have hg : g ∘ M =ᶠ[𝓝[V] p] ((Z.emit (v ∘ X.s)) ∘ X.name) ∘ M :=
      hu'.eventually (A.tilted x hx |>.fits)
    refine hg.trans ?_
    have hn : ∀ᶠ u in 𝓝[V] p, u ∈ conf n :=
      Eventually.filter_mono nhdsWithin_le_nhds ((conf_open n).mem_nhds hp)
    filter_upwards [self_mem_nhdsWithin, hn] with u hu hc
    simp only [Function.comp_apply, M, wick_name]
    exact (emit_terrace p' h hF (v ∘ X.s) (show X.switch u ∈ ordered n from hu)).trans
      (tiled p' h v X u)

  rw [← hM]
  refine complex_germ ha hb (wick_span n) fun m => ?_
  have hm : ContDiffAt ℝ m C p := hC.of_le (WithTop.coe_le_coe.mpr le_top)
  have hf : ContDiffAt ℂ m f (M p) := ha.contDiffAt
  have hg : ContDiffAt ℂ m g (M p) := hb.contDiffAt
  have hne := ordered_neBot (q := p) (hup.symm ▸ before_east hy)
  have hne' := switch_neBot X (q := p) (hvp.symm ▸ before_east hy)
  exact (jets_on_open_side (ordered_open n) hne heq m ((hf.restrict_scalars ℝ).comp p M.contDiff.contDiffAt)
    hm).trans (jets_on_open_side ((ordered_open n).preimage X.switch.continuous) hne' heq'.symm m
      hm ((hg.restrict_scalars ℝ).comp p M.contDiff.contDiffAt))


omit h p'
open Work.C21
theorem realizes_panes (hF:Z.FullBody F) (v:Fin n→V)(y:Heights n)(P:NearPair n)(A:PairedPanes P Z v y) : A.Forms:=by
  constructor
  · intro x hx
    refine realize (V := fields n) (fun _ => Iff.rfl) (A.permitted.first x) (A.original x hx) (fun z hz => ?_)
      (Z.sees hF v _ A.permitted.here (modified _))
    exact (hF.hol n v).continuousOn.comp_continuous ((home n).comp (continuous_id.prodMk continuous_const))
      (fun _ => show shade (glow _ z) ∈ fields n by simpa using hz)
  intro x hx
  let V := P.switch ⁻¹' fields n
  have hV p : p ∈ P.name ⁻¹' tube n ↔ shade p ∈ V := by
    change shade (P.name p) ∈ fields n ↔ P.switch (shade p) ∈ fields n
    simp [NearPair.name]
  refine realize hV (A.permitted.second x) (A.tilted x hx) (fun z hz => ?_) (fun f => ?_)
  · have he : Continuous P.name := (home n).comp ((P.switch.continuous.comp (cont_Re n)).prodMk
      (P.switch.continuous.comp (cont_sh n)))
    exact (hF.hol n _).continuousOn.comp_continuous (he.comp ((home n).comp (continuous_id.prodMk continuous_const)))
      (fun _ => (hV _).2 (show shade (glow _ z) ∈ V by simpa using hz))
  have ht := Z.sees hF (v ∘ P.s) _ A.permitted.there (modified _) (along P.switch.toContinuousLinearEquiv f)
  have hP : Tendsto P.switch (𝓝[V] dawn y) (𝓝[fields n] P.switch (dawn y)) :=
    P.switch.continuous.continuousWithinAt.tendsto_nhdsWithin fun _ h => h
  exact (ht.comp hP).congr' (Eventually.of_forall (reindex (Z.emit (v ∘ P.s)) P f))

include h p'
theorem casement (hF:Z.FullBody F)(hs:Z.Spun R)(P:NearPair n) : ∃ y:ℕ→Heights n,Tendsto (dawn ∘ y) atTop (𝓝 0) ∧ ∀ (k:ℕ)(v:Fin n→V), ∃ A:PairedPanes P Z v (y k), A.sameGround ∧ A.Forms:=by
 obtain ⟨y,h',m⟩:= Work.C17.answer n P; refine ⟨y,h',fun k v=>?_⟩; obtain ⟨B⟩:= moods R Z hF hs v P (y k) (m k).1 (m k).2; exact ⟨B,tiled_panes p' h hF v (y k) P B,realizes_panes hF v (y k) P B⟩
end Palette
open Palette Boundary.NearPair
namespace WView
def Localizes (W:WView V): Prop := ∀ n (v:Fin n→V)(P:NearPair n), IsVanishingOn (fun f=> (W.W n v - flipW (W.W n (v ∘ P.s)) P) f) P.gap
theorem isLocal {F: InkWaves V}{R:Courts V}{H:Hilbert}{S:OS.Semigroup H timeAxis}{B:Carton S V}(u:InkPort B F W)(h:R.Carriage F): W.Localizes:=by
 let D:= Palette.blanket; let Z:= Palette.ticket D W; let hurs:=u.fades h; let p:= on_shape hurs u.half_price; let hZ:= Z.available p u.region u.gap_cost u.weighted u.looks; intro n v P; obtain ⟨y,he,k⟩:= Palette.casement u.region h hZ (Z.spun_of_selfSpeaks R hurs p) P; exact Palette.observes Z v P (Palette.modified _) (p n) ⟨y,he,fun m=>k m v⟩
end WView
end YM.SatinWFixed
