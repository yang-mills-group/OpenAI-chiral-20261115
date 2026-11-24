import YM.SU5.One.Coda
import Mathlib.Analysis.Complex.Tietze

/-!
# Actual *continuous*, first-link only regulator readings

Possible even though the original marks depend on both links, can be
merely bounded Borel, and the predictions in the gauge kernel have
fallbacks. Preserve all the gauge invariant data and the fixed physical
support, and certify this is a local-Obs for the stated edge sets/matter
at the UV level (not just some functional with the same integrated value).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 300000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.One
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Branch Tenant
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification Tapestry PhaseChoice Altitude

section specific
open Set Topology CF.Pannier.Chancel Reed
variable {N : Side} (S : Support (More N)) {X Y : Evaluation N}

def diamonds := univ.filter (fun i:Edge (Site (More N))=> i.1 ∈ S ∧ i.1 + step i.2 ∈ S)
def taps (W : Pane N) : ↥(diamonds S)→ SU.E:=fun i=> W i.val
lemma taps_cont : Continuous (taps S):= by apply continuous_pi; intro i; exact continuous_apply i.val
lemma taps_agree {v w : Pane N} : taps S v=taps S w ↔ Lattice.Agrees S v w:= by
  constructor
  · intro h i hi v; exact congrFun h (⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi,v⟩⟩ : ↥(diamonds S))
  intro h; exact funext (fun i=> h i.val (mem_filter.mp i.property).2.1 (mem_filter.mp i.property).2.2)

private def floors (S' : Support (More N)) (v:Bool) : Submodule ℂ (FC (Single N)) where
 carrier:={x | Reed.Fine (Tset N) (modesIn N S') v x}
 zero_mem':= Reed.Fine.empty _
 add_mem':=fun _ _=> Reed.Fine.add ‹_› ‹_›
 smul_mem':=fun c _ h=> Reed.Fine.scale h c

lemma extension {C : Set (Pane N)} {b : Bool}
    (p : IsCompact C) (h : AtSupport b S (toMark X)) (t : ContinuousOn X C) :
    ∃ H : Evaluation N, Continuous H ∧ EqOn H X C ∧ AtSupport b S (toMark H):= by
  let A:= floors S b
  letI : CompactSpace ↥C := isCompact_iff_compactSpace.mp p
  let r (v:C):= taps S v.val
  let f (w: C) : ↥A:=⟨X w.val,h.allV (w.val,w.val)⟩
  have hf : Continuous f:= (continuousOn_iff_continuous_restrict.mp t).subtype_mk _
  have he {u v:C}(x : r u=r v) : f u=f v:=
    Subtype.ext (h.dep (u.val,u.val) (v.val,v.val) ((taps_agree S).1 x) ((taps_agree S).1 x))
  let D:= range r
  let R:= rangeFactorization r
  have hc : Continuous r:= (taps_cont S).comp continuous_subtype_val
  have hp : Surjective R:= Set.rangeFactorization_surjective
  have ht : IsQuotientMap R:= IsQuotientMap.of_surjective_continuous hp hc.rangeFactorization
  choose l hl using hp
  let g (v: D) : ↥A:= f (l v)
  have hT : g ∘ R=f:= funext (fun i=> he (congrArg Subtype.val (hl (R i))))
  have hG: Continuous g:= ht.continuous_iff.mpr (hT.symm ▸ hf)
  letI : TietzeExtension.{0,0} ↥A:= RCLike.instTietzeExtensionTVS (𝕜:=ℂ)
  obtain ⟨G,H⟩:=ContinuousMap.exists_restrict_eq ((isCompact_range hc).isClosed) (⟨g,hG⟩:ContinuousMap (range r) A)
  let T : Evaluation N:= fun i=> (G (taps S i)).val
  have hC:Continuous T:= continuous_subtype_val.comp (G.continuous.comp (taps_cont S))
  refine ⟨T,hC,?_,AtSupport.fromEval _ (Env.compact hC) (fun u v h=> by change (G _).val=(G _).val; rw [(taps_agree S).2 h]) (fun x=>(G (taps S x)).property)⟩
  intro i z
  let u: C:= ⟨i,z⟩
  exact congrArg Subtype.val ((show G ((r u))=g (R u) from congrArg (fun L:ContinuousMap D A=> L (R u)) H).trans (congrFun hT u))

-- Scope charging: stamps explicitly the support EVEN after re-gauging.
lemma refined_regions (g:Zodiac N) {b:Bool}{x:FC (Single N)} (h: Reed.Fine (Tset N) (modesIn N S) b x) :
    Reed.Fine (Tset N) (modesIn N S) b (twist (atelier g) x):=by
  -- adaptation of `tradedFine` for subsets
  have he := Cascade.tick_g (n:=N) g; rw [touchP] at he
  have hN : twist (tradew N g) (cutM (Tset N)ᶜ)= cutM (Tset N)ᶜ:=by rw [dim_cut,map_sub,map_one,he]
  have hp : twist (tradew N g) (cutM (modesIn N S))=cutM (modesIn N S):=by
     apply Mir.twist_comm
     ext ⟨i,j⟩ ⟨k,l⟩
     rw [cutM,Matrix.diagonal_mul,Matrix.mul_diagonal]
     by_cases h:i=k
     · subst k; by_cases hw: node i.1∈ S <;> simp [modes_at,hw]
     simp [tradew,jump_apply,h]
  change Reed.Fine _ _ _ (twist (quantU (tradew N g)) _)
  induction h with
  | empty=> rw [map_zero]; exact .empty _
  | one=> rw [map_one]; exact .one
  | seed i hi=>
     by_cases ht:i∈Tset N
     · rw [show (think _).term i=put i from if_pos ht,←create_put,twist_create]; exact fine_create _ (keepMode g he (within_basis _ _ ht)) (keepMode g hp (within_basis _ _ hi))
     rw [show (think _).term i= -takeF i from if_neg ht,map_neg,← remove_take,twist_remove]
     exact fine_neg (fine_remove _ (keepMode g hN (within_basis _ _ (mem_compl.mpr ht))) (keepMode g hp (within_basis _ _ hi)))
  | add _ _ h k=> rw [map_add]; exact h.add k
  | grow _ _ h k=> rw [map_mul]; exact h.grow k
  | scale _ _ h=> rw [twist_scalar]; exact h.scale _

private lemma refineGaugeAvg (C : Set (Pane N))(p : ∀ g : Zodiac N,MapsTo (Lattice.gauge g) C C)
    {b : Bool} (h : AtSupport b S (toMark Y)) (e : Continuous Y)
    (t : EqOn X Y C)(q:covariant (toMark X)):
    ∃ V : Evaluation N, Continuous V ∧ EqOn V X C ∧ AtSupport b S (toMark V) ∧ covariant (toMark V):=by
  let Z:= toMark Y
  let V := Heat.both (molasses Z)
  have he : Continuous Z := e.comp continuous_fst
  have hx : Continuous V := (sweet he).comp (continuous_id.prodMk continuous_id)
  have ha(g:Zodiac N): star (atelier g)=atelier g⁻¹:=by -- from Chandelier
    unfold atelier; rw [← quantU_star]; let p:=tradew N g; have ht:p*tradew N g⁻¹=1:=by unfold p; rw [Hive.trade_c,mul_inv_cancel,Hive.trade_p]
    exact congrArg quantU (show star p=tradew N g⁻¹ from inv_eq_of_mul_eq_one_right ht)
  refine ⟨V,hx,?_,AtSupport.fromEval V (Env.compact hx) ?_ ?_,fun g x=> ?_⟩
  · intro x x₀
    have hp(g:Zodiac N): getBack Z g (x,x)=X x:=by
       apply (twist (atelier g)).injective
       change twist (quantU (tradew N g)) (getBack Z g (x,x))=twist (quantU (tradew N g)) _
       rw [←trueBack Z g]; change Y (Lattice.gauge g x)=twist (atelier g) (X x)
       rw [←t (p g x₀)]
       exact q g (x,x)
    change (∫ g,getBack Z g (x,x) ∂ domeLaw N)=_
    simp_rw [hp]; simp
  · intro a b' u
    apply integral_congr_ae; apply Eventually.of_forall; intro g
    apply congrArg (twist (star (atelier g)))
    have hx:Agrees S (Lattice.gauge g a) (Lattice.gauge g b'):=by intro i p q; unfold Lattice.gauge; rw [u i p q]
    exact h.dep _ _ hx hx
  · intro i
    apply fine_integral
    apply Eventually.of_forall; intro g
    change Fine _ _ _ (twist (star (atelier g)) _)
    rw [ha]; exact refined_regions S g⁻¹ (h.allV _)
  exact preserves_s he g (x.1,x.1)
-- scope note: odd parity of test X used only as function on its permitted carriers, no Gram assumption.
lemma blueprint {C : Set (Pane N)} (p : IsCompact C) (g : ∀ a:Zodiac N, MapsTo (Lattice.gauge a) C C)
    (h : AtSupport false S (toMark X))(q: ContinuousOn X C) (t:covariant (toMark X)):
    ∃ V : Evaluation N, EqOn V X C ∧ V∈localObs N (diamonds S) (sitesIn N S):=by
  obtain ⟨E,hE,u,v⟩:= extension S p h q
  obtain ⟨F,hF,u,b,w⟩:= refineGaugeAvg S C g v hE u.symm t
  refine ⟨F,u,(Window.mem_localObs _).2 ⟨hF,?_,fun x=> b.allV (x,x),fun g x=>w g (x,x)⟩⟩
  intro x y q
  let he : Agrees (S:Set _) x y:= fun i hi p=> q i ((Finset.mem_filter).mpr ⟨Finset.mem_univ _,hi,p⟩)
  exact b.dep (x,x) (y,y) he he
end specific

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K"=> tent Y H

/-- Height n and region S, in the regulator itself. `Grid` will use it at
*its* cutoff. `Set.EqOn` is for ALL clear configurations, not a limiting
almost-sure condition. -/
def GradeCall (x : Altitude.Cloud (Dome (tent Y H))) (i k : ℕ) (S : Finset Cover) (V : Evaluation (Journey.side Y i (Y.uv k))) : Prop:=
    let N:= Y.uv k; let s:= Journey.side Y i N; let W:= Satin.region S s
    V∈ Window.localObs s (diamonds W) (sitesIn s W) ∧ Set.EqOn V (bareStencil Y H i k x) (clearStage Y N)

theorem charter {s₀ : ℕ}{f : Altitude.Cloud (Dome (tent Y H))} {V : Set RSpace} {w : Bool}
    (p:f∈ observatory Y H w s₀ V): ∃ S:Finset Cover, SupportedPhysically Λ l s₀ S V ∧
       ∀ᶠ (k:ℕ) in atTop, s₀ < Y.uv k ∧ ∀ i:ℕ,(Y.voyage i).kick ≤ k →
          ∃ Q : Evaluation (Journey.side Y i (Y.uv k)), GradeCall Y H f i k (volumeAround Λ l (Y.uv k-s₀) S) Q:= by
  let w':=astro_loose Y H w s₀ V p
  obtain ⟨S,h,v⟩:= stencil_stays Y H w'
  refine ⟨S,h,?_⟩
  filter_upwards [each_imprint Y H,Y.uv_grows.tendsto_atTop.eventually (eventually_gt_atTop s₀)] with k g a
  refine ⟨a,fun i t=> ?_⟩
  have ha: Pay Y s₀ i k:=⟨t,a.le⟩
  have Ht := truly_neutral Y H i k f ha p
  obtain ⟨Q,p,q⟩:= blueprint _ (clear_stage_compact Y _)
      (fun c _ h=> clear_carries Y c h) (v i k ha).1 (g _ a i _ (optic_short Y H w s₀ V w')) Ht
  exact ⟨Q,q,p⟩

lemma hallmark {s : ℕ}{S : Finset Cover}{f : Altitude.Cloud (Dome (tent Y H))}(p:f∈ boardedDB (tent Y H) s) {i k : ℕ}
    (e:Pay Y s i k){x : Evaluation (Journey.side Y i (Y.uv k))}(q:GradeCall Y H f i k S x): Y.texture i k (Y.uv k) x=taking Y H i k f:=by
  let n:=Y.uv k; let z:=Journey.side Y i n; let Z:allObs z:=⟨x,Window.fits_all q.1⟩
  obtain ⟨A,h,Q⟩:= Y.true_read i k n Z e.1 le_rfl
  refine Q.trans ?_
  rw [show partitionZ _ _ _= _ from (bare_vacuum Y i k e.1).2.1, (pay_bare Y H i k f p e).2.2]; apply congrArg (· / _)
  have ht: (∫ w: Skye.Orbit z,inspectedBare Y H i k f w.1∂city z)=(∫ w: Pane z,inspectedBare Y H i k f w ∂prior SU.group (More z)):=by
    change (∫ v : Pane z×_, _ ∂ (prior SU.group (More z)).prod (depot z))=_
    rw [MeasureTheory.integral_fun_fst]; simp
  refine Eq.trans ?_ ht; apply integral_congr_ae; apply Filter.Eventually.of_forall; intro w
  change inner ℂ _ (acts _ (denZ (((Y.voyage i).X (Y.uv k)).gram (Y.uv k)) Λ.U ((Y.voyage i).CapeT (Y.uv k)) w))=_
  rw [Y.whole]; by_cases h:w.1∈clearStage Y (Y.uv k)
  · unfold inspectedBare bareField; exact congrArg (fun o : FC (Single z)=> inner ℂ (Dial.mateK z) (acts o (bareCore Y i k w.1))) (q.2 h)
  change inner ℂ _ (acts _ (bareCore Y i k w.1))=inner ℂ _ (acts _ (bareCore Y i k w.1)); rw [obstruction Y i k h,map_zero,map_zero]
end YM.CF.Buffered.Afterglow.Tower.One
