import YM.CF.BProof.Garden.Button
import YM.CF.BProof.Veil.Class
/-! Busy contribution. separation for local cylinder terms. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.BProof.Veil
open Function Filter NormedSpace Finset MeasureTheory RecN
open Cube Lattice Tenant SU Lat Dial Tulip Fock Skye Spin Branch Hearth Tape Hero Stint Oasis Scree Palot Wick Crystal Garden
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical Hearth Tape Mark
attribute [local instance] opCStarAlgebra
variable {N:Side}{j:ℕ}{a b l r c δ v η o h:ℝ} {P:Spin.Ready j a b l r}{F:Core j a b l r N}{H: Honor P F δ}
local instance busyFC {I:Type}[Fintype I][DecidableEq I]: MeasurableSpace (Op I):=borel _ -- equivalent
local instance busyFop {I:Type}[Fintype I][DecidableEq I]: BorelSpace (Op I):=⟨rfl⟩
variable {y:Pay}(M:Marks H y c v η)(D:GramM N)(q:Cargo D h o) (w:ℂ)
structure Shade (S:Support (More N))(s s':Support N)(x y:Loft F δ c v η)(Z Z':Orbit N)(X X':Plant N)(b b':Fields N):Prop where
 beam:(quiet N).agree S (Z.1,sion x) (Z'.1,sion y)
 law:Set.EqOn Z.2 Z'.2 S
 phase:Set.EqOn b.1 b'.1 S
 sway(i:Site N)(p: node i∈ S): X.leaf i=X'.leaf i ∧ b.2 i=b'.2 i ∧ (i∈s ↔ i∈s')
variable {x x':Loft F δ c v η} {s s':Support N}{S T:Support (More N)} {Z Z':Orbit N}{X X':Plant N}{z z':Fields N}
lemma Shade.mono (t:Shade T s s' x x' Z Z' X X' z z')(p:S⊆T): Shade S s s' x x' Z Z' X X' z z':=⟨(quiet _).onwards t.beam p,t.law.mono (coe_subset.mpr p), t.phase.mono (coe_subset.mpr p), fun i g=> t.sway _ (p g)⟩
include q
lemma tZero(k:OptionR N) (t:(pine N).agree (lot D.p k.1.2) Z.1 Z'.1): FeeR D 1 Z.1 k= FeeR D 1 Z'.1 k:=congrArg (fun A:Cipher N=> (1:ℝ) • Pastry.crumb A.val k.2.val) (q.dataR _ ((pine_eq _).mp t)) -- tune
lemma tStar (i:Options N)(t:Shade (streets D.p i).val s s' x x' Z Z' X X' z z'): angle D w x X s Z z i=angle D w x' X' s' Z' z' i:=by
 rcases i with i|(i|i); · let S:Support (More N):={node i.1}; have he:Shade S ..:=t; obtain ⟨u,e,l⟩:= he.sway i.1 (mem_singleton_self _); have hp: (window N).agree S (sion x) (sion x'):= (paired _|>.mp he.beam).2; have hf: x.val.2.val (node i.1)=x'.val.2.val (node i.1):= (curve_rule _|>.mp (equalize _ _ _|>.mp hp).2.2) _ (mem_singleton_self _); exact flEq w x x' X X' i z.2 z'.2 s s' l u e hf
 · exact tZero D q i (show (pine N).agree _ _ _ from ((paired (streets D.p _).val).mp t.beam).1)
 exact feeRProof D q Z Z' i z.1 z'.1 ((pine_eq _).mp ((paired (streets D.p _).val).mp t.beam).1) t.phase t.law
lemma alive (i:Y (More N)) (t: Shade i.val s s' x x' Z Z' X X' z z'): fBusy x M D X Z z w s i=fBusy x' M D X' Z' z' w s' i:=by
 unfold fBusy; apply congrArg₂ _ _ (minor M q i x x' Z.1 Z'.1 _ t.beam); have he: (window N).agree i.val (sion x) (sion x'):= (paired i.val |>.mp t.beam).2
 refine Civic.gaugeRead (plaza D.p N) (M.eye x) (M.eye x') (angle D w x X s Z z) (angle D w x' X' s' Z' z') i ?_ (fun i h=> tStar D q w _ (t.mono h))
 let V:= (Tape.kiln H.1 c v η).st; have hv:= (stateD H i.val x x' he).2; exact fun j f p u _=>niceEye x M j x' (le_antisymm ((V.includeV f x x').trans_eq hv) (V.pos ..)) p u
variable {A:Type*}[MeasurableSpace A]
omit q in
lemma m_core (K:Key):Measurable (fun x:Loft F δ c v η=>(view x K 1: Op (Single N))):=by
 -- generic evaluation use pair_cont; topology continuous shelf ok
 apply Continuous.measurable; have he:Continuous (fun x:Loft F δ c v η=> x.val.2):=continuous_snd.comp continuous_subtype_val; exact pair_cont.comp ((Tape.Skein.Roam K).comp (he.prodMk (continuous_const (y:=(⟨1,Wick.walk1⟩: Time))))) -- tune
omit q in
lemma tck(i:OptionJ N)(x:A→Loft F δ c v η)(X:A→ Support N)(R:A→ Plant N)(V:A→Fields N)(h:Measurable x)(v:Measurable X)(g:∀ i, Measurable (fun y=> (R y).leaf i))(d:Measurable V) : Measurable (fun p:A=> tokenJ (X p) (V p).2 w (R p) (coreB (x p)) i):=by
 unfold tokenJ; apply Measurable.ite _ _ measurable_const; · apply v (show MeasurableSet {x:Support N| i.1∈x} from (Set.to_countable _).measurableSet) -- syntax
 have ht: Measurable (fun p:A=> coeffJ (chef i.1) (coreB (x p)) i.2.val ((R p).leaf i.1)):= button (chef i.1) i.2.val _ _ (Measurable.comp (g:=coreB) (m_core (false,false)) h) (g i.1); apply Measurable.mul _ ht; apply measurable_const.mul; exact glow.continuous.measurable.comp ((measurable_pi_apply (X:=fun _:Site N=> YPhase) i.1).comp (measurable_snd.comp d)) -- tune
lemma tFlare (i:OptionF N)(x:A→Orbit N)(V:A→Fields N) (e: Measurable x)(h:Measurable V): Measurable (fun p=>RateF D (V p).1 (x p) i):=by unfold RateF; exact ((style_cont ..).measurable.comp (measurable_fst.comp h)).mul ((feeC i.2.val).comp ((q.measF _).comp e))
lemma busyMeas (x:A→Loft F δ c v η)(X:A→ Support N)(U:A→Orbit N)(Z:A→Plant N)(V:A→Fields N)(h:Measurable x)(v:Measurable X)(e:Measurable U)(g:∀ i, Measurable (fun k=> (Z k).leaf i))(d:Measurable V)(i:Y (More N)): Measurable (fun k=> fBusy (x k) M D (Z k) (U k) (V k) w (X k) i):=by
 unfold fBusy gustLog; apply Measurable.sub; apply Civic.measurable; exact fun j t k _=> ((M.expo j t k).connected.measurable).comp h
 · rintro (j|(j|j)); exact tck w j x X Z V h v g d; exact (show Measurable (fun p:Pane N=> FeeR D 1 p j) from offerM q 1 (.inr (.inl j))).comp (measurable_fst.comp e); exact tFlare D q j U V e d -- tune
 apply Civic.measurable; exact fun j t k _=> ((M.expo j t k).connected.measurable).comp h; intro p; exact (offerM q 1 p).comp (measurable_fst.comp e)
end YM.CF.BProof.Veil
