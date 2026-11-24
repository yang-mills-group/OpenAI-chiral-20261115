import YM.SU5.Regis.Screening
import YM.SU5.Regis.Ranging
import YM.SU5.Diva.Tailor
/-! # Carry gauge aperture and take actual histological heights -/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 320000
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Papal
open Function NormedSpace Filter Metric Fock SU Finset Lat Lattice Cube RP Reflect Nacre -- remove unknown
open Wilson Push.SectorMeasure RG Cube Lat Spire Scroll ProbabilityTheory MeasureTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye CF.Pannier.Chancel Brace Velvet Buffered.Lifted Cliplet Reed CF.Lamour.Bridge CF.Lamour.Bridge.Celeste
open Girt
open Afterglow -- tune
open Pannier Regis.Head Preparation Journey
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical ContDiff Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {G:Gauge}{I:Type*}[Fintype I](A: Etch SU.group I){N:Side}
abbrev spanOf:= insert 0 (univ.biUnion (fun i:I=> (A.slot i).stencil))
abbrev panelet (ρ:ℝ) : Weaver:=fun _=> paletteU A ρ 1 0
lemma designed (t:ℝ) : let f:LinksC→ℂ:=(fun u=> A.portrait t u); Buffered.Coeff false (spanOf A) (f ∘ Prod.fst):=by
 intro f; apply Coeff.fromC; · unfold f Etch.portrait; apply Complex.continuous_ofReal.comp; apply A.diff.continuous.comp; apply continuous_pi; intro j; fun_prop
 intro x y p; unfold f Etch.portrait; apply congrArg Complex.ofReal; apply congrArg A.f; funext i; refine congrArg (t • ·) ((A.slot i).covered x y ?_); intro e h v; exact p e (mem_insert_of_mem (mem_biUnion.mpr ⟨i,mem_univ i,h⟩)) (mem_insert_of_mem (mem_biUnion.mpr ⟨i,mem_univ i,v⟩))
lemma paint_val(N:Side)(x:Fields N)(t:ℝ): panelet A t N x= (A.portrait t (onC N x.1):ℂ) • (1:FC (Single N)):=by
 let T:=SU.group; change (A.palette t 1 0 x.1:ℂ) • _= _; rw [Etch.palette,pull_id]; rfl
lemma panel_eq(X:Calibration)(ρ:ℝ) : household X (panelet A ρ)=Buffered.scalar X (fun u=> (A.portrait ρ u.1:ℂ)) := funext fun i=> funext fun u=> paint_val A (X.c i) u ρ -- tune
lemma designed_test (X:Calibration)(ρ:ℝ): InTest X false (spanOf A) false (household X (panelet A ρ)):=by
 rw [show household X (panelet A ρ)=_ from panel_eq A X ρ]; exact InTest.seed (designed A ρ)
lemma owner_hard (N:Side)(ρ:ℝ): AtSupport false (dBook N (spanOf A)) (panelet A ρ N) :=by
 let f : PairsC→ℂ:=fun i=> (A.portrait ρ i.1:ℝ); have q : Coeff false (spanOf A) f:=designed A ρ
 let B(V:Fields N):=(onC N V.1,onC N V.2); rw [funext (fun i:Fields N=>paint_val A N i ρ)]; exact ⟨pole_w (f ∘ B) (fun x:ℂ=> x • (1:FC (Single N))) (continuous_id.smul continuous_const) (Env.along q.env (((on_cont _).measurable.comp measurable_fst).prodMk ((on_cont _).measurable.comp measurable_snd))),fun U V p l=>congrArg (fun x:ℂ=> x • 1) (q.locus (B U) (B V) (on_agree _ p) (on_agree _ l)),fun U=> Fine.one.scale _⟩
lemma painted_gauge (ρ:ℝ) (N:Side): covariant (panelet A ρ N):=by intro g p; unfold simultaneous; let F:=panelet A ρ N; change (A.palette _ _ _ (gauge g p.1):ℂ) • _ = twist (quantU (tradew N g)) ((A.palette _ _ _ p.1:ℂ) • _); rw [A.panel_gauge,twist_scalar,map_one] -- tune
-- ultrareference via hyperfilter both levels
section hyper
abbrev sceneL:Filter ℕ:= Filter.hyperfilter ℕ
private lemma atlas(x:ℕ→ℝ){C:ℝ}(p:∀ i,|x i|≤C): ∃ T:ℝ,|T|≤C∧Tendsto x sceneL (𝓝 T):=by
 let a:= (Filter.hyperfilter ℕ).map x; obtain ⟨z,t,h⟩:= IsCompact.ultrafilter_le_nhds' (s:=Set.Icc (-C) C) isCompact_Icc (f:=a) (show ∀ᶠ i in sceneL,x i∈Set.Icc (-C) C from Eventually.of_forall fun i=> abs_le.mp (p i)) -- map coercions tune
 exact ⟨z,abs_le.mpr t,h⟩
-- Across k chosen by V.
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l)) (K H:ℕ→ℕ)
variable (s:ℕ)
lemma restrict_tape (s i k:ℕ): |hatsMuseo Y A s i k| ≤ A.arc:= A.stable_budget ..
-- order of args tape? section variables A before.
def innerTab (s i:ℕ):ℝ:= (atlas (fun k=> hatsMuseo Y A s i (H k)) (fun k=> restrict_tape A Y ..)).choose
lemma innerTel (i): |innerTab A Y H s i|≤ A.arc∧ Tendsto (fun k=> hatsMuseo Y A s i (H k)) sceneL (𝓝 (innerTab A Y H s i)):= (atlas _ (fun i=>restrict_tape A Y ..)).choose_spec
noncomputable def ornament :ℝ:= (atlas (fun i=> innerTab A Y H s (K i)) (fun i=> (innerTel A Y H s _).1)).choose
lemma terrace_ultra : |ornament A Y K H s| ≤ A.arc ∧ Tendsto (fun i=> innerTab A Y H s (K i)) sceneL (𝓝 (ornament A Y K H s)):= (atlas _ (fun i=> (innerTel A Y H s _).1)).choose_spec
-- preserve estimates if compatible support. Need n→∞ costs
variable {K H} (h:Real.exp 1≤ P.x) (p:Geometry P)(hp:P.Attic) (q:∃ a,CF.Velvet.Procurement P.K.j a P.d)
variable {T:ℕ→ Buffered.Family (tent Y h)→ℕ→ℂ} {E:ℕ →Buffered.Family (tent Y h)→ℂ} (V:Universal Y h K H T E)
open Buffered.Afterglow.Tower
-- one core
include p hp q V
lemma panelThink (ε:ℝ)(pE:0<ε):∀ᶠ s in atTop, let f:=panelet A (museumV (P:=P) s); ‖E s (household (tent Y h) f)-(ornament A Y K H s:ℂ)‖ ≤ε:=by
 let U:= spanOf A; let r:=breadth 0 U; let B:=2*(r+0); filter_upwards [lens_state Y A p hp q h B _ pE] with s p f; let g:=household (tent Y h) f; let X:= V.together s g (Tower.aux_test ((designed_test A (tent Y h) (museumV (P:=P) s)).widen)); let c(y:ℝ):ℂ:=y
 apply le_of_tendsto (Filter.Tendsto.norm ((X.periods.mono_left Nat.hyperfilter_le_atTop).sub (Complex.continuous_ofReal.continuousAt.tendsto.comp (terrace_ultra A Y K H s).2)))
 apply Nat.hyperfilter_le_atTop; -- because we want all late i
 have r0:=(V.pick.grow_i.tendsto_atTop.eventually p).and (((count_la Y s).comp V.pick.grow_i.tendsto_atTop).eventually (breadthMoney 0 U));
 filter_upwards [r0] with i gX; apply le_of_tendsto (Filter.Tendsto.norm (((X.inner (K i)).mono_left Nat.hyperfilter_le_atTop).sub (Complex.continuous_ofReal.continuousAt.tendsto.comp (innerTel A Y H s (K i)).2)))
 let pK:=V.pick.grow_k.tendsto_atTop.eventually (gX.1); refine Nat.hyperfilter_le_atTop (pK.mono fun k h' => ?_)
 let N:= count Y s (K i); have ht: Inhabited (Seat N):= inferInstance; let Z:= dBook N U; let F:=Journey.compass Y (K i) (H k) s (f N); let Y':= hatsMuseo Y A s (K i) (H k)
 have hz : (0:Seat N)∈ Z:= by rw [← map_zero (wrap (More N))]; exact mem_image_of_mem _ (mem_insert_self ..)
 have hu: ‖F-c Y'‖≤ ε:= h' 0 1 hz (fun i=> by
    obtain ⟨t,h⟩:=blocks_rest (wrap (More N) (0:Cover)) (r+0) i; exact ⟨t,fun i v=> h _ (Lamour.Bridge.fit gX.2 v)⟩) (owner_hard A N (museumV (P:=P) s))
 change ‖Journey.compass Y (K i) (H k) s (send Y h (K i) s (g (momentm Y (K i) s))) - c Y'‖≤ ε; rw [show send Y h _ _ (g (momentm Y (K i) s)) = f N from resideA f _ N (terrain Y h (Y.ir (K i)) s)]; exact hu
where resideA(F:Weaver)(A B:Side)(g:A=B): (g ▸ F A)=F B:=by subst B; rfl

omit p hp q V
variable {ι:Type*}[Fintype ι]
lemma panel_spread (x:ι→ Cover) (p:Injective x): ∀ᶠ N:Side in atTop, Injective (fun i=> wrap (More N) (x i)):=by
 have he(i:ι) : ∀ᶠ N:Side in atTop,Lattice.lift (wrap (More N) (x i))=x i:=by
    let k:= univ.sup (fun a=> ((x i) a).natAbs); filter_upwards [eventually_ge_atTop (⟨2*k+1,by omega⟩:Side)] with N ht; change 2*k+1≤N.val at ht; apply lift_eq_iff.mpr; refine ⟨rfl,fun j=>?_⟩; have h:((x i) j).natAbs ≤ k:=le_sup (f:=fun a=> ((x i) a).natAbs) (mem_univ j); rw [show (More N).val=N.val*2 from rfl]; omega
 filter_upwards [Filter.eventually_all.mpr he] with N t; intro i j g; apply p; rw [← t i,←t j]; exact congrArg Lattice.lift g -- g writes function reducible?
open Next.SectorChange
include V
lemma beefing(x y:ι→ Cover)(o z:ι→ Signed)(p:Injective x)(f:Injective y) [Nonempty ι]:∀ᶠ s:ℕ in atTop, let X:= (A.ensemble o x).radial (A.ensemble z y); |ornament X Y K H s- ((Fintype.card ι)* ornament A Y K H s)^2| ≤ Fintype.card ι* A.climax P.K.top.clip:=by
 filter_upwards [(turnover P).eventually_gt_atTop (0:ℝ)] with s hx X;
 apply le_of_tendsto (((terrace_ultra X Y K H s).2.sub (((terrace_ultra A Y K H s).2.const_mul (Fintype.card ι:ℝ)).pow 2)).abs)
 apply Nat.hyperfilter_le_atTop; let E:= (count_la Y s).comp V.pick.grow_i.tendsto_atTop; filter_upwards [E.eventually (panel_spread x p),E.eventually (panel_spread y f)] with i g e;
 apply le_of_tendsto (((innerTel X Y H s (K i)).2.sub (((innerTel A Y H s (K i)).2.const_mul (Fintype.card ι:ℝ)).pow 2)).abs); apply Nat.hyperfilter_le_atTop; filter_upwards [V.pick.grow_k.tendsto_atTop.eventually (ferry_later Y s (K i))] with k t
 let n:= More (count Y s (K i)); let G:=gram Y s (K i) (H k); let d:= Y.uv (H k)-s; obtain ⟨a,b,c,v,l⟩:=prices_plot Y s (K i) (H k) t.enters
 let S:=P.V.L; let B:= S.mood d; have hi:= (Etch.railB (β:=G.beta) v.1 v.2 hx); let M:=S.roof d; exact A.ensemble_double P.K.top.clip x y o z B (S.tied d) (M.2.1 n) (M.2.2 n) (le_trans (by norm_num) hi.1) hi.2 g e
end hyper
end YM.CF.Py.Rate.LocalLimit.Papal
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.panelThink

#print axioms YM.CF.Py.Rate.LocalLimit.Papal.beefing
