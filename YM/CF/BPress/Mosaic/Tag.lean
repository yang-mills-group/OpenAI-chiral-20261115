import YM.CF.BPress.Peel.Short
import YM.CF.BPress.Peel.Mango
/- $small exponent arrays$ one evaluator per Seal. Padded support at zero weight. Tag counts.Bias.L. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Mosaic
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch LocalH Cube Lat SU Skye Port Locale Sugar Wealth Weave House Scree Precision Pressure Next.SectorChange RG Push.SectorMeasure Crew RG.PathData Grid Honey Recipe Peel
open scoped Topology BigOperators Classical YM.CF.BPress.Vesper Matrix Matrix.Norms.Frobenius InnerProductSpace
attribute [local instance] Gauge.frobInner
variable {N: Side}{B:BandWidth}{A: Bands (More N) B}
open Peel.Spine Ledger Push.AbsoluteSums
variable {R:Hangar (More N)} {H:Crew A}
abbrev SlotT (A:Bands (More N) B)(R:Hangar (More N)):=Seal (BlockY A R)
structure Act0 {I:Type} (S:I→SlotT A R)(w:I→ℝ)(b:ℝ) (F:I→ Visit A R H→ℂ):Prop where
 reads(i):∀ x y, Peek H (S i) x.val y.val→ F i x=F i y
 worth :Cash S w 4 b
 shore :∀ i x, ‖F i x‖≤ w i
 glow :∀ i,w i≠0 →Grove (shape A R) (S i)
 meas :∀ i,Measurable (F i)
-- use typed assembler $ℛ$.
structure Lift (b:ℝ)(f:Visit A R H→ℂ):Prop where
 wraps : ∃ (w:SlotT A R→ ℝ)(F:SlotT A R→ Visit A R H→ℂ), Act0 id w b F ∧ ∀ x,f x=∑ i,F i x
variable {I:Type}[Fintype I] {S:I→SlotT A R}{v w: SlotT A R→ℝ} {b c:ℝ}{u:I→ℝ}
namespace Act0
variable {F G:SlotT A R→ Visit A R H →ℂ}
lemma plus (p:Act0 id v b F)(q:Act0 id w c G): Act0 id (v+w) (b+c) (F+G):=by
 refine ⟨fun i x y h=>?_,p.worth.plus q.worth,fun i x=>(norm_add_le ..).trans (add_le_add (p.shore i x) (q.shore i x)),fun i h=>?_,fun i=> (p.meas i).add (q.meas i)⟩; · exact congrArg₂ (·+·) (p.reads i x y h) (q.reads i x y h)
 by_cases r:v i=0; exact q.glow i (fun v=>h (by simp [*, Pi.add_apply])); exact p.glow i r
lemma more (p:Act0 id v b F)(q:b ≤ c): Act0 id v c F:= {p with worth:=p.worth.weaken q}
variable {f:I→ Visit A R H→ℂ}
lemma wallet (p:Act0 S u b f) : Lift b (fun x=> ∑ i,f i x):=by
 let G(t:SlotT A R)(x:Visit A R H):= Ledger.lump S (fun i=>f i x) t; let w:=Ledger.lump S u; have he:=p.worth.lump S u (hasSum_fintype _).summable; refine ⟨w,G,⟨?_,he,fun i x=> lump_bound _ _ _ (hasSum_fintype _).summable (fun i=>p.shore i x) _,?_ , ?_ ⟩,fun x=> ?_⟩
 · intro i u v H; refine tsum_congr fun j=>?_ ; split; next h=> exact p.reads j u v (h ▸ H)
   · exact rfl
 · intro i h; obtain ⟨j,g,v⟩:=exists_ne_zero_of_sum_ne_zero (show ∑ j:I,(if i=S j then u j else 0)≠0 from by simpa only [tsum_fintype,w, Ledger.lump] using h)
   split at v; next h=> rw [h]; exact p.glow j v -- need v first binder mem univ from `exists_ne...`
   · contradiction
 · intro i; unfold G Ledger.lump; simp_rw [tsum_fintype]; apply Finset.measurable_fun_sum; intro j l; split; exact p.meas j; exact measurable_const
 unfold G; rw [lump_sum S _ (hasSum_fintype _).summable,tsum_fintype]
end Act0
namespace Lift
variable {f g: Visit A R H →ℂ}
lemma plus (p:Lift b f)(q:Lift c g):Lift (b+c) (fun x=>f x+g x):=by
 obtain ⟨w,F,h,r⟩:=p.wraps; obtain ⟨W,G,p,H⟩:=q.wraps; refine ⟨_,F+G,h.plus p,fun i=>?_⟩; simp only [Pi.add_apply,r i,H i,sum_add_distrib]
lemma more(p:Lift b f)(h:b ≤ c): Lift c f:=by obtain ⟨w,F,t,h'⟩:=p.wraps; exact ⟨w,F,t.more h,h'⟩
lemma sw(p:Lift b f)(h:∀ x,f x=g x):Lift b g:= funext h ▸ p
end Lift
end YM.CF.BPress.Mosaic
