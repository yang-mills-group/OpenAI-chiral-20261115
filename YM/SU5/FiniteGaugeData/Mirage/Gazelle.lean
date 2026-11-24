import YM.SU5.FiniteGaugeData.Brique.Pike
import YM.SU5.FiniteGaugeData.Mirage.Pledge
import YM.CF.Cubes.Transport
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 380000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Quest
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Heat Brique Window.Brique Journey Py Py.Rate LocalLimit Preparation FullBill Steam Vale
namespace Chaperone
open Dial -- collisions
variable {N:Side}{i j l n:ℕ}{x y u v o:Cover}{p A B U V S:Finset Cover}
structure Chart (o:Cover) where
 τ : Cover→ Walk
 endsT (x:Cover) : stop o (τ x)=x
namespace Chart
variable (T:Chart o)
abbrev Hires(S U:Finset Cover)(o:Cover)(T:Chart o) := ∀ i∈S, (visits o (T.τ i)).toFinset ⊆U
/-- use SAME fit-room for all THREE frame sets so can share, though buying different Corset. -/
def legH (N:Side)(U:Finset Cover)(i: Site (More N)):= if p:i∈region U N then (mem_image.mp p).choose else Rush.natural i
lemma legR {v:Site (More N)} : wrap (More N) (legH N U v)=v:=by
 unfold legH; split; next p=> exact (mem_image.mp p).choose_spec.2
 exact nat_true _
lemma leg_spec {v:Site (More N)}(p:v∈region U N): legH N U v∈ U:=by unfold legH; rw [dif_pos p]; exact (mem_image.mp p).choose_spec.1
lemma leg_on (p:Hosp U N)(v:Cover)(x:v∈ U) : legH N U (wrap (More N) v)=v:=p.seat_ (leg_spec (mem_image_of_mem (wrap _) x)) x legR
lemma gauge_here (x:Seat N→SU.E)(V:Pane N): onC N (Lattice.gauge x V)=Lattice.gauge (x ∘ wrap (More N)) (onC N V):=by funext i; unfold onC; rw [expandAt_gauge]; simp only [add_zero]; rfl -- tune
abbrev rootF (x:LinksC)(u:Cover): SU.E:= travel x o (T.τ u)
def tenor (N:Side)(S:Finset Cover)(x:Pane N)(i:Seat N): SU.E:=rootF T (onC N x) (legH N S i)
lemma trunk_w (S:Finset Cover)(x:Seat N→SU.E)(V:Pane N): tenor T N S (gauge x V)=globalH N (x (wrap (More N) o)) * tenor T N S V * x⁻¹:=by
 funext i; unfold tenor rootF; rw [gauge_here, travel_gauge,T.endsT]; dsimp only [comp_apply]; rw [legR]; rfl
lemma rent (p:Hires S U o T)(x:Cover)(g:x∈S): Lattice.LocalOn U (fun z=>rootF T z x):= fun a b v=>travel_local o (T.τ x) a b fun i t y=> v i (p x g (List.mem_toFinset.mpr t)) (p x g (List.mem_toFinset.mpr y))
attribute [local fun_prop] on_cont
lemma tenor_from(W:Finset Cover): Continuous (tenor T N W):= continuous_pi fun i=> by unfold tenor rootF; fun_prop (disch:=exact on_cont N)
lemma tenor_site (x:Cover)(q:x∈ V)(p:Hosp V N)(W:Pane N): tenor T N V W (wrap (More N) x)=rootF T (onC N W) x:=by unfold tenor; rw [leg_on p x q]
def passH (p:Hosp V N)(h:S⊆ V)(g:Hires S U o T): Corset (region S N) (region U N) (wrap (More N) o) where
 g:=tenor T N V
 up_cont:=tenor_from ..
 locale i k := by intro x y v; obtain ⟨z,e,rfl⟩:=mem_image.mp k; dsimp only; rw [tenor_site T z (h e) p,tenor_site T z (h e) p]; exact rent T g z e _ _ (on_agree N v)
 law x h:=trunk_w ..
end Chart
-- mask study.
variable {X: ℝ}{n:Side}
open scoped Matrix.Norms.Frobenius in
private lemma chord_unit (v:SU.E)(p:SU.group.chord v=0) : v=1:=by apply SU.group.mat_injective; rw [Gauge.mat_one]; rw [Gauge.chord,div_eq_zero_iff] at p; exact sub_eq_zero.mp (norm_eq_zero.mp (p.resolve_right (Real.sqrt_pos.mpr (by exact_mod_cast SU.group.dimPos)).ne')) -- `h:G` remove, possible norm instance conflict.
abbrev PureZ (x:LinksC):=∀ i:Face ℤ, SU.group.chord (faceValue x i)=0
lemma PureZ.owns {V:LinksC}(T:Chart o) (p:PureZ V): gauge (T.rootF V) V=1:=by
 have ht: Covered firstF V 0:=by
    intro x i j t; rcases lt_or_gt_of_ne t with h|h; · rw [show travel V x (square i j)=1 from chord_unit _ (p (x,⟨(i,j),h⟩)),cmp_id]
    rw [show travel V x (square i j)=(travel V x (square j i))⁻¹ from ?_, show travel V x (square j i)=1 from chord_unit _ (p (x,⟨(j,i),h⟩)),inv_one,cmp_id]; rw [show square i j=Lattice.reverse (square j i) from rfl]; nth_rw 1 [←square_stop x j i]; rw [travel_reverse]
 funext ⟨x,i⟩; let a:= T.τ x; let b:=T.τ (x+step i); let l:=a++[posDir i]; let z:=Cube.near_walk le_rfl ht o l b (by unfold l; rw [stop_append,T.endsT,stop,stop,Step.vec_pos,T.endsT]);
 have hv: travel V o l=travel V o b:=by apply SU.group.mat_injective; exact sub_eq_zero.mp (norm_le_zero_iff.mp (show ‖(firstF (travel V o l)).val-(firstF (travel V o b)).val‖≤0 from (by unfold compareW Cube.cmp at z; simpa using z))); -- tune simp rw
 unfold l at hv; rw [travel_append,T.endsT] at hv; unfold Lattice.gauge; change (travel V o a)*V (x,i)*(travel V o b)⁻¹=1; rw [show travel V o a * V (x,i)=  travel V o b from (by simp [travel,Step.pos_read] at hv; exact hv),mul_inv_cancel] -- inferred _ maybe outer
-- Compact coverage test: allowed even HUGE supra-mask A for `Subsidy`: only need paid by s-as-large-as-necessary AFTER proving E estimate for fixed rectangle at cost/h paying masked test. (using Thermo supports can indeed absorb that). 
lemma pension {f:LinksC→ℝ}(p:Continuous f)(h:∀ x:LinksC,PureZ x→ f x=0)(a:ℝ)(t:0<a):∃ A:Finset (Face ℤ),∃ b:ℝ, 0<b ∧∀ c:ℝ,c ≤ b→∀ x:LinksC, ¬ alarm A c (x,x) → f x≤a:=by
 classical
 let V:= {x: LinksC| a ≤ f x}; have he:IsCompact V:= (isClosed_le continuous_const p).isCompact; let I:= Face ℤ × ℕ
 let A(u:I):Set LinksC:= {x:LinksC | Real.exp (-(u.2:ℝ)) < SU.group.chord (faceValue x u.1)}; have hv: Tendsto (fun i:ℕ=> Real.exp (-(i:ℝ))) atTop (𝓝 0):= Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
 obtain ⟨S,g⟩:= he.elim_finite_subcover A (fun i=> isOpen_lt continuous_const (by unfold faceValue; fun_prop)) (by
    intro v z; refine Set.mem_iUnion.mpr ?_; have hz:¬PureZ v:=fun g=>t.not_ge ((h v g) ▸ (show a≤ f v from z)); obtain ⟨i,t⟩:= not_forall.mp hz
    obtain ⟨j,f⟩:= (hv.eventually (gt_mem_nhds (lt_of_le_of_ne (SU.group.chord_nonneg _) (Ne.symm t)))).exists; exact ⟨(i,j),f⟩)
 let w:= S.sup (fun x:I=> x.2); refine ⟨S.image (fun i=>i.1),_,Real.exp_pos (-(w:ℝ)),fun c e z zz=>?_⟩; by_contra! q; have ht : z∈⋃ i∈S,A i:= g q.le; obtain ⟨i,hk⟩:= Set.mem_iUnion.mp ht; obtain ⟨y,t'⟩:= Set.mem_iUnion.mp hk; exact zz ⟨i.1,mem_image_of_mem _ y,lt_of_le_of_lt (e.trans (Real.exp_monotone (neg_le_neg (Nat.cast_le.mpr (le_sup (f:=Prod.snd) y))))) t'⟩
end Chaperone
end YM.CF.Buffered.Afterglow.Hierarchy.Quest
