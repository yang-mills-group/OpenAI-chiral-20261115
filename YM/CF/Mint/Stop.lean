import YM.CF.Mint.Dace
import YM.CF.Vale.Trilogy
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mint.Stop
open Function NormedSpace Filter Finset Graph Lattice Laurent Wilson Analysis Pressure Tulip Lat Cube SU Emu Rush Scree Graph RG Scroll Peaks Drapes Cascade Vault Sods Spire Paige Nova Girt Skye Kea Ember MeasureTheory Vale Hom Grace Push.SectorMeasure Next.SectorChange Precision
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n M B:Side}{b C e s h:ℝ}{α:Type*}
lemma stamp (P:Credit){V:Interest n}(t:InterestX P _ V): V.under (min (min P.f P.u) P.b) (max (max P.F P.U) P.B) (min (min P.f P.u) P.b) (max (max P.F P.U) P.B) (min (min P.f P.u) P.b) (max (max P.F P.U) P.B):=by
 obtain ⟨⟨x,y⟩,q⟩:=t.leanJ
 exact ⟨⟨Laic.qmon x ((le_max_left ..).trans (le_max_left ..)) ((min_le_left ..).trans (min_le_left ..)),Laic.qmon y ((le_max_right ..).trans (le_max_left ..)) ((min_le_left ..).trans (min_le_right ..))⟩, {q with pay:=fun i=> (Pec.monk _ _ (min_le_right ..)).trans ((q.pay i).trans (le_max_right ..))}⟩
lemma sage(L: Loom n)(P:GramM n)(q:ℕ)(p:Roof n s e q L)(g:P.p.threshold ≤ s): SkinT P L e:=by
 refine ⟨⟨s,q,p⟩,fun i h=>?_⟩; apply funext; intro t; apply p.lamp; suffices hs:flags s i.1=∅ by simp [hs]; -- tune
 apply Finset.eq_empty_iff_forall_notMem.mpr; intro j z; obtain ⟨p',v,k⟩:= (flags_spec ..).mp z; change flags _ _=∅ at h; exact notMem_empty _ (h ▸ (flags_spec ..).mpr ⟨p',v,g.trans_lt k⟩)
variable {K:Teller group}{P:RG.Patch}{R:ChartRatio group} {W:Grace K P R}{X:Grasp W.U B e}{G:GivenX W X} (L:Robes M W G)
open Roe
-- specialization to bare. arbitrary footprint-period.Same Gram
variable {N:ℕ→Side}{v w a r x:ℝ}{k:ℕ}
variable (q:ℕ→BudgetPoint) (Y Z:ℕ→ℝ) -- no use X constants
lemma seedB (D:Pic.Span G.pearl b v w a r x k)(j:1≤h)(f:Tendsto (eur N) atTop atTop) (g:Gray (lum Y) (eur N))(H:RangeH Y Z s C)(t:∀ᶠ i in atTop,(q i).threshold=tame Y i): WindS B (fun i=>N i*M) Y h 0 1 K.top.width K.top.paths K.top.clip.linear K.top.clip.direct s C 0 0 (fun _=>W.W.bar) (fun i=>launch W.L (Z i) (q i) (mid (N i*M) B)):=by
 let T (i):= mid (N i*M) B; have ht:∀ i,eur T i= eur N i *((M.val:ℝ)*2 * B.val):=by intro i; unfold eur; change (↑(((N i).val*M.val)*2*B.val):ℝ)=_; push_cast; ring
 have hk:Tendsto (eur T) atTop atTop:= by rw [funext ht]; exact f.atTop_mul_const (by have :=nPos M; have :=nPos B; positivity)
 have he:=tc H.rank
 refine ⟨H,by change Gray _ (eur T); rw [funext ht]; exact g.mul (Gray.coef he _),hk,fun i=>by simp,Gray.coef he 0, Gray.coef he _,j,one_pos,le_rfl,K.top.clip.tail_pos,?_,t.mono fun i p=>?_⟩
 · have h:Nonempty PlaqAxes:=⟨⟨(0,1),by decide⟩⟩; obtain ⟨b,h,v⟩:=(W.L.mood 0).rows h.some; exact le_trans (tsum_nonneg b) v
 have hp:Interest.under (vanilla (T i)) 1 0 1 0 1 0:= ⟨⟨empty_pay le_rfl,empty_pay le_rfl⟩,(white_cost le_rfl).1⟩
 exact ⟨p,⟨(lye ..).1,(lye ..).1,(lye ..).2, hp⟩,W.L.mood 0,le_rfl,le_rfl,le_rfl⟩
lemma loom_p (p:∀ i,L.h ≤(N i).val)(f:Tendsto Y atTop atTop)(E:∀ᶠ i in atTop,(q i).threshold=tame Y i): ∀ᶠ i in atTop,SkinT (launch W.L (Z i) (q i) (mid (N i*M) B)) (L.rack (N i) (p i)) e:=by -- edit
 filter_upwards [E, (damp f).shrinks.eventually (ge_mem_nhds L.ht)] with i hi p'; exact sage _ _ _ (L.berth _ _) (hi.trans_le p')
end YM.CF.Mint.Stop
