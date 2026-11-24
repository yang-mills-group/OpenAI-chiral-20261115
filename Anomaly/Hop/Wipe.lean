import Anomaly.Ship.Sleet
/-!
 Normal budget variant. Allocate a reserve palette in each location; this uses fixed Key multiplicities even as multiple steps or gap occurrences will descend there. Recycle designated Key coordinates when shipping new openings through the Ring. `wipe` recycles BEFORE seeding. 
 -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Vow.TreasuryFog
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tenant Tulip
open Pastry Hake Peaks Fock Branch Drapes Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Palot Cadre Rill Stax Rive Ione Larch Roots Push.AbsoluteSums.Trees Sour Py.Rate.BScale Nor Mew PowerSeries
open scoped Mew
variable {n:Side} {I:Type} [LinearOrder I] [Fintype I]
variable {P:BudgetPoint} {q:ℕ} {h:ℝ}
open Neon Bake Rive QuadClock Stilo Roots
open Py Oise Swell Sault Pastry Rue
variable {N B:Side}
local notation "Tc"=> mid N B
local notation "Hp"=> hill I
abbrev wipe (D:Finset I)(x:Mew.Key I):Mew.Key I:= fun j=> if j∈D then 0 else x j
variable (D:Finset I)
local notation "F₀"=>wipe D
lemma wipe_dead {A:Type}(f:Key I→A): Dorm D (f ∘ F₀):= fun z _ w _ h=> congrArg f (funext fun i=>by by_cases p:i∈D <;> simp [wipe,p,h i])
lemma wipe_hill {z:Key I}(p:z∈ Hp): F₀ z∈ Hp:=by
 refine hill_i.mpr (fun i=>?_); unfold wipe; split; · simp
 exact hill_i.mp p i
lemma wipe_morn :wipe D 0=0:=funext fun i=>by simp [wipe]
lemma wipe_up (p:I)(g:p∉D)(x:ℂ)(z:Key I): F₀ (update z p x)=update (F₀ z) p x:=by
 funext i; by_cases h:i=p; · subst i; simp [wipe,g]
 simp [wipe,h, Function.update_of_ne h]
lemma wipe_low (p:I)(g:p∈D)(x:ℂ)(z:Key I):F₀ (update z p x)= F₀ z:=by
 funext i; by_cases h:i=p; · subst i; simp [wipe,g]
 simp [wipe,h,Function.update_of_ne h]
variable {A:Type}[NormedAddCommGroup A][NormedSpace ℂ A]
open Set Topology
lemma wipeSweep (f:Key I→A)(p:River f): River (f ∘ F₀):=by
 have hc:Continuous F₀:=by apply continuous_pi; intro i; unfold wipe; split; exact continuous_const; exact continuous_apply _
 refine ⟨p.shore.comp hc.continuousOn (fun _ g=>wipe_hill D g),?_⟩
 intro i g j z q; unfold Function.comp; by_cases t:j∈D; · simp_rw [wipe_low D j t]; exact differentiableAt_const ..
 simp_rw [wipe_up D j t]; exact p.slope _ (wipe_hill D g) j z q
variable [CompleteSpace A] {f v:Key I→A}
lemma wipe_read (f:Key I→A)(l:List I)(t:∀ i∈l,i∉D)(x:Key I): Mew.lance (f ∘ F₀) l x=Mew.lance f l (F₀ x):=by
 induction l generalizing f x with|nil=>rfl|cons i l ih=>
    have he:cutI (f ∘ F₀) i=cutI f i ∘ F₀:=by funext z; unfold cutI Function.comp; simp_rw [wipe_up D i (t i (by simp))]; -- tune no goals
    simp only [Mew.lance,he,ih (t:=fun i v=>t _ (by simp [v]))] -- `ih` binder proof syntax
lemma wipe_list (f:Key I→A)(l:List I)(t:∀ i∈ l,i∉D):tipI (f ∘ F₀) l=tipI f l:=by unfold tipI; rw [wipe_read D f l t,wipe_morn]
lemma wipe_out (f:Key I→A)(p:River f)(l:List I)(i:I)(w:i∈l)(u:i∈D): tipI (f ∘ F₀) l=0:=by
 let F:= f ∘ F₀; let L:= i :: l.erase i
 have ht: L.Perm l:= (List.perm_cons_erase w).symm
 have he(z) (e:z∈Hp): cutI F i z =0:=by
    have hx:=mitt (wipeSweep D f p) e i; simp_rw [Function.comp_apply,wipe_low D i u] at hx; exact hx.unique (hasDerivAt_const ..)
 unfold tipI; rw [← move_ζ ht (wipeSweep D f p) roots]
 exact ((lace_C _ (g:=fun _=>0) he roots).trans (tip_0 _))
-- useful scalar.readBudget
lemma wipe_α (g:I→ℂ): α_ξ (wipe D g)= (α_ξ g) ∘ F₀:=by
 funext z; unfold α_ξ Function.comp; refine Finset.sum_congr rfl fun i _=>?_ ; by_cases h:i∈D<;>simp [wipe,h]
variable {R:GramM (mid N B)}{Y:Key I→Pax (mid N B)}{V:Key I→Cusp (mid N B)}{E:Key I→RegBudget (mid N B)} {K:Key I→ForceBudget (mid N B)}{e a b:ℝ}{r s:Key I→ℂ}{o:I→ Site (mid N B)}
lemma wipe_I (x:I)(R:Key I→RegBudget n)(p:∀ S W,River (fun z=> R z S W)): νTip (R∘ F₀) x=if x∈D then 0 else νTip R x:=by
 -- n must mQ
 funext S W; by_cases f:x∈ D; rw [if_pos f]; exact wipe_out D _ (p _ _) [x] x (by simp) f
 rw [if_neg f]; exact wipe_list D (fun z:Key I=> R z S W) [x] (by simpa using f)
lemma wipe_K (x:I)(R:Key I→ForceBudget n)(p:∀ S W,River (fun z=> R z S W)): emberTip (R∘ F₀) x=if x∈D then 0 else emberTip R x:=by
 funext S W; by_cases f:x∈ D; rw [if_pos f]; exact wipe_out D _ (p _ _) [x] x (by simp) f
 rw [if_neg f]; exact wipe_list D (fun z:Key I=> R z S W) [x] (by simpa using f)
-- Boiler with old E,K as seen from realized Plan. no need to have actually paid new marks in this use, and accepts when r not zero across placements.
lemma wipeCost (z:Diesel R.p (Cube.node∘o) h e a Y V E s)(Wc:E 0=0)(Vz:K 0=R.K) (V0:BudK K (Cube.node∘o))
    (u:River r)(t:∀ i:Scree.Hub (mid N B), Rive.Hush (Cube.node ∘ o) i.val.2 (fun z=> E z i) ∧∀ x,River (fun z:Key I=> E z i x))
    (pK:∀ z∈hill I,FlagWidth R.p (K z) (cipherK q)∧SanB (K z) (giftK R.p (R.p.supportExponent+1/2)) R.p h (fun _=>b)) (F':Key I→ RegBudget (mid N B))(hF:∀ i∈hill I,ForgeB (F' i) (filmK R.p (R.p.supportExponent+1)) R.p h (fun _=>e))(h0:∀ X V,River (fun z:Key I=> F' z X V))(hf:∀ L: List I,L.Nodup→2 ≤ L.length→∀ X V,tipI (fun z:Key I=>F' z X V) L=tipI (fun z=> E z X V) L) (hp:1≤h):
    Furnace R D q o (E ∘ wipe D) (K ∘ wipe D) (r ∘ wipe D) h e a b ∧ CrestPay R.p (Cube.node∘o) (E ∘ wipe D) (R.p.supportExponent+1) h e:=by
 let F:= F₀; -- universe variable resolution
 have hσ{Z:Type} (T:Key I→Z)(X:Support (More Tc))(u:Rive.Hush (Cube.node ∘ o) X T):Rive.Hush (Cube.node ∘ o) X (T ∘ F):= fun v hv j w k=>u _ (wipe_hill D hv) _ (wipe_hill D w) (fun i g=>by unfold F wipe; split; rfl; exact k _ g)
 have z₀:F₀ 0=0:=wipe_morn D
 let hE:SiltQ (E∘F₀) (Cube.node ∘ o):=⟨fun i=>hσ _ _ (t i).1, fun V x=> wipeSweep D _ ((t V).2 x)⟩
 refine ⟨⟨(show E (F₀ 0)=0 from by rw [z₀,Wc]),?_,hE,⟨fun i=>hσ _ _ (V0.quiet i),fun i V=>wipeSweep D _ (V0.toll i V)⟩,wipeSweep D _ u,wipe_dead D E,wipe_dead D K,wipe_dead D r,fun i v=>(pK _ (wipe_hill D v)).1,fun i v=>(pK _ (wipe_hill D v)).2,?_⟩,?_⟩
 · change K (F₀ 0)=_; rw [z₀,Vz]
 · refine ⟨Y ∘ F,V ∘ F, s ∘ F,?_, wipe_dead D Y,wipe_dead D V⟩; obtain ⟨T,s,t,P,crop,cup,h,w,u,q⟩:=z
   obtain ⟨g,A,C⟩:= w; exact ⟨(congrArg Y z₀).trans T,(congrArg V z₀).trans s,fun i u=>t _ (wipe_hill D u),fun j=>hσ _ _ (P j),fun i v=>wipeSweep D _ (crop i v),fun i X v=>hσ _ _ (cup _ _ v),fun i X v x=>wipeSweep D _ (h i _ v x),⟨_,A,fun i v=> C _ (wipe_hill D v)⟩,fun i v=>u _ (wipe_hill D v),fun i v=> q _ (wipe_hill D v)⟩
 refine growE_t (F' ∘ F) hE (fun i v=>hF _ (wipe_hill D v)) (fun i v=> wipeSweep D _ (h0 i v)) ?_ (zero_lt_one.trans_le hp)
 intro v k; funext X P; let d:=Mew.Cue I v
 let G(z:Key I):=F' z X P; let J(z:Key I):= E z X P
 change tipI (G ∘ F₀) d=tipI (J ∘ F₀) d
 by_cases h:∀ i∈d,i∉D; swap; · push Not at h; obtain ⟨i,v,b⟩:=h; rw [wipe_out _ _ (h0 X P) _ _ v b,wipe_out _ _ ((t X).2 P) _ _ v b]
 have ht:= (mem_filter.mp k).2.1; rw [wipe_list _ _ d h, wipe_list _ _ d h]; exact hf d (Finset.sort_nodup ..) (by rw [show d.length=v.card from Finset.length_sort ..]; omega) ..
end YM.CF.Vow.TreasuryFog
