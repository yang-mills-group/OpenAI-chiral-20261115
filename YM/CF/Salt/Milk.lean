import YM.CF.Salt.Desk
import YM.CF.Plume.Wager
import YM.CF.Haro.Silk
import YM.CF.Salt.Felt
import YM.CF.Tye.Wheel
import YM.CF.Salt.Dial
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 21000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Salt
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo Urn Palot Hake Scion Levier Hive Nacre Tye Skye RG Pressure Next.SectorChange Planned.AtomRegular Girt Spire
open Eire Skye Levier Scion Urn Pastry Rill Kennel Pec
open Eire Girt Tulip Spire Proa RG Pressure Stilo Scree Palot Tye Cour Broc Hive Hake
open Esti Forge AnalyticBridge.Annulus1AD Ac AnalyticBridge.GaussianFieldAlignment Tensor Locations Push.SectorMeasure.Oriented
variable {P N B: Side}(G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(p:S.ratio=ratio G)(f:Sweep (mid N B))(X:Stores S)(r k:ℕ)
open Plume Atala Eire
local notation "H"=> Hos S r
local notation "Ζ"=> laden S f r
local notation "Θ"=> reSweep G f
abbrev shelf {v:Side}(s:Sweep v):Equiv.Perm (Support (More v)):=⟨actS s, actS s⁻¹,Hive.actG_l s,fun x=>by simpa only [inv_inv] using Hive.actG_l s⁻¹ x⟩
abbrev luckP : Equiv.Perm (Kite S r):= Equiv.prodCongr (laden S f r) (Equiv.prodCongr (shelf (reSweep G f)) (shelf (reSweep G f)))
local notation "Λ"=> luckP G S f r
local notation "L"=> liftK S
variable (Y:Finset (Kite S r))
lemma duck_b(K:Hos S r) : laden S f r K ∈ liftK S (Y.image Λ)↔ K∈L Y:=by unfold liftK; rw [image_image]; simp only [mem_image]; apply exists_congr; intro i; refine and_congr_right fun _=> (laden S f r).injective.eq_iff
lemma rushB : L (Y.image Λ)=(L Y).image Ζ:=by ext i; obtain ⟨j,rfl⟩:=(laden S f r).surjective i; rw [duck_b]; simp only [mem_image,(laden S f r).injective.eq_iff,exists_eq_right]
lemma pure_a : pureK S (Y.image Λ)↔ pureK S Y:=by
 constructor; · intro h i v j w l; apply (lay_o f _ _).mp; change Disjoint (actY f (Esti.stem S i.1)) (actY f (Esti.stem S j.1)); have hp := (@h (Λ i) (show Λ i∈ (↑(Y.image Λ):Set (Kite S r)) from mem_image_of_mem _ (show i∈Y from v)) (Λ j) (show Λ j∈ (↑(Y.image Λ):Set (Kite S r)) from mem_image_of_mem Λ (show j∈Y from w)) ((luckP G S f r).injective.ne l)); change Disjoint (Esti.stem S (Ζ i.1)) (Esti.stem S (Ζ j.1)) at hp; rwa [stack_r,stack_r] at hp
 rintro h x v y w p; obtain ⟨i,v_,rfl⟩:=mem_image.mp (show x∈Y.image Λ from v); obtain ⟨j,w_,rfl⟩:=mem_image.mp (show y∈Y.image Λ from w); change Disjoint (Esti.stem S (Ζ i.1)) (Esti.stem S (Ζ j.1)); rw [stack_r,stack_r,lay_o]; exact h v_ w_ (fun e=>p (congrArg Λ e))
lemma bone_t: cook S (Y.image Λ)=airport f (cook S Y):=by
 apply vase_j S; rw [wears,church,wears]; ext i; obtain ⟨i,rfl⟩:=(loftX S f).surjective i; simp only [mem_image,(loftX S f).injective.eq_iff,exists_eq_right]; simp only [mem_biUnion, exists_mem_image]; apply exists_congr; intro u; refine and_congr_right fun v=> story S f u.1.val i
include p
lemma lamp_k(i: Kite S r): Eire.frameP S (luckP G S f r i)=actY f (Eire.frameP S i):=by
 unfold Eire.frameP; change Esti.stem S (laden S f r i.1) ∪ hatY S (danceL S (laden S f r i.1).val r∪actY Θ i.2.1∪actY Θ i.2.2)= _; have he(X Z:Support (Domain N B)):actY f (X∪Z)=actY f X∪actY f Z:= map_union ..; have h(X Z:Support (Domain P B)):actY Θ (X∪Z)=actY Θ X∪actY Θ Z:=map_union ..; rw [stack_r,he, twirl G S p,←h,←h,peg_k _ _ p] -- ambiguity
lemma way (i: Support (Domain N B)): Passage S (actY f i) = actY Θ (Passage S i):=by
 ext x; simp only [actY,mem_map_equiv,Equiv.symm_symm]; simp only [Passage,mem_filter,mem_univ,true_and]; simp only [mem_map_equiv,Equiv.symm_symm]; rw [← show S.ratio.parent (boxA Θ x)= boxA f (S.ratio.parent x) from congrFun (pace_k G S p f) x]
variable (V:Ids (mid P B))(W:Finset (Hos S r))
omit p
lemma halo_o(i:Hos S r): (Passage S (Esti.stem S i)).Nonempty:=by obtain ⟨i,p⟩:=stem_p S i; exact ⟨S.ratio.embed i, mem_filter.mpr ⟨mem_univ _,by rw [Ratio.embed_parent]; exact p⟩⟩
lemma honorB (h:Set.PairwiseDisjoint (W:Set (Hos S r)) (Esti.stem S))(v:Injective (priorP V)): Set.InjOn (Plume.deed V) (W:Set (Hos S r)):=by
 let Hx(x:Hos S r):= Passage S (Esti.stem S x); let f(x):=greet (Hx x) (priorP V); have ht(x:Hos S r): f x∈Hx x:= (mastP _ (halo_o S r x) _).1
 intro x hx y hy g; have hh:f x=f y:=v g; by_contra p; exact Finset.disjoint_left.mp (h hx hy p) (mem_filter.mp (ht x)).2 (mem_filter.mp (show f x∈Hx y from hh.symm ▸ht y)).2
include p
lemma mornK(i:Hos S r): deed (bun (reSweep G f) V) (Ζ i)=deed V i:=by
 unfold Plume.deed; rw [stack_r, way G S p]; dsimp only; let X:=Passage S (Esti.stem S i); let X':= actY Θ X
 obtain ⟨v,w⟩:= mastP X (halo_o ..) (priorP V); obtain ⟨b,a⟩:= mastP X' (map_nonempty.mpr (halo_o S r i)) (priorP (bun Θ V)); apply le_antisymm; let q:=boxA Θ; let k':=greet X (priorP V); let g:=a (q.symm k') (mem_map_of_mem _ v); change _≤ priorP V (q (q.symm k')) at g; rwa [Equiv.apply_symm_apply] at g
 apply w; exact Finset.mem_map_equiv.mp b
open scoped Classical
open Push.SectorMeasure
lemma gone (A:Type*)[Fintype A][DecidableEq A](F:A→ℝ)(C:Finset A)(u:A≃A)(V:A→ℝ)(i:F=V ∘ u) (p:Set.InjOn F (C:Set A)) : (C.image u).sort (Plume.suitsG V) = (C.sort (Plume.suitsG F)).map u:=by -- omit p
 let LP:=C.sort (Plume.suitsG F)
 have hl:LP.Pairwise (fun x y=> Plume.suitsG V (u x) (u y)):= (pairwise_sort ..).imp_of_mem fun {x y} hx hy h=>by
    by_cases p':x=y; · exact p' ▸ (le_refl _)
    have ht:F x≠ F y:= fun g=> p' (p ((mem_sort ..).mp hx) ((mem_sort ..).mp hy) g)
    unfold Plume.suitsG Plume.sue at h ⊢; rw [Prod.Lex.toLex_le_toLex] at h ⊢
    left; rw [show V (u x)=F x from (congrFun i _).symm,show V (u y)=F y from (congrFun i _).symm]; exact h.resolve_right fun p=>ht p.1 -- tune
 refine Eq.symm (List.Perm.eq_of_pairwise' (List.pairwise_map.mpr hl) (pairwise_sort ..) (List.perm_of_nodup_nodup_toFinset_eq ((sort_nodup ..).map u.injective) (sort_nodup ..) ?_)); ext x; simp
lemma work_t(v:pureK S Y)(t:Injective (priorP V)): (walksK (bun (reSweep G f) V)).filter (fun i=> i∈L (Y.image Λ))=((walksK V).filter (fun i=>i∈L Y)).map (Ζ):=by
 rw [walksK, Plume.rail_p _ _ _ (fun _ _=>rfl), walksK, Plume.rail_p _ _ _ (fun _ _=>rfl), rushB]; exact gone G S p _ _ _ _ _ (funext fun i=>(mornK _ _ p _ r V i).symm) (honorB S r V _ (proud S Y v) t) -- tune
end YM.CF.Salt
