import YM.CF.BPress.Engine.Rink
/-! support equality for occupancy log, and reduction to regular only when outside. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Engine
open Function Filter NormedSpace MeasureTheory Finset Lattice Branch Ledger Push.AbsoluteSums Palmer Fock Pastry Pine Pine.EdgeD Pf Vesper Spin Spin.Pledge Spin.Stride Currency Spin.Cellar Spin.Cellar.Pass Spin.Basement Pine.Story
open Spark Cube Lat SU Spin.Paint Skye Girt Scree Tulip Tenant Pf.RealBook RG Chalk Lily DoughBag
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical YM.CF.BPress.Vesper
attribute [local instance] opCStarAlgebra
variable {N:Side}{D:Type}{P:Form N D} [TopologicalSpace D]
namespace Shot
def clearF (u:Pane N) : Shot N := ⟨(u,fun _=>(0,1,1)),fun _=>0,fun _=>0,∅,fun _=> 1⟩
lemma readyF(u:Pane N)(x:ℝ)(p:0≤x): (clearF u).inBudget x:=by
 refine ⟨fun i=>?_,fun i=>?_,fun t=>⟨Matrix.transpose_one,(unitary _).one_mem,Matrix.det_one⟩⟩; · simp [clearF];
 simp [clearF,p]
variable (Q: Shot N)(T:Actor N D)
structure Camera (x y:D)(R:Support (More N))(Q':Shot N)(B:ℕ):Prop where
 here: P.eval R x y=0
 view: Agrees R Q.field.1 Q'.field.1
 frames: Set.EqOn Q.field.2 Q'.field.2 (R:Set (Site (More N)))
 picks: ∀ i:Site N,node i∈R→T.KG x (node i)= T.KG y (node i) ∧ Q.j i= Q'.j i∧ Q.stampX (node i)= Q'.stampX (node i)∧(i∈ Q.inserts↔ i∈Q'.inserts)
 feet:∀ i:Force N,storyP B i⊆R→Q.f i=Q'.f i
end Shot
open Shot Till Store
variable {A:Actor N D}{W:Pledge}{F:GramM N}{μ h ε r g q:ℝ}{U:Till P F}
abbrev RegGas(T:Till P F)(A:Actor N D)(α:ℂ)(y:D)(u:Pane N)(X:Support (More N)):= T.logGas A y (clearF u) α X
namespace Store
variable (G:Store P A W F h ε r g q μ U) {T S: Shot N} (x y:D) (α:ℂ) (Q:Support (More N))(u v: Pane N)
local notation "B_"=>F.p.B
-- copy Chaff.Pulse.fenceW restricted to here.
lemma ping_read (t:ℝ)(S: Support (More N))(h:Agrees (inspected S) u v): pingS t S u↔ pingS t S v:=by
 have he(i:Face (Per (More N)))(l:¬Disjoint S (touched i)):faceValue u i=faceValue v i:=by apply travel_local _ _ u v; apply agrees_mono h; intro y g; refine mem_union_right _ (mem_biUnion.mpr ⟨i,mem_univ _,?_⟩); rw [if_neg l]; exact List.mem_toFinset.mpr g
 exact ⟨fun v i w=> he i w ▸ v i w, fun v i w=> (he i w).symm ▸ v i w⟩
variable {u v}
include G
lemma meter_read (i:LocB N)(V:Agrees (storyE F.p.B i) u v) : u_budget F u i = u_budget F v i:=by
 have ht:= (G.rit.p i).choose_spec; have p:= ping_read u v F.p.threshold (earth i) (agrees_mono V (show inspected (earth i)⊆ storyE B_ i from wake _ (Subset.refl _))); -- specify meta tune
 unfold u_budget numbE; by_cases h:pingS F.p.threshold (earth i) u; rw [Set.indicator_of_mem (show u∈ _ from h), Set.indicator_of_mem (show v∈_ from p.mp h)]; exact ht.term _ _ (agrees_mono V (dorm_sub B_ (earth i)))
 rw [Set.indicator_of_notMem (show u∉_ from h), Set.indicator_of_notMem (show v∉ _ from mt p.mpr h)]
lemma estimate_same (V:Agrees Q u v) : Estimate F α u Q= Estimate F α v Q:=by
 unfold Estimate Ledger.lump; apply tsum_congr; intro i; split; next h=> rw [Vesper.digit,Vesper.digit,uB,uB,G.meter_read i (h ▸ V)]
 next h=> rfl
lemma fuel_same (C:Camera T A x y Q S B_ (P:=P))(i:MFuel N)(p: storyP B_ i.fst ⊆ Q) : fuelVal F T.field T.f i=fuelVal F S.field S.f i :=by
 let t:= i.fst; have h:= (G.ent.p t).choose_spec; have v: storyP B_ t⊆Q:=p; have he: harbor t ⊆ Q:=(dorm_sub B_ _).trans p; have ht: boundF t F.p T.field.1 ↔ boundF t F.p S.field.1:= ping_read _ _ _ _ (agrees_mono C.view ((wake B_ (sdiff_subset (t:= t.val.2))).trans p)); have hx:F.K t T.field=F.K t S.field:=h.values _ _ _ _ (agrees_mono C.view he) (C.frames.mono he)
 unfold fuelVal pickLeaf fB f_budget Scree.clamp; by_cases q:boundF t F.p T.field.1 <;> first | rw [if_pos q,if_pos (ht.mp q),hx,C.feet t v] | rw [if_neg q,if_neg (mt ht.mpr q), C.feet t v]
lemma reg_same (C:Agrees Q u v) (i:MReg N)(p: storyE B_ i.1⊆ Q): regVal F u α i=regVal F v α i:=by unfold regVal; rw [pickStone_val,pickStone_val,uB,uB,G.meter_read i.1 (agrees_mono C p)]
lemma recall_t (C:Camera T A x y Q S B_ (P:=P))(i:Heat N)(p:story B_ i⊆ Q): U.fires A x T α i= U.fires A y S α i:=by
 rcases i with (i|(i|i)); · obtain ⟨k,b,h,v⟩:= C.picks i.1 (p (mem_singleton_self _)); change optionW _ _ _ _ _ = optionW _ _ _ _ _; unfold optionW; rw [b,k,h , show selectP i.1 T.inserts= selectP i.1 S.inserts from (by by_cases p:i.1∈T.inserts; exact (decide_eq_true p).trans (decide_eq_true (v.mp p)).symm; exact (decide_eq_false p).trans (decide_eq_false (mt v.mpr p)).symm)] -- tune decide expr rewrite
 · exact reg_same G α Q C.view i p
 exact fuel_same G x y Q C i p
lemma thorn (i:Shimmer P.stage)(r:(TheoryP P).look i⊆ Q)(b:P.eval Q x y=0): U.e x i= U.e y i:= by
 apply sub_eq_zero.mp; apply norm_eq_zero.mp; apply le_antisymm _ (norm_nonneg _); let L:=(G.pfo.help i); have ht:= L.variation x y; have he:P.stage.eval ((TheoryP P).look i) x y=0:=le_antisymm (b ▸ P.mono r x y) (P.pos _ _ _); rw [he,mul_zero] at ht; exact ht -- tune eq lea
lemma gas_read (C:Camera T A x y Q S B_ (P:=P)): U.logGas A x T α Q= U.logGas A y S α Q:=by
 exact congrArg₂ (·+·) ((Saga P B_).readR (U.e x) (U.fires A x T α) _ _ _ (G.recall_t x y α Q C) (fun i q=>G.thorn x y Q i q C.here)) (estimate_same G α Q C.view)
end Store
end YM.CF.BPress.Engine
