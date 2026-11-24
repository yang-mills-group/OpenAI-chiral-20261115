import YM.CF.BPress.Engine.Reads
/- regular-only projected log. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Engine
open Function Filter NormedSpace MeasureTheory Finset Lattice Branch Ledger Push.AbsoluteSums Palmer Fock Pastry Pine Pine.EdgeD Pf Vesper Spin Spin.Pledge Spin.Stride Currency Spin.Cellar Spin.Cellar.Pass Spin.Basement Pine.Story
open Spark Cube Lat SU Spin.Paint Skye Girt Scree Tulip Tenant Pf.RealBook RG Chalk Lily DoughBag Shot Till Store
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical YM.CF.BPress.Vesper
attribute [local instance] opCStarAlgebra
variable {N:Side}{D:Type}{P:Form N D} [TopologicalSpace D]
variable {A:Actor N D}{W:Pledge}{F:GramM N}{μ h ε r g q:ℝ}{U:Till P F}
namespace Store
variable (G:Store P A W F h ε r g q μ U) {T: Shot N} (x y:D) (α:ℂ) (Q:Support (More N))(u v:Pane N)
local notation "B_"=> F.p.B
private lemma vacant_γ (i:MFuel N)(p:T.f i.fst=0):U.fires A x T α (.inr (.inr i))=0:=by
 change fuelVal _ _ _ _=0; unfold fuelVal pickLeaf fB; rw [p,weft, wee_zero,zero_mul]; rfl
private lemma bare_γ (i:WantJ N)(p:T.j i.fst=0): U.fires A x T α (.inl i)=0:=by change T.j _*_=0; rw [p,zero_mul]
private lemma reg_0 (i:MReg N) : U.fires A x (clearF u) 0 (.inr (.inl i))=0:=by change regVal F u _ _=0; unfold regVal; rw [pickStone_val, uB,weft, wee_zero,zero_mul]; rfl
lemma cold_base (A:Actor N D)(U: Till P F): RegGas U A 0 x u Q=0:=by
 have hp(i): U.fires A x (clearF u) 0 i=0:=by rcases i with (i|(i|i)); exact bare_γ _ _ _ rfl; exact reg_0 _ _ i; exact vacant_γ _ _ _ rfl
 unfold RegGas logGas PutLog Estimate; rw [funext hp, tape_nill,zero_add,Ledger.lump,tsum_fintype,sum_eq_zero]; intro i v; unfold Vesper.digit; rw [uB,weft,wee_zero,zero_mul]; split<;>rfl
include G
lemma tainted(i:MFuel N)(h: Disjoint (trueFlags F T.field) (storyP F.p.B i.fst)) : U.fires A x T α (.inr (.inr i))=0:=by
 let j:=i.fst; have ht:= (G.ent.p j).choose_spec; have hv:F.K j T.field=0:=by
    by_contra e; obtain ⟨u,q⟩:=j.property.1; exact Finset.disjoint_left.mp h (ht.protect _ e q) (dorm_sub (X:=harbor j) _ (j.property.2 q))
 change fuelVal _ _ _ _=0; unfold fuelVal pickLeaf fB; rw [show f_budget F T.field i.fst=0 from ?_,weft,mul_zero]; rfl
 unfold f_budget Scree.clamp; split; exact hv; rfl
omit G
-- drop possible extras on supports, exact equality even when weights not bounded
structure barren (F:GramM N)(T:Shot N)(Q: Support (More N)):Prop where
 arms: ∀ i:Site N,node i∈Q→ T.j i=0
 cold: Disjoint (trueFlags F T.field) Q
include G
lemma still_gas (p:barren F T Q): U.logGas A x T α Q=RegGas U A α x T.field.1 Q:=by
 apply congrArg₂ (·+·) _ rfl; apply readR _ _ _ _ _ _ _ (fun i _=>rfl); intro i v; rcases i with (i|(i|i)); · exact (bare_γ _ _ _ (p.arms i.1 (v (mem_singleton_self ..)))).trans (bare_γ _ _ _ rfl).symm
 · rfl
 exact (G.tainted x α i (p.cold.mono Subset.rfl v)).trans (vacant_γ _ _ _ rfl).symm
lemma reg_read (p:P.eval Q x y=0)(s:Agrees Q u v): RegGas U A α x u Q= RegGas U A α y v Q:=by
 apply congrArg₂ (·+·) _ (estimate_same G α Q s); apply readR _ _ _ _ _ _ _ (fun i t=> G.thorn x y Q _ t p); intro i h; rcases i with (i|(i|i)); · exact (bare_γ _ _ _ rfl).trans (bare_γ _ _ _ rfl).symm
 · exact G.reg_same α Q s i h
 exact (vacant_γ _ _ _ rfl).trans (vacant_γ _ _ _ rfl).symm
omit G
lemma pureOp(H:Op (Single N))(K:Paint (More N)): let F':= F; let A:= clearF u;
 opus F' A.field α A.f K A.stampX H A.j A.inserts=tank H (exp (weft α (office F u))):=by
 intro F A; let T:=oceans K A.stampX A.j A.inserts; unfold opus; have he:tomes univ T=1:=by suffices H:∀ S:Support N,tomes S T=1 from H _; intro s; induction s using Finset.induction_on with|empty=>simp|@insert i s h ih=> rw [brick _ _ _ h,ih,mul_one]; change 1+ (0:ℂ) • _= _; rw [zero_smul,add_zero]
 let X:=fB F A.field A.f; have ht: X=(fun _ :Force N=>(0:Cipher N)):=by funext i; unfold X fB; rw [show A.f i=0 from rfl,weft,wee_zero,zero_mul]
 rw [he,one_mul]; unfold strength pantry; rw [show fB F A.field A.f=X from rfl,ht,Vesper.box_zero,mul_one]; rfl
include G
lemma reg_expected (p:‖α‖≤1)(ω: Wave (Single N))(t:Pf.Top (mood (A.A x) (A.M x)) ω): let Q:= A.A x; let D:= F; let a:= A.seat x; wick (holdα a (A.KG x)) ω (tank Q (exp (weft α (office D u))))=Complex.exp (∑ i:Support (More N),RegGas U A α x u i):=by
 intro Q D a; rw [←pureOp (F:=F) α u Q (A.KG x)]; exact lift_log G α p x (readyF u g G.Tclock.he) ω t -- tune
end Store
end YM.CF.BPress.Engine
