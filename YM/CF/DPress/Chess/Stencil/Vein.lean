import YM.CF.DPress.Chess.Stencil.Shun
import YM.CF.Dial.Beet
/-!
# paid locality of the actual wave on zero and other residues.

Cost is billed at the portico of the column. Read true fine-link argument (will be populated
by the `seine` output). Correct for every pair of actual fields, inside or outside tests. Use
`Peaks.worn` for the fine-to-coarse transport, `Its.Lobe_κ` permits both lobe projections without global lookups. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.DPress.Chess.Symbol
open Function Filter Finset Lattice Bloch Laurent Next.Free Fir Rush Scroll Lat Peaks Cube Tulip Dial SU Branch Drapes Wilson
open scoped Topology BigOperators NNReal ENNReal Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n m N:Side}(G:Ratio n m){A B:Nom n m→Op (Iota G)}{r j:ℕ}
abbrev earnS(i: Iota G)(r:ℕ): Support (More m):= Lattice.halo r {Peaks.touch G false i.1}
-- end-cost directly
lemma visited(x:Site n)(w:Walk)(i:Site n)(p:i∈visits x w): separation (stop x w) i≤ w.length:=by
 induction w generalizing x with
 | nil=> simp [stop,visits] at *; rw [p,separation_self]
 | cons v W ih=> rcases List.mem_cons.mp p with t | t; rw [t,separation_comm]; exact leakspan ..; exact le_trans (ih _ t) (by simp)
structure Stroke (A:Nom n m→Op (Iota G))(r:ℕ):Prop where
 ω :Continuous A
 range : ∀ x i j, Peaks.touch G true i.1 ∉ earnS G j r → A x i j=0
 read : ∀ x y i j, Agrees (earnS G j r) x.1 y.1 → A x i j=A y i j
namespace Stroke
variable {G}
lemma add (p:Stroke G A r)(t:Stroke G B r): Stroke G (fun i=>A i+B i) r:=⟨p.ω.add t.ω,fun x i j y=> by rw [Matrix.add_apply,p.range _ _ _ y,t.range _ _ _ y,zero_add], fun x y i j z=> congrArg₂ (·+·) (p.read _ _ _ _ z) (t.read _ _ _ _ z)⟩
lemma zero : Stroke G (fun _ => 0) r:=⟨continuous_const,fun _ _ _ _=>rfl,fun _ _ _ _ _=>rfl⟩
lemma mul (p:Stroke G A r)(b:ℝ): Stroke G (fun i=> b • A i) r:=⟨p.ω.const_smul b,fun x i j h=>by rw [Matrix.smul_apply,p.range _ _ _ h,smul_zero],fun x y i j h=>congrArg (b • ·) (p.read _ _ _ _ h)⟩
lemma sum{I:Type*}(D:Finset I)(v:I→Nom n m→Op (Iota G))(p:∀ i∈D,Stroke G (v i) r): Stroke G (fun x=>∑ i∈D,v i x) r:=by induction D using Finset.induction_on with|empty=>simpa using (zero (G:=G) (r:=r))|@insert i D h ih=>simp_rw [sum_insert h]; exact add (p i (mem_insert_self ..)) (ih (fun j w=>p j (mem_insert_of_mem w)))
lemma chirality (q:Stroke G A r)(i:Bool): Stroke G (fun x=>Peaks.lobe G i*A x*Peaks.lobe G i) r:=by
 let F:= Peaks.lobe G i; have he (x y:Iota G)(T:Op (Iota G)):(F*T*F) x y= F x x*T x y* F y y:= by
    nth_rw 1 2 [show F= Matrix.diagonal _ from lobe_diag ..]; -- check twice
    rw [Matrix.mul_diagonal,Matrix.diagonal_mul]
 exact ⟨(continuous_const.mul q.ω).mul continuous_const,fun x y z w=>(he y z _).trans (by rw [q.range _ _ _ w,mul_zero,zero_mul]),fun x v y z w=> (he y z _).trans ((by rw [q.read _ _ _ _ w]: F y y*A x y z*F z z= F y y*A v y z*F z z).trans (he ..).symm)⟩
-- single term in drag. radius.
private lemma movement (ho:Odd G.count.val)(r t:St G.count)(k:Cover)(c:ℂ)(o:Lattice.Order)(i:Site n)(R:ℕ)(w:(runD true false G.count r t k o).length≤ R):
 let p:=(i,r); let q:=(i+wrap n k,t); Stroke G (fun X:Nom n m=> panel p q ((Rush.wind i k*c) • (track (unionP X).1 (Peaks.touch G true p) (runD true false G.count r t k o)).1)) R:=by
 intro s q; let u:= runD true false G.count r t k o; let x:= Peaks.touch G true s; let y:= Peaks.touch G false q; have hx: stop x u=y:= worn G true false ho r t k o i; let F(X:Nom n m):= travel X.1 x u; have he(X:Nom n m): (track (unionP X).1 (Peaks.touch G true s) (runD true false G.count r t k o))=brand (F X):=track_pr ..
 refine ⟨?_,?_,?_⟩
 · simp only [he]; have ht:Continuous F:= (travel_cont (K:=SU.E) x u).comp continuous_fst; apply continuous_matrix; intro i j; unfold panel brand; simp only [Matrix.of_apply,Matrix.smul_apply]; split; swap; exact continuous_const
   next v=> exact (((SU.matter_cont.comp ht).matrix_elem i.2 j.2).const_smul (Rush.wind s.1 k*c))
 · intro X i j v; unfold panel; rw [Matrix.of_apply]; split; next t=> exfalso; apply v; unfold earnS; simp only [t,halo_spec,mem_singleton,exists_eq_left]; change separation y x ≤ _; rw [←hx,separation_comm]; exact (leakspan ..).trans w
   next t=> rfl
 intro X Y i j p; unfold panel; simp only [he,Matrix.of_apply]; split; next h=>
   have ht(z:Site (More m))(u':z∈visits x u): z∈ earnS G j R:=by simp only [earnS,halo_spec,h,mem_singleton,exists_eq_left]; change separation y z≤ _; rw [←hx]; exact (visited x u z u').trans w
   rw [show F X= F Y from travel_local _ _ _ _ (fun i t v=>p i (ht _ t) (ht _ v))]
 next h=> rfl
lemma stork (ho:Odd G.count.val)(r t:St G.count)(k:Cover)(c:ℂ)(o:Lattice.Order)(R:ℕ)(w:(runD true false G.count r t k o).length≤ R): Stroke G (fun X:Nom n m=> drag G true false r t k c o (unionP X)) R:= sum univ _ (fun i _=>movement ho r t k c o i R w)
end Stroke
end YM.CF.DPress.Chess.Symbol
