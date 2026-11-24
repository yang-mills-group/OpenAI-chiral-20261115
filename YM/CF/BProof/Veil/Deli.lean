import YM.CF.BProof.Veil.Part
/-! Invariant extension (regular-only Fgas) on Quiet. -/
set_option autoImplicit false
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.CF.BProof.Veil
open Function Filter NormedSpace Finset MeasureTheory RecN
open Cube Lattice Tenant SU Lat Dial Tulip Fock Skye Spin Branch Hearth Tape Hero Stint Oasis Scree Palot Wick Crystal
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical Hearth Tape Mark
attribute [local instance] opCStarAlgebra
-- simplify giant Hall support interfaces
variable {m B N:Side} {D:GramM N} {j:ℕ}{a b l r c v δ η o h ε α C:ℝ} {P:Spin.Ready j a b l r}{F:Core j a b l r N}{H:Honor P F δ}
variable {y:Pay}(M:Marks H y c v η)(q:Cargo D h o)
include q in
lemma offerK {Z Z':Pane N}(m:ℝ)(i:Options N)(e:(pine N).agree (streets D.p i).val Z Z'): hotA D m 0 Z 0 i= hotA D m 0 Z' 0 i:=by
 rcases i with i|(i|i); · unfold hotA; simp only [Sum.elim_inl]
 · change (pine N).agree (lot D.p i.1.2) Z Z' at e; let j:Oasis.Stem N:= i.1; have hv: readR D j Z= readR D j Z':=Cargo.dataR q j ((pine_eq _).mp e); exact congrArg (fun A:Cipher N=> m • Pastry.crumb A.val i.2.val) hv
 unfold hotA actionsG; simp only [Sum.elim_inr]
lemma feeC(i:Finset (Dwell N)): Measurable (fun A:Cipher N=> Pastry.crumb A.val i):=by
 apply Continuous.measurable; exact ((show Continuous (fun B:FC (Dwell N)=> B i ∅) from (continuous_apply ∅).comp (continuous_apply _)).comp continuous_subtype_val)
include q
lemma offerM (m:ℝ)(i:Options N):Measurable (fun p:Pane N=> hotA D m 0 p 0 i):=by
 rcases i with i|(i|i); exact measurable_const; exact (show Measurable fun p=> m • Pastry.crumb (readR D i.1 p).val i.2.val from (feeC _|>.comp (q.measR _)).const_smul m); exact measurable_const
lemma DecRead (i:Oasis.Stem N)(Z Z':Pane N)(m:ℝ)(g:(pine N).agree (lot D.p i.2) Z Z') : DecR D m Z i=DecR D m Z' i:=by unfold DecR; rw [q.dataR _ ((pine_eq _).mp g)]
-- generalized sap locality with £. Keep crop uses separate
theorem minor (i:Y (More N)) (x x':Loft F δ c v η)(Z Z':Pane N) (m:ℝ)(p:(quiet N).agree i.val (Z,sion x) (Z',sion x')): gustLog x M 0 0 m D Z i=gustLog x' M 0 0 m D Z' i:=by
 have hg: (pine N).agree i.val Z Z'∧(window N).agree i.val (sion x) (sion x'):= (paired _).mp p
 have hx:= (stateD H i.val x x' hg.2).2
 refine Civic.gaugeRead (plaza D.p N) (M.eye x) (M.eye x') (hotA D m 0 Z 0) (hotA D m 0 Z' 0) i ?_ (fun v u=> offerK q m v ((pine N).onwards hg.1 u))
 let V:= (Tape.kiln H.1 c v η).st; exact (fun j f p u _=> niceEye x M j x' (le_antisymm ((V.includeV f x x').trans_eq hx) (V.pos ..)) p u)
abbrev KeyP(N:Side):= Oasis.Stem N ⊕ Y (More N)
def cityS(D:GramM N) : KeyP N→Support (More N):= Sum.elim (fun i=> lot D.p i.2) stern
def cityP(M:Marks H y c v η)(q:Cargo D h o)(ε:ℝ) : KeyP N→ℝ:= Sum.elim q.vouchR (fPrice (κ:=ε) M q)
def cityF(M:Marks H y c v η)(D:GramM N)(p:Pane N × Loft F δ c v η): KeyP N→ℂ:= Sum.elim (DecR D 1 p.1) (gustLog p.2 M 0 0 1 D p.1)
variable (R:Tube D y h ε o α C)
omit q
lemma valueQ(D:GramM N)(p:Pane N×Loft F δ c v η): (∑ i:KeyP N,cityF M D p i)= PureLog p.2 M D p.1 1:=Fintype.sum_sum_type ..
include q
lemma city_ne(i:KeyP N):(cityS D i).Nonempty:=by rcases i with i|i; exact (field D.p i.2).property; exact i.property
include R
lemma city_pay: Moment.Toll (cityS D) (cityP M q ε) (α/4) (Cargo.roomAge D.p.B (o+o)+4*C):= Moment.Toll.sum _ _ ((q.boughtR ((coin_ge _).trans R.cost) R.knot R.chew R.norm.le).weaken _ _ (show α/4≤α from by linarith [R.norm]) le_rfl) _ _ (R.known M q|>.prices)
lemma city_heat(i:KeyP N)(v:cityP M q ε i ≠0): Grove (terr _) (cityS D i):=by rcases i with i|i; exact lot_ok ..; exact (R.known M q).logG i v
lemma city_meas(i:KeyP N) : Measurable (fun x=>cityF M D x i):= by
 rcases i with i|i
 · exact ((feeC _|>.comp (q.measR _)).const_smul (1:ℝ)).comp measurable_fst
 apply Civic.measurable; -- tune apply def
 · intro j k t _; exact ((M.expo ..).connected.measurable).comp measurable_snd
 intro v; exact (offerM q 1 v).comp measurable_fst
lemma cityTag(i:KeyP N)(J:Occasion c v η): ∃ X: Quiet N→ℂ, TagF (quiet N) (T:=cityS D i) X (cityP M q ε i) ∧ ∀ p:Pane N×Loft F δ c v η, X (p.1,sion p.2)=cityF M D p i:=by
 letI:=standard H J; apply RecN.wid (quiet N) ((city_pay M q R).nonneg i) (T:=cityS D i) (ρ:=fun p:Pane N×Loft F δ c v η=> (p.1,sion p.2)) (by fun_prop) (fun x=>cityF M D x i) (city_meas M q R i)
 · intro x; rcases i with i|i; exact Dec_cost q ((coin_ge _).trans R.cost) i (by simp:‖(1:ℝ)‖≤1) _; exact quietBill x.2 M q R i 1 (by simp) x.1 -- tune
 intro x y t; rcases i with i|i; exact DecRead q i x.1 y.1 _ ((paired (cityS D _) |>.1 t).1); exact minor M q i x.2 y.2 x.1 y.1 1 t
structure Pantry (M: Marks H y c v η)(q:Cargo D h o)(ε:ℝ) where
 loan(i:KeyP N): Part (quiet N) (cityS D i) (cityP M q ε i)
 book(x:Pane N × Loft F δ c v η): (∑ i:KeyP N, (loan i).val (x.1,sion x.2))=PureLog x.2 M D x.1 1
lemma served (J:Occasion c v η) : Nonempty (Pantry M q ε):=by
 choose X f v' using fun i=> cityTag M q R i J; refine ⟨fun i=> ⟨(quiet N).varnish (X i),(quiet N).even (cityS D i) (f i), (quiet N).evenFix⟩,fun x=>?_⟩; let Z:= (quiet N); let p:= (x.1,sion x.2); let U:= PureLog x.2 M D x.1 1; change ∑ i:KeyP N,Z.varnish (X i) p=U; rw [Z.varnishList _ (cityP M q ε) (cityS D) p f]; · unfold U; rw [← valueQ M D x]; exact sum_congr rfl fun i _=>v' i x
 intro g; let y:Pane N × Loft F δ c v η:=(gauge g x.1,Oasis.runH H x.2 g)
 have hi: Z.act g p=(y.1,sion y.2):=rfl; rw [hi]; unfold p; have he(i):=v' i x; simp_rw [he, v' (p:=y)]; rw [valueQ,valueQ]; exact (totalInvariant x.2 M q R _ _).symm
end YM.CF.BProof.Veil
