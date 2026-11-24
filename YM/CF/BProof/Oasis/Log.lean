import YM.CF.BProof.Oasis.Rot
/-! Full-log and the *separate* pure contributions. Only rotate pure pieces
when doing extension/averaging; other terms stay as computed. -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.BProof.Oasis
open Function Filter Fock Finset NormedSpace Garden Align Wick Double Pastry Crystal MeasureTheory Dew
open Lattice Tenant Lat Cube Tulip Scree Skye Spin Branch Stint Hearth Tape Palot RG Push.AbsoluteSums Civic
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical Hearth ENNReal
attribute [local instance] opCStarAlgebra
variable {j:ℕ}{a b l r δ c v η:ℝ}{N:Side}{P:Spin.Ready j a b l r}{F: Core j a b l r N}{H:Honor P F δ}(x:Loft F δ c v η){D:GramM N}{m o α C κ:ℝ}
variable {y:Pay}(M:Marks H y c v η)(q:Cargo D m o)(R:Tube D y m κ o α C)
def PureLog (D:GramM N)(z:Pane N)(t:ℝ):ℂ:= PriceR D t z+ ∑ i, gustLog x M 0 0 t D z i
def fBusy(x:Loft F δ c v η)(M:Marks H y c v η)(D: GramM N)(X:Plant N)(p:Orbit N)(f:Fields N)(ε:ℂ)(s:Support N)(i:Y (More N)):ℂ:=gustLog x M (tokenJ s f.2 ε X (coreB x)) (RateF D f.1 p) 1 D p.1 i - gustLog x M 0 0 1 D p.1 i
def fuelLog(D: GramM N)(X:Plant N)(p:Orbit N)(f:Fields N)(ε:ℂ)(s:Support N):ℂ:=PureLog x M D p.1 1+ ∑ i, fBusy x M D X p f ε s i
abbrev fPrice (q:Cargo D m o) (i:Y (More N)) := (plaza D.p N).logP M.award (q.runs κ) i
include q R
lemma quietBill(i:Y (More N))(t:ℝ)(p:‖t‖≤1)(Z:Pane N): ‖gustLog x M 0 0 t D Z i‖≤ fPrice (κ:=κ) M q i:=Able.bills (Tube.known M q R) (quiet x M q R t p Z) _
lemma busyBill(X:Plant N)(p:Orbit N)(f:Fields N)(i:Y (More N))(s:Support N){ε:ℂ}(u:∀ i,‖X.leaf i‖≤ sitePrice)(he:‖ε‖≤κ): ‖fBusy x M D X p f ε s i‖≤ 2*fPrice (κ:=κ) M q i:= (norm_sub_le ..).trans ( (add_le_add (Able.bills (Tube.known M q R) (busy x M q p s f u he) i) (quietBill x M q R i 1 (by simp) p.1)).trans_eq (two_mul _).symm)
lemma classD(X:Plant N)(k:Orbit N)(b:Fields N)(s:Support N)(ε:ℂ)(e:‖ε‖≤κ)(A:Plant N)(g:∀ i,i∈s→ A.leaf i= opJ (chef i) (coreB x) (X.leaf i))(R':Phys N)(u:valid x R') (d:∀ i,‖X.leaf i‖≤ sitePrice):
 oracle x R' ((optional ε b.2 A).prod s * tank (coreA x) (boardF D k b.1))=Complex.exp (fuelLog x M D X k b ε s):=by
 let V:= extinctD x u M q R 1 k.1 (tokenJ s b.2 ε X (coreB x)) (RateF D b.1 k) (busy x M q k s b d e); rw [zoomB D b.1 q.fitted k, ←cookerJ X ε s b.2 (coreSkew x) A g, V]; congr 1; unfold fuelLog PureLog fBusy; rw [sum_sub_distrib]; abel
lemma staying (p:Pane N)(t:ℝ)(u:Phys N)(g:valid x u)(v:‖t‖≤1): Complex.exp (PureLog x M D p t)=oracle x u (tank (coreA x) (zoom D t 0 p)):=by
 have he:= (extinctD x g M q R t p 0 0 (quiet x M q R t v p)); rw [evaporate,map_one,one_mul] at he; exact he.symm
lemma airy (p:Pane N) : Continuous (fun t:Gas.Pearl=> PureLog x M D p t.val):=by
 unfold PureLog PriceR; apply Continuous.add
 · unfold DecR; fun_prop
 apply continuous_finsetSum _; intro i _; apply Civic.continuity (p:=plaza D.p N) _ _ (Tube.known M q R) (fun i:Gas.Pearl=> quiet x M q R i.val (by rw [Real.norm_of_nonneg i.property.1]; exact i.property.2) p) (fun _ _ _ _=> continuous_const); rintro (i|(i|i)); exact continuous_const; unfold hotA actionsG; simp only [Sum.elim_inr,Sum.elim_inl]; unfold FeeR; fun_prop; exact continuous_const
omit q R -- sap point property
lemma origin(p: Pane N): PureLog x M D p 0=0:=by
 have he: hotA D 0 0 p 0= (0:Options N→ℂ):=by ext1 (i|(i|i)); rfl; change (0:ℝ) • (_:ℂ)=0; rw [zero_smul]; rfl
 unfold PureLog PriceR DecR gustLog; simp_rw [he, Civic.origin]; simp
include q R in
theorem totalInvariant (z: Pane N)(g:Geometry N) : PureLog x M D z 1=PureLog (runH H x g) M D (Lattice.gauge g z) 1:=by
 obtain ⟨u,h⟩:=chooseS H x; let f(t:Gas.Pearl):=PureLog x M D z t.val; let h'(t:Gas.Pearl):=PureLog (runH H x g) M D (Lattice.gauge g z) t.val; apply Gas.simpleL f h' (airy x M q R z) (airy (runH H x g) M q R _) (by unfold f h'; rw [show (0:Gas.Pearl).val=(0:ℝ) from rfl,origin,origin]) _ 1; intro t; unfold f h'; have he:‖t.val‖≤1:=by rw [Real.norm_of_nonneg t.property.1]; exact t.property.2
 rw [← Complex.exp_eq_exp_ℂ]; rw [staying x M q R z t.val u h he,staying (runH H x g) M q R _ _ _ (owners H x g u h) he]; exact waveH H x q ..
end YM.CF.BProof.Oasis
