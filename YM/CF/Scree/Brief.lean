import YM.CF.Scree.Cook
import YM.CF.Cascade.May
import YM.CF.Tap.Patois
import YM.Push.SECTOR_MEASURE.Gauges
set_option autoImplicit false
noncomputable section
namespace YM.CF.Scree
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
-- addresses all finite post-collapse
abbrev Hub(n:Side):= {i: Seat n × Support (More n)//i.1∈i.2}
def moveHub {n:Side}(a:Sweep n)(v: Hub n) : Hub n:= ⟨( (boxA a).symm v.val.1, v.val.2.map (boxA a).symm.toEmbedding), Finset.mem_map_of_mem _ v.property⟩
abbrev OrbHub{n:Side}(v:Hub n):Finset (Hub n):= univ.image fun a:Sweep n=>moveHub a v
abbrev Force(n:Side) := {x:Hub n× Support (More n) // x.2.Nonempty∧ x.2 ⊆ x.1.val.2} -- halo reg via law
def moveForce {n:Side}(s: Sweep n)(v:Force n):Force n:= ⟨(moveHub s v.val.1, v.val.2.map (boxA s).symm.toEmbedding), Finset.map_nonempty.mpr v.property.1,map_subset_map.mpr v.property.2 ⟩
abbrev Cipher(n:Side):= ribbon (Single n)
instance {n:Type*}[LinearOrder n][Fintype n]: MeasurableSpace (Dough n):=borel _
instance {n:Type*}[LinearOrder n][Fintype n]: BorelSpace (Dough n):=⟨rfl⟩
abbrev InkD(n:Side):=Pane n→ Cipher n
abbrev Copy(n:Side):=Orbit n→ Cipher n
abbrev tangD(n:Side):=RG.Directions group (More n)
abbrev Dwell(n:Side):= LeanV (Single n)
-- max endpoint norm factor
variable {n:Side}
def endL (x: Seat n)(v:Finset (Dwell n)):ℕ:=v.sup fun i=>separation x (node i.2.1.1)
def tariff (p:RG.BudgetPoint)(x:Seat n)(h:ℝ)(v:Finset (Dwell n)):= (1+(endL x v:ℝ))^p.power*h^v.card
-- unscaled tests Euclidean in each color & sup 
structure Signs {N:Type*}[NormedAddCommGroup N][NormedSpace ℝ N](p:RG.BudgetPoint)(x:Seat n)(F:tangD n→N)(c:ℝ):Prop where
 grade: 0≤c
 paid: ContDiffAt ℝ (p.order:ℕ∞) F 0
 token (j:ℕ):j≤p.order→∀ k:Fin j→ tangD n, (∀ i,p.dirBound x (k i))→ ‖iteratedFDeriv ℝ j F 0 k‖≤c
-- OPEN strict thresholds for regular and kernel mask labels; the physical flags stay RG's.
section strict
open RG
def pingS{G:Gauge}{c:Side}(e:ℝ)(X:Support c)(U:Config G c):Prop:=∀ i:Face (Per c), ¬Disjoint X (touched i) → G.chord (faceValue U i)<e
variable {G:Gauge}{S:Side}{U:Config G S}{X:Support S}{e d:ℝ}
lemma pingB(U:Config G S)(g:Site S→ G.El): pingS e X (gauge g U) ↔ pingS e X U:=by unfold pingS; simp_rw [face_gauge,G.chord_conj]
lemma ping_o : IsOpen {U:Config G S|pingS e X U}:=by
 classical
 rw [show {U:Config G S|pingS e X U}= ⋂ i:({j:Face (Per S)//¬Disjoint X (touched j)}),{U : Config G S|G.chord (faceValue U i.val)<e} from by ext; simp [pingS]]
 apply isOpen_iInter_of_finite; intro i; exact isOpen_lt (by unfold faceValue; fun_prop) continuous_const
lemma ping_le (h:pingS e X U): Healthy e X U:= Finset.disjoint_left.mpr fun x w p=> by obtain ⟨i,g,z⟩:= (flags_spec ..).mp p; exact z.not_gt (h i (fun z=>Finset.disjoint_left.mp z w g))
lemma ping_lo (h:d<e)(g:Healthy d X U):pingS e X U:=by
 classical
 intro i q; apply lt_of_le_of_lt _ h; apply le_of_not_gt; intro v; obtain ⟨j,b,k⟩:=Finset.not_disjoint_iff.mp q; exact Finset.disjoint_left.mp g b ((flags_spec ..).mpr ⟨i,k,v⟩)
-- recover origin jets from library Health on a half subbudget
def pintK (p:BudgetPoint): BudgetPoint:={p with threshold:=p.threshold/2, threshold_pos:=half_pos p.threshold_pos, threshold_le:=(half_le_self p.threshold_pos.le).trans p.threshold_le}
lemma ping_f(p:BudgetPoint)(X:Support S): pingS p.threshold X (1:Config G S):=by intro i _; simpa [Lattice.faceValue,travel,square,oriented] using p.threshold_pos
end strict
abbrev BedP (p:RG.BudgetPoint)(V: Pane n)(F:InkD n)(X:Hub n)(c:Finset (Dwell n)→ℝ):Prop:= pingS p.threshold X.val.2 V → ∀ z: Finset (Dwell n), Signs p X.val.1 (fun x:tangD n=>crumb (F (RG.increment V x)).val z) (c z)
abbrev camp (X: Support (More n)): Finset (Dwell n):= univ.filter fun i=> node i.2.1.1 ∈ X
abbrev RegBudget (n:Side):=Hub n→InkD n
structure PressB (p:RG.BudgetPoint)(X:Hub n)(F:InkD n)(h v:ℝ): Prop where
 term : LocalOn X.val.2 F
 fitted(V): Flour (camp X.val.2) (F V).val
 measureV: Measurable F -- check instance
 gaugeV (V:Pane n)(g:Seat n→E): F (Lattice.gauge g V)= paintR false false (tradew n g) (F V)
 worth: ∃ b:Finset (Dwell n)→ℝ,(∀ i,0≤b i) ∧ (∀ U, BedP p U F X b) ∧ (∑ i:Finset (Dwell n), tariff p X.val.1 h i * b i)≤v
structure IncX (Q:Sweep n → Prop)(E:RegBudget n)(p:RG.BudgetPoint)(h δ:ℝ):Prop where
 weight:∃ v:Hub n→ℝ,(∀ x, PressB p x (E x) h (v x))∧ ∀ x:Seat n,(∑ i:Hub n,if x=i.val.1 then p.mass i.val.2 (v i) else 0) ≤ δ
 face (s:Sweep n):Q s→∀ U,JetS s.s s.charge (detX s.s) U→∀ X:Hub n,∀ V:Pane n, E (moveHub s X) (flashA s V)=paintR s.charge (detX s.s) (prepU (castX s) U (xtra s.charge) n) (E X V)
def openG (p:RG.BudgetPoint)(X:Support (More n))(x:tangD n): tangD n:= fun i=> if Disjoint (ends i) (Lattice.halo (5*p.B) X) then x i else 0
structure ForceB (p:RG.BudgetPoint)(X:Force n)(F:Copy n)(h v:ℝ):Prop where
 values (V W:Pane n)(τ ν:Ids n) : Agrees X.val.1.val.2 V W→Set.EqOn τ ν X.val.1.val.2 → F (V,τ)=F (W,ν)
 fitted(x): Flour (camp X.val.1.val.2) (F x).val
 flagsV : ¬ RG.inspected X.val.2 ⊆ X.val.1.val.2 → F=0
 measureV: Measurable F
 protect(x:Orbit n): F x≠0→X.val.2⊆RG.flags p.threshold x.1
 gaugeV (V:Pane n)(τ: Ids n)(g:Seat n→E): F (Lattice.gauge g V,threadG g τ)= paintR false false (tradew n g) (F (V,τ))
 costP: ∃ b:Finset (Dwell n)→ℝ,(∀ i,0≤b i)∧(∀ U:Orbit n, pingS p.threshold (X.val.1.val.2\ X.val.2) U.1 →∀ z:Finset (Dwell n), Signs p X.val.1.val.1 (fun i=>crumb (F (RG.increment U.1 (openG p X.val.2 i),U.2)).val z) (b z)) ∧(∑ i:Finset (Dwell n),tariff p X.val.1.val.1 h i*b i) ≤ v
abbrev ForceBudget(n:Side):=Force n→Copy n
structure Dark (Q:Sweep n → Prop)(F:ForceBudget n)(p:RG.BudgetPoint)(h δ:ℝ):Prop where
 weight:∃ v:Force n→ℝ,(∀ x, ForceB p x (F x) h (v x))∧ ∀ x:Seat n,(∑ i:Force n,if x∈i.val.1.val.2 then p.mass i.val.1.val.2 (v i) else 0) ≤ δ
 face (s:Sweep n):Q s→∀ U,JetS s.s s.charge (detX s.s) U→∀ X:Force n,∀ (V:Pane n)(τ:Ids n),Injective (priorP τ) → F (moveForce s X) (flashA s V,bun s τ)=paintR s.charge (detX s.s) (prepU (castX s) U (xtra s.charge) n) (F X (V,τ))
-- flat test exact PH orbit. Only short nonwrapping. quantity fixed boost later
def motP (D: RegBudget n)(s:Hub n)(i j:Single n):ℂ:= let X: Finset (Dwell n):={ (true,i), (false,j)}; star (crumb (Pastry.wire true i *Pastry.wire false j) X) * crumb (D s 1).val X
def insp (D:RegBudget n)(s:Hub n): Op (Single n):= Matrix.of fun i j=> ∑ X∈ OrbHub s, motP D X i j
-- cover Fourier; periodization unique lift range nonwrapping
abbrev rebate (D: RegBudget n)(s:Hub n)(v:Site n): Pal:= Matrix.of fun i j=> (wind (0:Site n) (lift v))⁻¹ * insp D s ((0,i.1),i.2) ((v,j.1),j.2)
def theme(D:RegBudget n)(s:Hub n) (p: Bloch.Momentum): Pal:= ∑ v:Site n, mode p (lift v) • rebate D s v -- check mode sign
structure Standard(p:RG.BudgetPoint)(D:RegBudget n)(j:ℕ)(M:Tulip.Male):Prop where
 void1(x:Hub n): Pastry.pane (D x 1)=0
 pot1 (X:Hub n)(h:Nonwrapping X.val.2 X.val.1)(x y:tangD n)(k: RG.IsAffineDirection X.val.1 x)(v: RG.IsAffineDirection X.val.1 y): iteratedFDeriv ℝ 2 (fun z : tangD n=> Pastry.pane (D X (RG.increment 1 z))) 0 ![x,y]=0
 themeZ(X:Hub n)(h:Nonwrapping X.val.2 X.val.1): Tap.AxisP (theme D X) ∧ Tap.NullW (Tap.potion j M (theme D X))
end YM.CF.Scree
