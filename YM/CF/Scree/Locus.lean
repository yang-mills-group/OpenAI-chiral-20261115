import YM.CF.Scree.Brief
set_option autoImplicit false
noncomputable section
namespace YM.CF.Scree
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n:Side}
def numbE (t:ℝ)(P:Support (More n))(F:InkD n):InkD n := Set.indicator {U|pingS t P U} F
def exponentL (p:RG.BudgetPoint)(F:RegBudget n) (V:Pane n) : Cipher n:=∑ i:Hub n, numbE p.threshold i.val.2 (F i) V
abbrev coverF (p: RG.BudgetPoint)(X: Finset (Force n))(V:Pane n) := X.biUnion (fun i=>i.val.2) = RG.flags p.threshold V
abbrev boundF (x: Force n)(p:RG.BudgetPoint)(U: Pane n):Prop:= pingS p.threshold (x.val.1.val.2\x.val.2) U
def clamp (p: RG.BudgetPoint)(i:Force n)(U:Copy n)(W:Orbit n):Cipher n:=by classical exact if boundF i p W.1 then U W else 0
def fueled (p: RG.BudgetPoint)(F:ForceBudget n)(W:Orbit n):Cipher n:=by classical exact ∑ i: Finset (Force n), if coverF p i W.1 ∧ Set.PairwiseDisjoint (i:Set (Force n)) (fun x=> x.val.1.val.2) then ∏ j∈i, clamp p j (F j) W else 0
lemma fuel_one (p:RG.BudgetPoint)(F:ForceBudget n)(W:Orbit n)(h:RG.flags p.threshold W.1=∅): fueled p F W=1:=by
 classical
 unfold fueled; rw [sum_eq_single ∅]; simp [coverF,h]; intro i _ t; rw [if_neg]; rintro ⟨g,z⟩; obtain ⟨y,u⟩:=nonempty_iff_ne_empty.mpr t; obtain ⟨a,v⟩:= y.property.1
 unfold coverF at g; have hq:=h ▸ g; exact absurd (show a∈ (∅:Support (More n)) from hq ▸ Finset.mem_biUnion.mpr ⟨y,u,v⟩) (notMem_empty _)
 simp
structure GramM (n:Side) where
 p:RG.BudgetPoint
 path:RG.PathData group
 funds: RG.Clip
 beta:ℝ
 J:Interest n
 F: RegBudget n
 slip: RegBudget n
 K: ForceBudget n
 v:ℂ -- regulator chiral phase v; real-positive rp v actual Weyl overlap may need chart. allow here.
-- evaluated state (physical) relative to prior×tag; S_K even though total may odd sector
abbrev Phys(n:Side):= Wave (Single n)
abbrev Loom(n:Side):= Orbit n→ Pane n
namespace GramM
variable(R:GramM n)
abbrev H0 (V:Pane n):ℂ:= R.v - ↑(R.path.inChannels R.funds R.p R.beta V) -- no volume normalization
def board(V:Orbit n): Cipher n:= exp (exponentL R.p R.F V.1+exponentL R.p R.slip V.1)*fueled R.p R.K V
def betaL (L:Loom n)(W:Orbit n) :ℂ:= H0 R W.1 - Pec.pigment R.J.I (L W)
end GramM
variable {m C B L:Side}{j:ℕ}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{e u:ℝ}
abbrev mid(m B:Side):=CSide m B
def relV(P:Grasp Y B e)(M:Interest (mid m B))(V:Pane (mid m B)):Phys (mid m B):=let A:=spar j M.M V; acts (exp (dg (Kennel.capT A (M.P.den V)))) (changeM (m:=m) P V M.M)
-- avoid if proof by tag polynomial roll - need relative at h law independence
def column {I:Type*}[Fintype I][LinearOrder I]{A:Type*}[Monoid A](F:I→A)(S:Finset I): A:= ((S.sort (·≤·)).map F).prod
def tank{I:Type*}[Fintype I][LinearOrder I](A:Op I)(x:ribbon I): FC I:= ∑ s:Finset (LeanV I),crumb x.val s • column (I:=LeanV I) (drawT A) s
def denZ (R:GramM (mid m B))(P:Grasp Y B e)(A:Loom (mid m B))(V:Orbit (mid m B)): Phys (mid m B):= Complex.exp (R.betaL A V) • acts (tank (spar j R.J.M (A V)) (R.board V)) (relV P R.J (A V))
lemma tank_eq {I:Type*}[Fintype I][LinearOrder I](A:Op I)(x:ribbon I)(h:IsStarProjection A): tank A x=(nursery A h).cook x:=rfl
abbrev beamZ (n:Side)(v:Phys n):ℂ := inner ℂ (mateK n) v
abbrev city (n:Side):Measure (Orbit n):=(prior group (More n)).prod (depot n)
variable (R:GramM (mid m B))(P:Grasp Y B e)(A:Loom (mid m B))
def partitionZ :ℂ:=∫ V:Orbit (mid m B),beamZ _ (denZ R P A V) ∂city _
def scaleZ (Q:Op Slot)(v:Phys n): Phys n:=let Z:=exp (-(plankP n Q)); (skyGlow (mateK n) Z (mateK n))⁻¹ • acts (quant Z) v
-- Uniform forest weights; split roots later
instance woodF(c f:Side)(D:Ratio c f): Fintype (Forest D):=by classical
  letI:Finite Step:=Finite.of_injective (fun x: Step=>(x.dir,x.neg)) (fun a b h=>by cases a; cases b; simpa using h)
  let t(F: Forest D) : (Site f→Step)× (Site f → Fin (4*D.count.val+1)):= (F.up, fun i=> ⟨F.height i,(Nat.lt_add_one_iff.mpr (F.bound i))⟩)
  have hp:Injective t:=by
    intro A B h; have hx:A.up=B.up:=congrArg Prod.fst h; have hv:A.height=B.height:=funext fun i=> Fin.ext_iff.mp (congrFun (congrArg Prod.snd h) i) -- tune newline
    cases A; cases B; congr
  letI: Finite (Forest D):= Finite.of_injective t hp
  exact Fintype.ofFinite _
variable (R':GramM (mid C B))(A':Loom (mid C B))(G:Ratio (mid m B) (mid C B))(T:RG.StepData (More (mid m B)) (More (mid C B)))(q:Chi)(d:ℝ)(Q:Op Slot)
def carrier (F:Forest (ratio G))(V:Orbit (mid m B))(W:Orbit (mid C B)): Phys (mid m B):=
 T.density R'.beta W.1 V.1 • scaleZ Q (fire (Thread j) G R'.J.M (unionP (seine G F q d (A' W) (A V),A V)) (cartsL (switchG G).symm (denZ R' P A' W)))
def integrated(V:Orbit (mid m B))(W:Orbit (mid C B)): Phys (mid m B) := (Fintype.card (Forest (ratio G)):ℝ)⁻¹ • ∑ F:Forest (ratio G),carrier P A R' A' G T q d Q F V W
def stove (V:Orbit (mid m B)): Phys (mid m B):=∫ W:Orbit (mid C B), integrated P A R' A' G T q d Q V W ∂city (mid C B)
structure RelayZ :Prop where
 out(V): denZ R P A V= Scree.stove P A R' A' G T q d Q V
 fed : Integrable (fun z: Orbit (mid m B) × Orbit (mid C B)=> integrated P A R' A' G T q d Q z.1 z.2) ((city _).prod (city _))
 inZ : Integrable (denZ R' P A') (city _)
 wheel(v:Phys (mid m B)): beamZ _ (scaleZ Q v)=beamZ _ v
 shape:G.count=L
 mesh:T.ratio=ratio G
 size:P.roundZ ≤ (mid m B).val
 hot:0<e
 pays:T.IsKernel R'.beta group
 eligible(F:Forest (ratio G))(V:Orbit (mid m B))(W:Orbit (mid C B)): JointB G (seine G F q d (A' W) (A V),A V) e
end YM.CF.Scree
