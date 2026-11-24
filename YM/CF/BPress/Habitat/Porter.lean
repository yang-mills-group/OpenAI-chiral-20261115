import YM.CF.BPress.Habitat.Cabal
/-! Habitat actual pricing domains. This proof does not need to claim any particular measurability class of the domain in its ambient space. It is gauge-invariant &, for ext of kernel, we extend via standard Borel *producer* onto actual accepted versions including gauge reindex, not postulating a general extension of every possible field cost. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Habitat
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Upled Plain Engine
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat.Plain
attribute [local instance] opCStarAlgebra
variable {N s:Side}
structure Driver (N:Side) where
 d:ℝ -- same as Grasp after warmth
 h:ℝ -- speed_bound on paths (ΨTone)
 v:ℝ -- r License. can use all fields satisfying stronger/slack.
 ε:ℝ -- gap
 p:ℝ -- Slow on X, e.g. Grasp's tolerance for hum not necessarily lemma B-bra.
 j:ℕ
 M:Jill.Male
 F:Aim N
namespace Driver
variable (V: Driver N)
abbrev packsA (v:Pec.Post N): Op (Single N):= spar V.j V.M v -- tune Post(Pec)
abbrev packsM(v:Pec.Post N):=Ts V.F (packsA V v) v
def model : Actor N (Plain N):= ⟨key,(fun x=> V.packsA x.G), (fun x=> V.packsM x.G), (fun x=>x.spin false),(fun x=>x.spin true)⟩
local notation "M_"=> V.model
structure Hallowed (x:Plain N):Prop where
 glow: Guard x.G V.d
 tuneK: Slow x.G (hook x.X) V.p
 toll: ∀ t∈Set.Icc (0:ℝ) 2,∀ z:Site (More N),∀ a:Bool, ‖x.spin a t z‖≤ V.h
 state: Pf.Issued ((M_).keys true x) ((M_).keys false x) ((M_).A x) ((M_).M x) ((M_).col x) ((M_).col' x) V.v V.ε
 day : MatPlan ((M_).KG x)
abbrev Pose : Type:= {x:Plain N// Hallowed V x}
scoped instance ΩBC: OpensMeasurableSpace V.Pose:= by letI : OpensMeasurableSpace (Plain N):=@BorelSpace.opensMeasurable _ _ _ (bore_p (N:=N)); exact Subtype.opensMeasurableSpace (p:=Hallowed V) -- tune name
abbrev Beta : Form N V.Pose:=⟨fun s a b=> evalC s a.val b.val,fun i a b=>pos_eval i a.val b.val,fun {x y} h a b=>mono_τ x a.val b.val h ⟩ -- tune order of eval and mono
abbrev decks : Actor N V.Pose:=⟨(M_).seat ∘ Subtype.val,(M_).A ∘ Subtype.val,(M_).M ∘ Subtype.val,(M_).H ∘ Subtype.val,(M_).H' ∘ Subtype.val⟩
local notation "Φ"=> V.Pose
variable (x y:Pose V)
def fundsX (x:Pose V) : Spin.OpenW N V.d:= ⟨x.val.G,x.property.glow⟩
lemma group_cover : GroupFields  (N:=N)  (Beta V) V.fundsX (decks V).seat:=by -- tune `(β:=..`
 let F:=Beta V; constructor; · exact Continuous.subtype_mk (cont_G.comp continuous_subtype_val) _
 · exact fun i a b=>ticketS ..
 · intro i; let u(x:Pose V): Bool:=x.val.stars i; have p: Continuous u:=(continuous_apply i).comp (cont_star.comp continuous_subtype_val); rw [show {x:Pose V|i∈ (decks V).seat x}=u ⁻¹' {true} from ?_]; exact (isClopen_discrete _).preimage p; ext x; simp only [decks,model,Function.comp_apply,key,mem_filter,mem_univ,true_and, Set.mem_setOf]; rfl
 intro s x y i h g; let u:= FateTick (x.val.stars i) (y.val.stars i); have hx:u=1:= by apply if_neg; intro p; rcases g with g|g; exact g.2 (mem_filter.mpr ⟨mem_univ _,p ▸ (mem_filter.mp g.1).2⟩); exact g.2 (mem_filter.mpr ⟨mem_univ _,p.symm ▸ (mem_filter.mp g.1).2⟩)
 rw [←hx]; exact (single_le_sum (s:=nearBits s) (f:=fun i=> FateTick (x.val.stars i) (y.val.stars i)) (fun i _ => tickc ..) (mem_filter.mpr ⟨mem_univ _,h⟩)).trans (ticketT ..)
lemma spines (t:Bool)(r:ℝ)(h:0≤r)(v:r≤1): Sight (Beta V) (fun (x:Pose V)=> x.val.spin t) V.h r:=by
 let G(i: Set.Icc r (r+1)):Set.Icc (0:ℝ) 2:=⟨i.val,h.trans i.property.1, i.property.2.trans ((add_le_add_left v 1).trans_eq (by norm_num))⟩; constructor; · exact fun i j=> i.1.property.toll i.2.val (G i.2).property j t
 · exact fun X i p x y s=> Plain.spins X x.val y.val _ (G s).property (node i) p t -- order arguments
 exact (Plain.cont_spin t).comp (f:=fun x:Pose V × Pf.Currency.PartH r=>(x.1.val,x.2.val)) ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))
structure Wish (A B Q:Pledge):Prop where
 pen : Shelf N V.d V.j A
 pay : V.F.toll B.rate Q.rate B.price Q.price
open Pf Pf.RealBook
abbrev payA (A B Q:Pledge) := priceS A B Q
theorem wish {A B Q:Pledge} (g:Wish V A B Q): price_spin (Beta V) V.decks A (payA A B Q) (stream 1) (Sight.price V.h) V.ε V.v:= ⟨Spin.gen V.group_cover g.pen _ _ g.pay _ _ ⟨V.spines false 0 le_rfl zero_le_one, V.spines false 1 zero_le_one le_rfl⟩ ⟨V.spines true 0 le_rfl zero_le_one,V.spines true 1 zero_le_one le_rfl⟩ (fun x=>x.property.state), fun x=>x.property.day⟩ -- tune Pledge
end Driver
end YM.CF.BPress.Habitat
