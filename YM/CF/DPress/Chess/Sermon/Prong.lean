import YM.CF.DPress.Chess.Sermon.Pocket
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Chess.Sermon
open Function Filter Lattice RG Wilson MeasureTheory ProbabilityTheory Push.GridApprox FD Skye Tree Precision Rush Spire Scree Lift Transit Bough Turn Push.SectorMeasure Tulip
open Fock Finset Girt
open Cube (More assembly node)
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal Bough Matrix.Norms.L2Operator YM.CF.BPress
attribute [local instance] opCStarAlgebra
variable (W:Wall) {n m:Side}{K:Ratio n m}{S:StepData (More n) (More m)}{r ℓ d:ℕ}{β u k:ℝ}{P:Loom n}
abbrev root_M(K:Ratio n m)(D:Support (More n)):Setoid (Ticket K):= joins (Bough.Counts (ratio K) D) (Ties SU.group D)
abbrev page_M(K:Ratio n m)(X Y:Support (More n)): Setoid (Pane n × Ticket K):= joins (Ties SU.group X) (root_M K Y)
section
variable {U:Type*}
abbrev Lit (W:Wall)(ℓ:ℕ)(A:Stage n→ U):Prop:= Uses A (focus (W.crop n Wall.rail) (W.crop n (2*ℓ)))
abbrev Hi(W:Wall)(ℓ:ℕ)(A:Fold K U):Prop:= Uses A (joins (focus ((W.boost K.count).crop _ Wall.rail) ((W.boost K.count).crop _ (2*ℓ))) (page_M K (W.crop n Wall.rail) (W.crop n ℓ)))
abbrev wake (W:Wall){n: Side}:Stage n → Stage n:= fun x=>(W.shine _ x.1,W.shine _ x.2)
abbrev peer_T{S:StepData (More n) (More m)}(p:S.ratio=ratio K) : Ticket K → Ticket K:=Prod.map (ζF W p) (W.shine _)
def retire {S:StepData (More n) (More m)}(t:S.ratio=ratio K) (A:Fold K (ReOp m)) : Fold K (ReOp m):=fun i=> (W.boost K.count).θ _ (A (wake (W.boost K.count) i.1,(W.shine _ i.2.1, peer_T W t i.2.2))) -- use syntax
lemma negCap(n:Side){U V: Support (More n)}:Respects (focus (W.negZ U) (W.negZ V)) (focus U V) (wake W):= fun _ _ p=>⟨W.read p.1,W.read p.2⟩
@[fun_prop] lemma cap_C(n: Side):Continuous (wake W (n:=n)):= ( (W.iceM n).comp continuous_fst).prodMk ((W.iceM n).comp continuous_snd)
lemma negTicket(t:S.ratio=ratio K)(X:Support (More n)): Respects (root_M K (W.negZ X)) (root_M K X) (peer_T W t):=fun _ _ p=>⟨Turn.worth W t X _ _ p.1, W.read p.2⟩
@[fun_prop] lemma peer_M(t:S.ratio=ratio K): Measurable (peer_T W t):=(measurable_of_countable (ζF W t)).prodMap (W.trail _).measurable
local notation "Nt"=> W.boost K.count
lemma pension{A:Fold K (ReOp m)}(t:S.ratio=ratio K)(v: Envelope A) : Envelope (retire W t A):=by
 let G:Tour K → Tour K:=Prod.map (wake (Nt)) (Prod.map (W.shine _) (peer_T W t)); refine Env.along (pole_w A ((Nt).θ m) ((Nt).θ_c _) v) (g:=G) ((cap_C (Nt) _).measurable.prodMap ((W.trail _).measurable.prodMap (peer_M W t))) -- tune `Proper SpaceOp`
lemma KnowH {A:Fold K (ReOp m)}(h:Hi W ℓ A)(t:S.ratio=ratio K): ∀ x:Stage m, Uses (fun z:Pane n× Ticket K=> retire W t A (x,z)) (page_M K (W.negZ (W.crop n Wall.rail)) (W.negZ (W.crop n ℓ))) :=fun x y z p=> congrArg ((Nt).θ m) (h (wake (Nt) x, (W.shine n y.1, peer_T W t y.2)) (wake (Nt) x, (W.shine n z.1, peer_T W t z.2)) ⟨(focus _ _).iseqv.refl (wake (Nt) x),W.read p.1, negTicket W t _ _ _ p.2⟩) -- ζW tune
end
lemma knowingX {X:Type*}{A:Fold K X} (h:Hi W ℓ A):∀ x:Stage m, Uses (fun z: Pane n × Ticket K=> A (x,z)) (page_M K (W.crop n Wall.rail) (W.crop n ℓ)):=fun i x y p=> h _ _ ⟨(focus _ _).iseqv.refl i,p⟩
section
variable [Nonempty (Forest (ratio K))] {V: Type*}[NormedAddCommGroup V][NormedSpace ℝ V][SecondCountableTopology V][MeasurableSpace V][BorelSpace V]
lemma ears {X T:Support (More n)} {A: Fold K V}(x:Stage m)(i j:Pane n)(p:Uses (fun z=>A (x,z)) (page_M K X T))(v:Firm P u r)(t:Measurable P)(g:Envelope A)(l: Agrees X i j)(hq:Agrees (halo r T) i j): sum_T P A x i=sum_T P A x j:=by
 let F:=unc_N A x i; have he(h:Pane n): (∫ z:Ticket K,F z ∂νticket P h)= ∫ y,(∫ z:Pane n,F (y,z)∂ Robe.τ P h)∂ Bough.St (ratio K):=by letI:=tight (K:=K) t h; letI:= Robe.prob t h; exact integral_prod _ (Env.integrableX (shelfK g ..) _)
 rw [sum_T,sum_T,show unc_N A x j= F from (funext fun (z:Ticket K)=>(p (i,z) (j,z) ⟨l,(root_M _ _).iseqv.refl z⟩).symm)]; change (∫ z:Ticket K,F z ∂νticket P i)=_; rw [he i,he j]; exact integral_congr_ae (Eventually.of_forall fun y=>Robe.samePrice v (fun z=> F (y,z)) ((shelfK g x i).meas.comp measurable_prodMk_left) (fun a b t=>p (i,(y,a)) (i,(y,b)) ⟨(Ties SU.group X).iseqv.refl _, ⟨(Counts _ _).iseqv.refl _,t⟩⟩) hq)
end
end YM.CF.DPress.Chess.Sermon
