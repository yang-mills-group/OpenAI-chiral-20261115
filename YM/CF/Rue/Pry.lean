import YM.CF.Eire.Gown
import YM.CF.Rue.Jets
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option quotPrecheck false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Rue
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open RG Pressure
open Jet Forge Eire Pressure.Tube Esti Cloak Rill Hake
attribute [local instance] opCStarAlgebra
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{s t C B u w:ℝ}{k:ℕ}
local notation "G₀"=>SU.group
lemma four_p (q:Chi)(k:ℕ)(hp: SU.group.colorScale≤ C): ∃ D:ℝ, 0≤D∧∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{x:E}{n:Side}(U:E→ Pane n)(T F: Finset (Cell (More n)))(P:ℝ),0<P → F ⊆ T → (∀ i∈F,Tender (fun t=> faceValue (U t) i) x (C*P) k) →
 let G'(z):=∏ i∈F, padK (fun t=>faceValue (U t) i) q P z; Allows k G' x (Cloak.priceK k T.card D) ∧ (x∈tsupport G' → ∀ i∈F, Pressure.toll (U x) i < P) :=by
 obtain ⟨D,h,H⟩:= mantle q k hp; refine ⟨D,h,@fun E _ _ x n U T F t l v p=>?_⟩ -- tune
 intro G; refine ⟨Allows.mono (prince F _ _ h (fun i v=>H l _ (p i v)) (fun i u=> (abs_of_nonneg (q.range _).1).trans_le (q.range _).2)) (by unfold Cloak.priceK; gcongr),fun g j t'=> padHi (fun y=>faceValue (U y) j) q l ?_ (e_cont _ (p j t'))⟩
 exact closure_mono (fun x' (y:x'∈Function.support G)=>show x'∈Function.support (padK (fun y=> faceValue (U y) j) q t) from fun w=> y (show G x'=0 from prod_eq_zero t' w)) g -- tune
variable {n m:Side}(S:StepData n (More m))(x:ℝ)(T:Tube G₀ S)(q:Chi)(d β:ℝ)(l:ℕ)
variable(M: Monk G₀ S) (P: E→ Config G₀ n)
abbrev hallU (P:E→ Config G₀ n)(M:Monk G₀ S)(x:E): Monk G₀ S:= {M with V:= P x}
local notation "M_"=>hallU S P M
local notation "U_"=> (fun y=> (M_ y).sent x T q d l β)
local notation "Y'"=> (mid m m) -- dummy
variable{S} {R:GramM m}
lemma poignant_hold (X:Support (More m))(p:5*R.p.B+4 ≤ 10*radiusB x)(h:X ⊆ brushK M.key (chillB M) R.p.threshold)(i:Bond (More m))(u:i∉ unrest X R.p.B)(t z:E): U_ t i=U_ z i :=by
 obtain ⟨y,lx,b⟩:=Finset.not_disjoint_iff.mp (fun g=>u (mem_filter.mpr ⟨mem_univ _,g⟩)); obtain ⟨s,v,w⟩:=halo_spec.mp b
 obtain ⟨j,g,a⟩:= mem_biUnion.mp (h v); have hv:S.ratio.parent s∈M.key.place:=mem_union_left _ (mem_union_left _ (mem_biUnion.mpr ⟨j,(mem_filter.mp g).1,mem_image_of_mem _ a⟩))
 have hk:separation y i.1≤ 1:=?_; swap; · cases mem_insert.mp lx with| inl h=> rw [h,separation_self]; omega| inr h=> rw [mem_singleton.mp h,separation_comm]; exact Work.E01.sep_step_le ..
 have hk':=separation_triangle s y i.1; have hg:= Work.E04.parent_separation S.ratio s i.1; have hp: S.ratio.parent i.1 ∈ M.key.dome (10*radiusB x):=halo_spec.mpr ⟨_,hv,by omega⟩; have hs(u):= Eire.sketch (M_ u) T x q d l β i hp; exact (hs t).trans (hs z).symm
variable{E' : Type*}[LinearOrder E'][Fintype E']
lemma zero_s {F:E→Dough E'}{v:E}(u:Raid E')(p:0≤u)(q:∀ᶠ y in 𝓝 v,F y=0):Rigid F k v u:=by
 have hp:= Woody.germ (n:=E') (k:=k) (Woody.empty v) (G:=fun z=>(F z).val) (q.mono fun i p=>by dsimp only; rw [p]; rfl); exact ⟨hp.own,fun i=>⟨(hp.haveP i).smooth,(hp.haveP i).earned.trans (p i)⟩⟩
variable {F:E→ℝ}{K:E→Dough E'}{x':E}{U₀:Raid E'}
noncomputable def φC : ℝ→L[ℝ] ℂ:= Complex.ofRealCLM
abbrev ξ (k:ℕ)(C:ℝ):= ‖φC‖* C*(k+1:ℝ)
lemma pace_p (h:Rigid K k x' U₀)(hp:Allows k F x' C):Rigid (fun x=> F x • K x) k x' (ξ k C • U₀):=by
 have hx:Pence k (fun x=>φC (F x)) x' (ξ k C):= by unfold ξ; rw [mul_comm]; exact bare_p _ _ (hp.linear φC le_rfl) -- check lemma
 refine ⟨Eventually.of_forall (fun x=>(fineShape _).allP),fun i=> (hx.twice (h.haveP i)).germ ?_⟩
 filter_upwards with y; change _=crumb (F y • (K y).val) i; rw [Pastry.crumb_scaleR]; exact (Complex.real_smul ..).symm
end YM.CF.Rue
