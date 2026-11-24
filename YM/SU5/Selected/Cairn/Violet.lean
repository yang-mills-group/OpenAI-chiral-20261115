import YM.SU5.Selected.Cairn.Sedge
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Pannier.Chancel.Attic.Cairn
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest Airy Rail Lantern Lantern.Bulb Attic Cuve
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 20000
local notation "I"=>Complex.I
open Mint Mezz
open Stencil (pace heatize heats pval pulseNode) -- Mezz options later
namespace Giant
variable (A:Giant) {N:Side} (Z:A.Notes→basisRule) {T:Type}[Fintype T][DecidableEq T](P:Society T)(b:Bool)
local notation "Q" b:max => park N (A.patio b)
structure Viole (F:Pane N→ WRect (Single N) P.Club): Prop where
 cont : Continuous F
 support (V:Pane N): Contained (modesIn N (Q b)) (F V)
 fixes (V:Pane N): hand b (cutM (Tset N))* F V= F V
 respect : Lattice.LocalOn (Q b) F -- signature orientation measure
namespace Viole
variable {A P b} {F G:Pane N→ WRect (Single N) P.Club} (h:Viole A P b F) (u:Viole A P b G)
#print Viole.mk
include h u
lemma adds: Viole A P b (F+G):= ⟨h.cont.add u.cont, fun x=> Contained.add (h.support _) (u.support _),fun x=> by rw [Pi.add_apply,Matrix.mul_add,h.fixes,u.fixes],fun x y p=> congrArg₂ (fun a b: Matrix _ _ ℂ => a+b) (h.respect x y p) (u.respect x y p)⟩
omit u
lemma scale (c:ℂ): Viole A P b (c • F):= ⟨continuous_const.smul h.cont,fun x=> (h.support _).smul _,fun x=> by rw [Pi.smul_apply,Matrix.mul_smul,h.fixes],fun x y p=>congrArg (fun i:WRect _ _=>c • i) (h.respect x y p)⟩
lemma serves : AtSupport false (Q b) (fun x:Fields N=> tape b (F x.1)):= by
 apply AtSupport.fromEval (F:= fun x=> tape b (F x));
 · exact Push.SectorMeasure.Env.compact ((tape_c b).comp h.cont)
 · exact fun x y p=> congrArg _ (h.respect x y p)
 intro x; refine (show decide (Odd (Finset.univ:Finset P.Club).toList.length) = false from ?_) ▸ seed_party b (h.support x) (h.fixes x) univ.toList -- tune syntax
 rw [rung_len P.club_card]; decide
end Viole
abbrev garden (b:Bool) :Finset Cover:= A.Broad -- maybe unneeded
variable (y:Bool)(C:ℝ)(i:A.Block)(c:Bool)
noncomputable def HourX (U:Pane N):= Mint.yoke (filmL A P y C U) i c
noncomputable def HourY (U:Pane N):= Mint.yoke (filmR A Z P C U) i c
noncomputable def Hours (U:Pane N):= if b then HourX A P y C i c U else HourY A Z P C i c U
local notation "K"=> cutM (Tset N)
local notation "L"=> filmL A P y C
local notation "R"=> filmR A Z P C
variable {M:Tulip.Male}{δ γ:ℝ}(e:Pride A Z C δ γ M N) (h:A.tokenS<N.val)
include e h
lemma time_X : Viole A P true (HourX (N:=N) A P y C i c):=by
 refine ⟨(Silks.dressed_c ..).matrix_mul continuous_const,fun V:Pane N=>(floraN A P y C V).times _,fun x=> desc_s A P i c (flora_pitch A P y C x),fun x t g=>?_⟩ -- desc_s args order
 exact congrArg (fun X:WRect (Single N) _=> Mint.yoke X i c) (evenL A P y h C x t g)
lemma time_Y : Viole A P false (HourY (N:=N) A Z P C i c):=by
 refine ⟨(Silks.dressed_c ..).matrix_mul continuous_const,fun V:Pane N=>(floraY A Z P C V e.crop).times _,fun x=> desc_s A P i c (fluf A Z P x e),fun x t g=>?_⟩ -- desc_s
 exact congrArg (fun X:WRect (Single N) _=> Mint.yoke X i c) (evenR A Z P e.crop h C x t g)
lemma chronos: Viole A P b (Hours (N:=N) A Z P b y C i c):=by cases b; exact time_Y A Z P C i c e h; exact time_X A Z P y C i c e h -- Z may explicit by include e
omit e h in
lemma patio_2 : A.patio b ⊆ A.Core:=by cases b; exact A.nut.trans A.portS; exact A.nudge.trans A.portS
-- remove include for patio lemma
local notation "S₀" => park N A.Broad
noncomputable def stable : Station (park N A.Broad) A.Block P.Club:= by
 refine ⟨fun i c x=> A.Hours Z P true y C i c x.1,fun i c x=>A.Hours Z P false y C i c x.1,fun i t=> ?_⟩
 let F(b c): Pane N → WRect (Single N) P.Club:= A.Hours Z P b y C i c; let a:ℂ:= pval t; let w':=(heatize (pval t):ℂ); let Y':= a^(11:ℕ) • F true true + F true false; let Q':= w' • (a • F false true + F false false);
 let η : Buffered.Mark N := fun x => tape true (Y' x.1); let ξ : Buffered.Mark N := fun x=> tape false (Q' x.1); -- η small or big notation.
 have ht(b c): Viole A P b (F b c) := chronos A Z P b y C i c e h; have he(b): (park N (A.patio b))⊆ S₀:= image_subset_image ((patio_2 A b).trans A.portT)
 have hY: Viole A P true Y':= Viole.adds ((ht true true).scale _) (ht true false)
 have hQ: Viole A P false Q':= ((ht false true).scale _ |>.adds (ht false false)).scale _
 have hs: AtSupport false S₀ (η*ξ):= (hY.serves.mono (he true)).mulM (hQ.serves.mono (he false));
 change AtSupport false S₀ (-(η*ξ)); rw [←neg_one_smul ℂ]; exact hs.smulM _
#check @stable
lemma uptime (x:Fields N): (stable A Z P y C e h).low i c x= yoke (L x.1) i c :=rfl
lemma downtime (x:Fields N): (stable A Z P y C e h).high i c x=yoke (R x.1) i c:=rfl
-- covariance operands. primeU
omit e h
lemma merit (g:Seat N→SU.E)(x:Pane N): let p:= if b then A.anchorX y else A.anchorY; A.Hours Z P b y C i c (gauge g x)*(P.arm (g (wrap (More N) p))).val= (tradew N g).val*A.Hours Z P b y C i c x:=by cases b; exact aweR A Z P x i C c g; exact aweL ..
end Giant
end YM.CF.Pannier.Chancel.Attic.Cairn
open YM.CF.Pannier.Chancel.Attic.Cairn.Giant
#print axioms stable
#print axioms downtime
#print axioms chronos
#print axioms merit
